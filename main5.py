#!/usr/bin/env python3
import os
import re
import aiohttp
import asyncio
import threading
from pathlib import Path
from datetime import datetime, timedelta
from pyrogram import Client, filters
from pyrogram.types import Message, BotCommand, InlineKeyboardMarkup, InlineKeyboardButton, CallbackQuery
from pyrogram.enums import ParseMode
from pyrogram.errors import FloodWait
from PIL import Image
from hachoir.parser import createParser
from hachoir.metadata import extractMetadata
import subprocess
import traceback
import json 
from flask import Flask, render_template_string
import requests
import time
import math
import logging
import yt_dlp

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# env variables
API_ID = int(os.getenv("API_ID", "1234567")) # Please use your real API ID
API_HASH = os.getenv("API_HASH", "your_api_hash")
BOT_TOKEN = os.getenv("BOT_TOKEN", "your_bot_token")
PORT = int(os.getenv("PORT", "10000")) 
RENDER_EXTERNAL_HOSTNAME = os.getenv("RENDER_EXTERNAL_HOSTNAME", "")
COOKIES_TXT = os.getenv("COOKIES_TXT") # Added for yt-dlp cookies

TMP = Path("tmp")
TMP.mkdir(parents=True, exist_ok=True)

# --- STATE VARIABLES ---
USER_THUMBS = {}
TASKS = {}
SET_THUMB_REQUEST = set()
SUBSCRIBERS = set()
SET_CAPTION_REQUEST = set()
USER_CAPTIONS = {}
USER_COUNTERS = {}
EDIT_CAPTION_MODE = set()
USER_THUMB_TIME = {}
HIDE_PROGRESS_BAR = set()

# --- NEW STATE VARIABLES FOR YT-DLP FEATURES ---
USER_MODES = {}               # Tracks if user is in 'direct' or 'yt_dlp' mode
USER_PRESETS = {}             # Saves the selected qualities for 'Load Same Quality'
URL_INFO_CACHE = {}           # Temporarily stores extracted yt-dlp info for messages
USER_QUALITY_SELECTIONS = {}  # Tracks the ✅/❌ selections in the inline keyboard


# Flask Initialization
flask_app = Flask(__name__)

@flask_app.route("/")
def index():
    return "Bot is running perfectly with yt-dlp and direct mode!"

def ping_service():
    if not RENDER_EXTERNAL_HOSTNAME:
        print("Render URL is not set. Ping service is disabled.")
        return

    url = f"http://{RENDER_EXTERNAL_HOSTNAME}"
    while True:
        try:
            response = requests.get(url, timeout=10)
            print(f"Pinged {url} | Status Code: {response.status_code}")
        except requests.exceptions.RequestException as e:
            print(f"Error pinging {url}: {e}")
        time.sleep(600)

def run_flask_and_ping():
    flask_thread = threading.Thread(target=lambda: flask_app.run(host="0.0.0.0", port=PORT, use_reloader=False))
    flask_thread.start()
    ping_thread = threading.Thread(target=ping_service)
    ping_thread.start()
    print("Flask and Ping services started.")

async def periodic_cleanup():
    while True:
        try:
            now = datetime.now()
            for p in TMP.iterdir():
                try:
                    if p.is_file():
                        if now - datetime.fromtimestamp(p.stat().st_mtime) > timedelta(days=3):
                            p.unlink()
                except Exception:
                    pass
        except Exception:
            pass
        await asyncio.sleep(3600)


# Bot Initialization
app = Client(
    "my_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN
)

# -------------------------------------------------------------------------
# HELPER FUNCTIONS
# -------------------------------------------------------------------------

def split_file_ffmpeg(input_file, max_size=1932735283): 
    # 1.8 GB hard limit (1.8 * 1024 * 1024 * 1024 = 1932735283 bytes)
    file_size = os.path.getsize(input_file)
    if file_size <= max_size:
        return [input_file]
    
    print(f"File {input_file} is larger than 1.8GB. Splitting...")
    try:
        # Get video duration safely
        cmd = ["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "default=noprint_wrappers=1:nokey=1", input_file]
        duration = float(subprocess.check_output(cmd).decode('utf-8').strip())
        
        # Calculate parts needed based on size limit
        parts = math.ceil(file_size / max_size)
        part_duration = duration / parts
        
        output_files = []
        base_name = os.path.splitext(input_file)[0]
        ext = os.path.splitext(input_file)[1]
        
        for i in range(parts):
            out_name = f"{base_name}_part{i+1}{ext}"
            start_time = i * part_duration
            
            split_cmd = [
                "ffmpeg", "-i", input_file, "-ss", str(start_time), "-t", str(part_duration),
                "-c", "copy", out_name, "-y"
            ]
            subprocess.run(split_cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            output_files.append(out_name)
            
        return output_files
    except Exception as e:
        print(f"Error during splitting: {e}")
        return [input_file] # Fallback to original file if splitting fails

def generate_yt_keyboard(msg_id, info, selected_formats):
    formats = info.get('formats', [])
    filtered_formats = []
    seen_heights = set()
    
    # Filtering available qualities
    for f in formats:
        if f.get('vcodec') != 'none' and f.get('acodec') != 'none':
            h = f.get('height')
            if h and h not in seen_heights:
                filtered_formats.append(f)
                seen_heights.add(h)
                
    # Sort formats by height (e.g., 360p, 480p, 720p)
    filtered_formats = sorted(filtered_formats, key=lambda x: x.get('height', 0))
    
    buttons = []
    for f in filtered_formats:
        fid = f['format_id']
        height = f.get('height', 'Unknown')
        ext = f.get('ext', 'mp4')
        size = f.get('filesize') or f.get('filesize_approx') or 0
        size_mb = size / (1024 * 1024)
        
        btn_text = f"{height}p ({ext}) - {size_mb:.1f}MB"
        
        # Direct Download Button
        q_btn = InlineKeyboardButton(btn_text, callback_data=f"ytdl|{msg_id}|{fid}")
        
        # Checkbox Toggle Button
        check_text = "✅" if fid in selected_formats else "❌"
        c_btn = InlineKeyboardButton(check_text, callback_data=f"yttgl|{msg_id}|{fid}")
        
        buttons.append([q_btn, c_btn])
        
    buttons.append([InlineKeyboardButton("OK ✅", callback_data=f"ytok|{msg_id}")])
    buttons.append([
        InlineKeyboardButton("Add Save Quality 💾", callback_data=f"ytsave|{msg_id}"),
        InlineKeyboardButton("Load Same Quality 🔄", callback_data=f"ytload|{msg_id}")
    ])
    
    return InlineKeyboardMarkup(buttons)

async def process_yt_download_and_upload(client, message, info, formats, user_id):
    title = info.get('title', 'Unknown_Video')
    clean_title = re.sub(r'[\\/*?:"<>|]', "", title)
    
    for fid in formats:
        try:
            quality_str = "Unknown Quality"
            for f in info.get('formats', []):
                if f['format_id'] == fid:
                    quality_str = f"{f.get('height', 'Unknown')}p"
                    break
                    
            dl_msg = await message.reply_text(f"⬇️ Downloading Quality: {quality_str} ...")
            
            out_tmpl = str(TMP / f"{clean_title}_{fid}.%(ext)s")
            ydl_opts = {
                'format': fid,
                'outtmpl': out_tmpl,
                'quiet': True,
                'cookiefile': COOKIES_TXT if COOKIES_TXT and os.path.exists(COOKIES_TXT) else None,
            }
            
            def run_yt_dlp():
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    ydl.download([info['webpage_url']])
                    
            await asyncio.to_thread(run_yt_dlp)
            
            dl_files = list(TMP.glob(f"{clean_title}_{fid}.*"))
            if not dl_files:
                await dl_msg.edit_text(f"❌ Failed to download {quality_str}")
                continue
                
            dl_file = dl_files[0]
            
            # File Splitting Check (1.8 GB)
            await dl_msg.edit_text(f"✂️ Checking file size for 1.8GB limit...")
            parts = split_file_ffmpeg(str(dl_file))
            total_parts = len(parts)
            
            for idx, part in enumerate(parts):
                part_info = f"\n**Part:** {idx+1}/{total_parts}" if total_parts > 1 else ""
                
                await dl_msg.edit_text(f"⬆️ Uploading {quality_str} (Part {idx+1}/{total_parts})...")
                
                # Setup Metadata, Caption & Thumbnail
                user_caption = USER_CAPTIONS.get(user_id)
                if user_caption:
                    caption = user_caption + part_info
                else:
                    caption = f"**{title}**\n**Quality:** {quality_str}{part_info}"
                    
                thumb_path = USER_THUMBS.get(user_id)
                
                # Get exact duration for Telegram metadata
                duration = 0
                try:
                    metadata = extractMetadata(createParser(part))
                    if metadata and metadata.has("duration"):
                        duration = metadata.get('duration').seconds
                except Exception:
                    pass
                
                # Upload logic
                await client.send_video(
                    chat_id=user_id,
                    video=part,
                    caption=caption,
                    thumb=thumb_path,
                    duration=duration,
                    supports_streaming=True
                )
                
            await dl_msg.delete()
            
            # Cleanup processed files
            for p in parts:
                try:
                    os.remove(p)
                except: pass
            if str(dl_file) not in parts:
                try:
                    os.remove(dl_file)
                except: pass
                
        except Exception as e:
            await message.reply_text(f"❌ Error with {quality_str}: {str(e)}")

# -------------------------------------------------------------------------
# BOT COMMANDS & HANDLERS
# -------------------------------------------------------------------------

@app.on_message(filters.command("start"))
async def start_cmd(client, message):
    await message.reply_text("Hello! I am ready. Send /yt_dlp to switch modes or use /setthumb & /set_caption.")

@app.on_message(filters.command("setthumb") & filters.private)
async def setthumb_cmd(client, message):
    SET_THUMB_REQUEST.add(message.from_user.id)
    await message.reply_text("Please send the photo you want to use as a custom thumbnail.")

@app.on_message(filters.photo & filters.private)
async def save_thumb(client, message):
    user_id = message.from_user.id
    if user_id in SET_THUMB_REQUEST:
        file_path = await message.download(file_name=f"tmp/{user_id}_thumb.jpg")
        USER_THUMBS[user_id] = file_path
        SET_THUMB_REQUEST.remove(user_id)
        await message.reply_text("✅ Thumbnail saved successfully!")

@app.on_message(filters.command("delthumb") & filters.private)
async def delthumb_cmd(client, message):
    user_id = message.from_user.id
    if user_id in USER_THUMBS:
        try:
            os.remove(USER_THUMBS[user_id])
        except:
            pass
        del USER_THUMBS[user_id]
        await message.reply_text("✅ Custom thumbnail deleted.")
    else:
        await message.reply_text("❌ No custom thumbnail found.")

@app.on_message(filters.command("set_caption") & filters.private)
async def setcaption_cmd(client, message):
    if len(message.command) > 1:
        caption = message.text.split(" ", 1)[1]
        USER_CAPTIONS[message.from_user.id] = caption
        await message.reply_text("✅ Custom caption saved successfully!")
    else:
        await message.reply_text("Please provide the caption after the command. Example:\n`/set_caption My Custom Caption`")

@app.on_message(filters.command("delcaption") & filters.private)
async def delcaption_cmd(client, message):
    user_id = message.from_user.id
    if user_id in USER_CAPTIONS:
        del USER_CAPTIONS[user_id]
        await message.reply_text("✅ Custom caption deleted.")
    else:
        await message.reply_text("❌ No custom caption found.")

# Toggle Command for yt-dlp
@app.on_message(filters.command("yt_dlp") & filters.private)
async def toggle_yt_dlp(client, message):
    user_id = message.from_user.id
    current_mode = USER_MODES.get(user_id, "direct")
    
    if current_mode == "direct":
        USER_MODES[user_id] = "yt_dlp"
        await message.reply_text("✅ **yt-dlp mode is now ENABLED.**\nAny links you send will be processed via yt-dlp with multi-quality selection.")
    else:
        USER_MODES[user_id] = "direct"
        await message.reply_text("❌ **yt-dlp mode is now DISABLED.**\nBot will use the default direct download link mode.")

# General Link Handler
@app.on_message(filters.text & filters.private)
async def handle_text_links(client, message):
    text = message.text
    if text.startswith("/"): 
        return
        
    user_id = message.from_user.id
    mode = USER_MODES.get(user_id, "direct")
    
    is_link = re.match(r'https?://[^\s]+', text)
    
    if is_link:
        if mode == "yt_dlp":
            await handle_yt_dlp_link(client, message, text)
        else:
            await handle_direct_link(client, message, text)

# yt-dlp Link Process
async def handle_yt_dlp_link(client, message, url):
    msg = await message.reply_text("⏳ Extracting video information...")
    try:
        ydl_opts = {'quiet': True, 'no_warnings': True}
        if COOKIES_TXT and os.path.exists(COOKIES_TXT):
            ydl_opts['cookiefile'] = COOKIES_TXT
            
        def extract_info():
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                return ydl.extract_info(url, download=False)
                
        info = await asyncio.to_thread(extract_info)
        
        URL_INFO_CACHE[message.id] = info
        USER_QUALITY_SELECTIONS[message.id] = []
        
        keyboard = generate_yt_keyboard(message.id, info, [])
        await msg.edit_text(f"🎬 **{info.get('title', 'Video')}**\n\nSelect qualities and press OK:", reply_markup=keyboard)
        
    except Exception as e:
        await msg.edit_text(f"❌ Extraction Error: {e}")

# Direct Download Logic (Fallback)
async def handle_direct_link(client, message, url):
    msg = await message.reply_text("⬇️ Downloading direct link (Normal Mode)...")
    try:
        user_id = message.from_user.id
        file_name = url.split("/")[-1]
        if not file_name or "?" in file_name:
            file_name = "direct_download.mp4"
            
        file_path = TMP / file_name
        
        async with aiohttp.ClientSession() as session:
            async with session.get(url) as resp:
                if resp.status == 200:
                    with open(file_path, "wb") as f:
                        while True:
                            chunk = await resp.content.read(1024 * 1024)
                            if not chunk:
                                break
                            f.write(chunk)
                            
        # Splitting logic integrated for direct mode as well
        await msg.edit_text("✂️ Checking file size...")
        parts = split_file_ffmpeg(str(file_path))
        
        for idx, part in enumerate(parts):
            part_str = f"\n**Part:** {idx+1}/{len(parts)}" if len(parts) > 1 else ""
            await msg.edit_text(f"⬆️ Uploading file (Part {idx+1}/{len(parts)})...")
            
            caption = USER_CAPTIONS.get(user_id, f"**Direct Download**{part_str}")
            thumb = USER_THUMBS.get(user_id)
            
            await client.send_document(
                chat_id=user_id,
                document=part,
                caption=caption,
                thumb=thumb
            )
            
        await msg.delete()
        for p in parts:
            try:
                os.remove(p)
            except: pass
    except Exception as e:
        await msg.edit_text(f"❌ Error in direct download: {str(e)}")

# -------------------------------------------------------------------------
# CALLBACK HANDLERS FOR YT-DLP KEYBOARDS
# -------------------------------------------------------------------------

@app.on_callback_query(filters.regex(r"^yttgl\|"))
async def cb_toggle_checkbox(client, query):
    _, msg_id, fid = query.data.split("|")
    msg_id = int(msg_id)
    
    selected = USER_QUALITY_SELECTIONS.get(msg_id, [])
    if fid in selected:
        selected.remove(fid)
    else:
        selected.append(fid)
    USER_QUALITY_SELECTIONS[msg_id] = selected
    
    info = URL_INFO_CACHE.get(msg_id)
    if info:
        keyboard = generate_yt_keyboard(msg_id, info, selected)
        await query.message.edit_reply_markup(reply_markup=keyboard)
    await query.answer()

@app.on_callback_query(filters.regex(r"^ytdl\|"))
async def cb_direct_download(client, query):
    # Single quality direct click logic
    _, msg_id, fid = query.data.split("|")
    msg_id = int(msg_id)
    info = URL_INFO_CACHE.get(msg_id)
    
    if info:
        await query.message.edit_text("⏳ Processing selected direct quality...")
        asyncio.create_task(process_yt_download_and_upload(client, query.message, info, [fid], query.from_user.id))
    await query.answer()

@app.on_callback_query(filters.regex(r"^ytok\|"))
async def cb_ok_button(client, query):
    _, msg_id = query.data.split("|")
    msg_id = int(msg_id)
    selected = USER_QUALITY_SELECTIONS.get(msg_id, [])
    info = URL_INFO_CACHE.get(msg_id)
    
    if not selected:
        await query.answer("⚠️ Please check/select at least one quality, or click a quality name directly.", show_alert=True)
        return
        
    if info:
        await query.message.edit_text("⏳ Starting downloads for your selected queue...")
        asyncio.create_task(process_yt_download_and_upload(client, query.message, info, selected, query.from_user.id))
    await query.answer()

@app.on_callback_query(filters.regex(r"^ytsave\|"))
async def cb_save_presets(client, query):
    _, msg_id = query.data.split("|")
    msg_id = int(msg_id)
    user_id = query.from_user.id
    selected = USER_QUALITY_SELECTIONS.get(msg_id, [])
    
    if not selected:
        await query.answer("⚠️ Select at least one quality checkbox to save!", show_alert=True)
        return
        
    USER_PRESETS[user_id] = selected
    await query.answer("✅ Quality choices saved successfully! You can use 'Load Same Quality' for next links.", show_alert=True)

@app.on_callback_query(filters.regex(r"^ytload\|"))
async def cb_load_presets(client, query):
    _, msg_id = query.data.split("|")
    msg_id = int(msg_id)
    user_id = query.from_user.id
    preset = USER_PRESETS.get(user_id)
    info = URL_INFO_CACHE.get(msg_id)
    
    if not preset:
        await query.answer("⚠️ No saved qualities found. Please select qualities and click 'Add Save Quality' first.", show_alert=True)
        return
        
    if info:
        await query.message.edit_text("⏳ Loading saved qualities and starting download...")
        asyncio.create_task(process_yt_download_and_upload(client, query.message, info, preset, user_id))
    await query.answer()

# -------------------------------------------------------------------------
# MAIN EXECUTION
# -------------------------------------------------------------------------

if __name__ == "__main__":
    print("Bot is starting... Starting Flask and Ping threads, then Pyrogram will start.")
    t = threading.Thread(target=run_flask_and_ping, daemon=True)
    t.start()
    
    try:
        loop = asyncio.get_event_loop()
        loop.create_task(periodic_cleanup())
        app.run()
    except Exception as e:
        print(f"Error occurred: {e}")
