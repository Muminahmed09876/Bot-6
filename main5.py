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

# env
API_ID = int(os.getenv("API_ID"))
API_HASH = os.getenv("API_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
PORT = int(os.getenv("PORT", "10000")) 
RENDER_EXTERNAL_HOSTNAME = os.getenv("RENDER_EXTERNAL_HOSTNAME")
COOKIES_TXT = os.getenv("COOKIES_TXT") # Added for yt-dlp cookies

TMP = Path("tmp")
TMP.mkdir(parents=True, exist_ok=True)

# --- COOKIE FIX FOR RENDER ---
COOKIE_FILE_PATH = "cookies.txt"
if COOKIES_TXT:
    # If the ENV variable is a path and exists
    if os.path.exists(COOKIES_TXT):
        COOKIE_FILE_PATH = COOKIES_TXT
    # If the ENV variable contains the actual text content of the cookie
    elif len(COOKIES_TXT) > 50: 
        try:
            with open(COOKIE_FILE_PATH, "w", encoding="utf-8") as f:
                f.write(COOKIES_TXT)
        except Exception as e:
            logger.error(f"Failed to write cookie env to file: {e}")
# -----------------------------

# state
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

# --- STATE FOR AUDIO CHANGE ---
MKV_AUDIO_CHANGE_MODE = set()
PENDING_AUDIO_ORDERS = {} 
# ------------------------------

# --- NEW STATE FOR POST CREATION ---
CREATE_POST_MODE = set()
POST_CREATION_STATE = {} 

DEFAULT_POST_DATA = {
    'image_name': "Image Name",
    'genres': "",
    'season_list_raw': "1, 2" 
}
# ------------------------------------------------

# --- NEW STATE FOR BATCH CAPTION & QUEUE ---
BATCH_CAPTION_MODE = set()  
BATCH_UPLOAD_MODE = set()
BATCH_DATA = {}            
BATCH_STATUS_MSG = {}      

USER_QUEUES = {}           
USER_WORKERS = {}          
USER_UPLOAD_LOCKS = {}     
# ------------------------------------------------

# --- YT-DLP STATE ---
YT_SESSIONS = {}
# --------------------

# --- NEW FEATURES STATE ---
AWAITING_COOKIE_FILE = set()
YOUTUBE_MODE = set()
YT_LAST_SELECTION = {} # Stores last selected resolutions
USER_PROXY = {}

# Dummy proxies (Replace with real ones if needed)
PROXY_LIST = {
    "Bangladesh": "http://113.11.76.233:30226", 
    "India": "http://103.26.109.62:9256",
    "USA": "socks5://165.225.122.16:11368"
}
# --------------------------

ADMIN_ID = int(os.getenv("ADMIN_ID", ""))
MAX_SIZE = 4 * 1024 * 1024 * 1024

# Updated workers to 1000 as requested, added sleep_threshold to prevent FloodWait crashes
app = Client("mybot", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN, workers=1000, sleep_threshold=86400)
flask_app = Flask(__name__)

# ---- utilities ----
def is_admin(uid: int) -> bool:
    return uid == ADMIN_ID

def is_youtube_url(url: str) -> bool:
    parsed = url.lower()
    return "youtube.com" in parsed or "youtu.be" in parsed

def is_drive_url(url: str) -> bool:
    return "drive.google.com" in url or "docs.google.com" in url

def extract_drive_id(url: str) -> str:
    patterns = [
        r"/d/([a-zA-Z0-9_-]+)",
        r"id=([a-zA-Z0-9_-]+)",
        r"open\?id=([a-zA-Z0-9_-]+)",
        r"https://drive.google.com/file/d/([a-zA-Z0-9_-]+)/"
    ]
    for p in patterns:
        m = re.search(p, url)
        if m:
            return m.group(1)
    return None

def generate_new_filename(original_name: str) -> str:
    """Generates the new standardized filename while preserving the original extension."""
    BASE_NEW_NAME = "[@TA_HD_Anime] Telegram Channel"
    file_path = Path(original_name)
    file_ext = file_path.suffix.lower()
    
    file_ext = "." + file_ext.lstrip('.')
    
    if not file_ext or file_ext == '.':
        return BASE_NEW_NAME + ".mp4"
        
    return BASE_NEW_NAME + file_ext

def get_video_metadata(file_path: Path) -> dict:
    """Extracts duration, width, and height using FFprobe (with Hachoir fallback)."""
    data = {'duration': 0, 'width': 0, 'height': 0}
    try:
        cmd = [
            "ffprobe",
            "-v", "quiet",
            "-print_format", "json",
            "-show_streams",
            "-show_format", 
            str(file_path)
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, check=True, timeout=60)
        metadata = json.loads(result.stdout)
        
        video_stream = None
        for stream in metadata.get('streams', []):
            if stream.get('codec_type') == 'video':
                video_stream = stream
                break
        
        if video_stream:
            data['width'] = int(video_stream.get('width', 0))
            data['height'] = int(video_stream.get('height', 0))
        
        duration_str = metadata.get('format', {}).get('duration')
        
        if not duration_str and video_stream:
            duration_str = video_stream.get('duration')
            
        if duration_str:
            try:
                data['duration'] = int(float(duration_str))
            except (ValueError, TypeError):
                logger.warning(f"Could not parse duration string: {duration_str}")
                data['duration'] = 0 
        
        if data['width'] == 0 or data['height'] == 0:
            raise Exception("FFprobe returned 0 dimensions, trying Hachoir")

    except Exception as e:
        logger.warning(f"FFprobe metadata extraction failed: {e}. Trying Hachoir fallback...")
        try:
            parser = createParser(str(file_path))
            if not parser:
                return data 
            with parser:
                h_metadata = extractMetadata(parser)
            if not h_metadata:
                return data 
            
            if h_metadata.has("duration") and data['duration'] == 0:
                data['duration'] = int(h_metadata.get("duration").total_seconds())
            if h_metadata.has("width") and data['width'] == 0:
                data['width'] = int(h_metadata.get("width"))
            if h_metadata.has("height") and data['height'] == 0:
                data['height'] = int(h_metadata.get("height"))
            logger.info(f"Hachoir fallback successful for {file_path}")
        except Exception as he:
            logger.error(f"Hachoir fallback ALSO failed: {he}")
    
    return data

def parse_time(time_str: str) -> int:
    total_seconds = 0
    parts = time_str.lower().split()
    for part in parts:
        if part.endswith('s'):
            total_seconds += int(part[:-1])
        elif part.endswith('m'):
            total_seconds += int(part[:-1]) * 60
        elif part.endswith('h'):
            total_seconds += int(part[:-1]) * 3600
    return total_seconds

def progress_keyboard():
    return InlineKeyboardMarkup([[InlineKeyboardButton("Cancel ❌", callback_data="cancel_task")]])

def delete_caption_keyboard():
    return InlineKeyboardMarkup([[InlineKeyboardButton("Delete Caption 🗑️", callback_data="delete_caption")]])

def mode_check_keyboard(uid: int) -> InlineKeyboardMarkup:
    audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
    caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
    youtube_status = "✅ ON" if uid in YOUTUBE_MODE else "❌ OFF"
    
    waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
    waiting_status = f" ({waiting_count} orders pending)" if waiting_count > 0 else ""
    
    keyboard = [
        [InlineKeyboardButton(f"MKV Audio Change Mode {audio_status}{waiting_status}", callback_data="toggle_audio_mode")],
        [InlineKeyboardButton(f"Edit Caption Mode {caption_status}", callback_data="toggle_caption_mode")],
        [InlineKeyboardButton(f"YouTube Mode {youtube_status}", callback_data="toggle_youtube_mode")]
    ]
    return InlineKeyboardMarkup(keyboard)

def get_audio_tracks_ffprobe(file_path: Path) -> list:
    """Uses ffprobe to get a list of audio streams with their index and title."""
    try:
        cmd = [
            "ffprobe",
            "-v", "quiet",
            "-print_format", "json",
            "-show_streams",
            str(file_path)
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, check=True, timeout=60)
        metadata = json.loads(result.stdout)
        
        audio_tracks = []
        for stream in metadata.get('streams', []):
            if stream.get('codec_type') == 'audio':
                stream_index = stream.get('index') 
                title = stream.get('tags', {}).get('title', 'N/A')
                language = stream.get('tags', {}).get('language', 'und') 
                audio_tracks.append({
                    'stream_index': stream_index,
                    'title': title,
                    'language': language
                })
        return audio_tracks
    except Exception as e:
        logger.error(f"FFprobe error: {e}")
        return []

# --- NEW HELPER: Check if file has OPUS audio ---
def has_opus_audio(file_path: Path) -> bool:
    try:
        cmd = [
            "ffprobe",
            "-v", "error",
            "-select_streams", "a",
            "-show_entries", "stream=codec_name",
            "-of", "default=noprint_wrappers=1:nokey=1",
            str(file_path)
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, check=True, timeout=30)
        return "opus" in result.stdout.lower()
    except Exception as e:
        logger.error(f"Error checking OPUS audio: {e}")
        return False
# ------------------------------------------------

def format_size(bytes_size):
    if not bytes_size or bytes_size == 0:
        return "N/A"
    size_name = ("B", "KB", "MB", "GB", "TB")
    i = int(math.floor(math.log(bytes_size, 1024)))
    p = math.pow(1024, i)
    s = round(bytes_size / p, 2)
    return "%s %s" % (s, size_name[i])

# --- PROGRESS BAR HELPER ---
PROGRESS_CACHE = {}

def make_progress_bar(percent):
    filled = int(percent / 5)
    return "█" * filled + "░" * (20 - filled)

async def progress_callback(current, total, action, message, start_time):
    if message.chat.id in HIDE_PROGRESS_BAR:
        return
    if total == 0: return
    now = time.time()
    msg_id = message.id
    if msg_id in PROGRESS_CACHE:
        if now - PROGRESS_CACHE[msg_id] < 5: 
            return
    PROGRESS_CACHE[msg_id] = now
    
    percent = (current / total) * 100
    speed = current / (now - start_time) if now > start_time else 0
    
    text = (
        f"**{action}**\n"
        f"`[{make_progress_bar(percent)}]` **{percent:.2f}%**\n"
        f"**Size:** `{format_size(current)} / {format_size(total)}`\n"
        f"**Speed:** `{format_size(speed)}/s`"
    )
    try:
        await message.edit_text(text, reply_markup=progress_keyboard())
    except Exception:
        pass
# ---------------------------

async def update_batch_status(c, m, uid, status_text):
    if uid in BATCH_STATUS_MSG:
        try:
            await c.edit_message_text(m.chat.id, BATCH_STATUS_MSG[uid], status_text)
        except Exception:
            msg = await m.reply_text(status_text)
            BATCH_STATUS_MSG[uid] = msg.id
            async def auto_delete(msg_obj):
                await asyncio.sleep(15)
                try: await msg_obj.delete()
                except: pass
            asyncio.ensure_future(auto_delete(msg))
    else:
        msg = await m.reply_text(status_text)
        BATCH_STATUS_MSG[uid] = msg.id
        async def auto_delete(msg_obj, u):
            await asyncio.sleep(15)
            try: 
                await msg_obj.delete()
                if u in BATCH_STATUS_MSG:
                    del BATCH_STATUS_MSG[u]
            except: pass
        asyncio.ensure_future(auto_delete(msg, uid))

async def add_to_queue(uid, c, m, original_name, is_url=False, url=None, is_yt=False, yt_fmt=None, yt_title=None):
    if uid not in USER_QUEUES:
        USER_QUEUES[uid] = asyncio.Queue()
    
    try:
        if is_yt:
            status_msg = await m.reply_text(f"Queue: Processing YT Download...", reply_markup=progress_keyboard())
        else:
            status_msg = await m.reply_text(f"Queue: Processing started for `{original_name}`...", reply_markup=progress_keyboard())
    except:
        status_msg = None

    await USER_QUEUES[uid].put({
        'message': m,
        'original_name': original_name,
        'status_msg': status_msg,
        'is_url': is_url,
        'url': url,
        'is_yt': is_yt,
        'yt_fmt': yt_fmt,
        'yt_title': yt_title
    })
    
    if uid not in USER_WORKERS or USER_WORKERS[uid].done():
         USER_WORKERS[uid] = asyncio.create_task(process_queue_handler(uid, c))

def generate_post_caption(data: dict) -> str:
    image_name = data.get('image_name', DEFAULT_POST_DATA['image_name'])
    genres = data.get('genres', DEFAULT_POST_DATA['genres'])
    season_list_raw = data.get('season_list_raw', DEFAULT_POST_DATA['season_list_raw'])

    season_entries = []
    
    parts = re.split(r'[,\s]+', season_list_raw.strip())
    parts = [p.strip() for p in parts if p.strip()]

    for part in parts:
        if '-' in part:
            try:
                start, end = map(int, part.split('-'))
                if start > end:
                    start, end = end, start
                for i in range(start, end + 1):
                    season_entries.append(f"**{image_name} Season {i:02d}**") 
            except ValueError:
                continue
        else:
            try:
                num = int(part)
                season_entries.append(f"**{image_name} Season {num:02d}**")
            except ValueError:
                continue

    unique_season_entries = list(dict.fromkeys(season_entries))
    if not unique_season_entries:
        unique_season_entries.append("**Coming Soon...**")
    elif unique_season_entries[-1] != "**Coming Soon...**" and unique_season_entries[0] != "**Coming Soon...**":
        unique_season_entries.append("**Coming Soon...**")
        
    season_text = "\n".join(unique_season_entries)

    base_caption = (
        f"**{image_name}**\n"
        f"**────────────────────**\n"
        f"**‣ Audio - Hindi Official**\n"
        f"**‣ Quality - 480p, 720p, 1080p**\n"
        f"**‣ Genres - {genres}**\n"
        f"**────────────────────**"
    )

    collapsible_text_parts = [
        f"> **{image_name} All Season List :-**", 
        "> " 
    ]
    
    for line in season_text.split('\n'):
        collapsible_text_parts.append(f"> {line}")
        collapsible_text_parts.append("> ") 
        
    if collapsible_text_parts and collapsible_text_parts[-1] == "> ":
        collapsible_text_parts.pop()
        
    collapsible_text = "\n".join(collapsible_text_parts)
    final_caption = f"{base_caption}\n\n{collapsible_text}"
    
    return final_caption


async def download_stream(resp, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None):
    total = 0
    try:
        size = int(resp.headers.get("Content-Length", 0))
    except:
        size = 0
    chunk_size = 1024 * 1024
    start_t = time.time()
    try:
        with out_path.open("wb") as f:
            async for chunk in resp.content.iter_chunked(chunk_size):
                if cancel_event and cancel_event.is_set():
                    return False, "Operation cancelled by user."
                if not chunk:
                    break
                if total > MAX_SIZE:
                    return False, "File size cannot exceed 4GB."
                total += len(chunk)
                f.write(chunk)
                
                if message and size > 0:
                    await progress_callback(total, size, "Downloading...", message, start_t)
    except Exception as e:
        return False, str(e)
    return True, None

async def download_url_generic(url: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None):
    for attempt in range(1, 11):
        timeout = aiohttp.ClientTimeout(total=7200)
        headers = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"}
        connector = aiohttp.TCPConnector(limit=0, force_close=True)
        try:
            async with aiohttp.ClientSession(timeout=timeout, headers=headers, connector=connector) as sess:
                async with sess.get(url, allow_redirects=True) as resp:
                    if resp.status == 404 or resp.status != 200:
                        if attempt < 10:
                            await asyncio.sleep(2)
                            continue
                        return False, f"HTTP {resp.status}"
                    return await download_stream(resp, out_path, message, cancel_event=cancel_event)
        except Exception as e:
            if attempt < 10:
                await asyncio.sleep(2)
                continue
            return False, str(e)
    return False, "Failed after 10 attempts"

async def download_drive_file(file_id: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None):
    base = f"https://drive.google.com/uc?export=download&id={file_id}"
    for attempt in range(1, 11):
        timeout = aiohttp.ClientTimeout(total=7200)
        headers = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"}
        connector = aiohttp.TCPConnector(limit=0, force_close=True)
        try:
            async with aiohttp.ClientSession(timeout=timeout, headers=headers, connector=connector) as sess:
                async with sess.get(base, allow_redirects=True) as resp:
                    if resp.status == 200 and "content-disposition" in (k.lower() for k in resp.headers.keys()):
                        return await download_stream(resp, out_path, message, cancel_event=cancel_event)
                    if resp.status == 404 or resp.status >= 500:
                        if attempt < 10:
                            await asyncio.sleep(2)
                            continue
                    text = await resp.text(errors="ignore")
                    m = re.search(r"confirm=([0-9A-Za-z-_]+)", text)
                    if m:
                        token = m.group(1)
                        download_url = f"https://drive.google.com/uc?export=download&confirm={token}&id={file_id}"
                        async with sess.get(download_url, allow_redirects=True) as resp2:
                            if resp2.status == 404 or resp2.status >= 500:
                                if attempt < 10:
                                    await asyncio.sleep(2)
                                    continue
                            if resp2.status != 200:
                                return False, f"HTTP {resp2.status}"
                            return await download_stream(resp2, out_path, message, cancel_event=cancel_event)
                    for k, v in resp.cookies.items():
                        if k.startswith("download_warning"):
                            token = v.value
                            download_url = f"https://drive.google.com/uc?export=download&confirm={token}&id={file_id}"
                            async with sess.get(download_url, allow_redirects=True) as resp2:
                                if resp2.status == 404 or resp2.status >= 500:
                                    if attempt < 10:
                                        await asyncio.sleep(2)
                                        continue
                                if resp2.status != 200:
                                    return False, f"HTTP {resp2.status}"
                                return await download_stream(resp2, out_path, message, cancel_event=cancel_event)
                    
                    if attempt < 10 and resp.status != 200:
                        await asyncio.sleep(2)
                        continue
                    return False, "Google Drive requires permission or the link is not public."
        except Exception as e:
            if attempt < 10:
                await asyncio.sleep(2)
                continue
            return False, str(e)
    return False, "Failed after 10 attempts"

async def set_bot_commands():
    cmds = [
        BotCommand("start", "Start bot / Help"),
        BotCommand("upload_url", "Download & Upload file from URL (admin only)"),
        BotCommand("youtube", "Toggle YouTube Multi-download mode (admin only)"),
        BotCommand("file", "Load cookies.txt for yt-dlp (admin only)"),
        BotCommand("proxy", "Select Proxy for yt-dlp (admin only)"),
        BotCommand("setthumb", "Set custom thumbnail (admin only)"),
        BotCommand("view_thumb", "View your thumbnail (admin only)"),
        BotCommand("del_thumb", "Delete your thumbnail (admin only)"),
        BotCommand("set_caption", "Set custom caption (admin only)"),
        BotCommand("view_caption", "View your caption (admin only)"),
        BotCommand("edit_caption_mode", "Toggle edit caption mode (admin only)"),
        BotCommand("rename", "Rename replied video (admin only)"),
        BotCommand("mkv_video_audio_change", "MKV audio track change mode (admin only)"),
        BotCommand("create_post", "Create new post (admin only)"), 
        BotCommand("mode_check", "Check current mode status (admin only)"), 
        BotCommand("broadcast", "Broadcast (admin only)"),
        BotCommand("progress_bar", "Toggle progress bar ON/OFF (admin only)"),
        BotCommand("help", "Help")
    ]
    try:
        await app.set_bot_commands(cmds)
    except Exception as e:
        logger.warning("Set commands error: %s", e)

async def sequential_upload_task(uid, client, message, tmp_path, renamed_file, status_msg_id, cancel_event, custom_caption=None):
    """Background task that waits for upload lock to ensure sequential uploads."""
    if uid not in USER_UPLOAD_LOCKS:
        USER_UPLOAD_LOCKS[uid] = asyncio.Lock()
    
    async with USER_UPLOAD_LOCKS[uid]:
        if cancel_event.is_set():
            if tmp_path.exists(): tmp_path.unlink()
            return
        await process_file_and_upload(client, message, tmp_path, original_name=renamed_file, messages_to_delete=[status_msg_id], cancel_event_passed=cancel_event, custom_caption_override=custom_caption)

# --- QUEUE WORKER ---
async def process_queue_handler(uid, client):
    """Worker function that processes tasks sequentially for a user."""
    queue = USER_QUEUES[uid]
    while not queue.empty():
        task_data = await queue.get()
        try:
            m = task_data.get('message')
            original_name = task_data.get('original_name')
            status_msg = task_data.get('status_msg') 
            is_url = task_data.get('is_url', False)
            is_yt = task_data.get('is_yt', False)
            
            if is_yt:
                # Direct handle YouTube inside queue to prevent parallel processing overload
                url = task_data.get('url')
                yt_fmt = task_data.get('yt_fmt')
                yt_title = task_data.get('yt_title')
                await process_youtube_download(client, status_msg, uid, url, yt_fmt, yt_title, queued=True, original_message=m)
            elif is_url:
                url = task_data.get('url')
                await download_and_process_generic(client, m, url, status_msg)
            else:
                # Start Processing
                file_info = m.video or m.document
                
                cancel_event = asyncio.Event()
                TASKS.setdefault(uid, []).append(cancel_event)

                tmp_path = TMP / f"forwarded_{uid}_{int(datetime.now().timestamp())}_{original_name}"
                
                try:
                    # 1. Download Phase (Sequential)
                    if status_msg:
                        try:
                            await status_msg.edit("Downloading...", reply_markup=progress_keyboard())
                        except: pass
                    
                    start_t = time.time()
                    async def dl_prog(current, total):
                        if cancel_event.is_set():
                            client.stop_transmission()
                        if status_msg:
                            await progress_callback(current, total, "Downloading...", status_msg, start_t)
                            
                    await m.download(file_name=str(tmp_path), progress=dl_prog)
                    
                    if cancel_event.is_set():
                         if tmp_path.exists(): tmp_path.unlink()
                         TASKS[uid].remove(cancel_event)
                         continue

                    try:
                        if status_msg:
                            await status_msg.edit("Download complete, uploading to Telegram...", reply_markup=None)
                    except Exception:
                        pass

                    renamed_file = generate_new_filename(original_name)
                    
                    # 2. Upload Phase (Pipelined)
                    asyncio.create_task(
                        sequential_upload_task(uid, client, m, tmp_path, renamed_file, status_msg.id if status_msg else None, cancel_event)
                    )
                
                except Exception as e:
                    logger.error(f"Queue Item Failed: {e}")
                    if status_msg:
                        await status_msg.edit(f"Queue Error: {e}")
                    else:
                        await m.reply_text(f"Queue Error for `{original_name}`: {e}")
                    if tmp_path.exists():
                        tmp_path.unlink()
                finally:
                    pass

        except Exception as e:
            logger.error(f"Queue Loop Error: {e}")
        finally:
            queue.task_done()
    
    # Cleanup when queue is empty
    del USER_WORKERS[uid]
    del USER_QUEUES[uid]

# --- YT-DLP CORE FUNCTIONS ---
async def fetch_youtube_formats(c, m, url):
    uid = m.from_user.id
    if uid not in YOUTUBE_MODE:
        await m.reply_text("YouTube Mode is currently OFF. Please turn it on using the `/youtube` command to download YouTube videos.")
        return

    status_msg = await m.reply_text("Fetching YouTube formats...", quote=True)
    
    try:
        ydl_opts = {'quiet': True, 'no_warnings': True}
        if os.path.exists(COOKIE_FILE_PATH):
            ydl_opts['cookiefile'] = COOKIE_FILE_PATH
        if uid in USER_PROXY:
            ydl_opts['proxy'] = USER_PROXY[uid]

        def extract():
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                return ydl.extract_info(url, download=False)
        
        info = await asyncio.to_thread(extract)
        formats = info.get('formats', [])
        
        keyboard = []
        added_resolutions = set()
        
        session_id = f"yt_{uid}_{int(time.time())}"
        YT_SESSIONS[session_id] = {
            'url': url,
            'title': info.get('title', 'YouTube Video'),
            'formats_data': {}, # index -> dict
            'selected': [] # list of indices
        }
        
        fmt_index = 0
        for f in formats:
            ext = f.get('ext', '')
            res = f.get('height')
            size = f.get('filesize') or f.get('filesize_approx')
            vcodec = f.get('vcodec', 'none')
            
            if vcodec != 'none' and res and size:
                if res not in added_resolutions:
                    added_resolutions.add(res)
                    size_str = format_size(size)
                    format_id = f.get('format_id')
                    
                    dl_format = f"{format_id}+bestaudio/best" if f.get('acodec') == 'none' else format_id
                    
                    YT_SESSIONS[session_id]['formats_data'][fmt_index] = {
                        'format': dl_format,
                        'res': res,
                        'ext': ext,
                        'size_str': size_str
                    }
                    
                    # Row with direct download button AND add button
                    btn_direct = InlineKeyboardButton(f"{res}p - {size_str}", callback_data=f"yt_dl_{session_id}_{fmt_index}")
                    btn_add = InlineKeyboardButton("➕ Add", callback_data=f"yt_add_{session_id}_{fmt_index}")
                    keyboard.append([btn_direct, btn_add])
                    
                    fmt_index += 1
        
        if not keyboard:
            await status_msg.edit("No suitable video formats found.")
            return
        
        # Bottom Actions
        keyboard.append([InlineKeyboardButton("✅ Download Selected (OK)", callback_data=f"yt_ok_{session_id}")])
        if uid in YT_LAST_SELECTION and len(YT_LAST_SELECTION[uid]) > 0:
            keyboard.append([InlineKeyboardButton("🔄 Add Same Quality", callback_data=f"yt_same_{session_id}")])
        keyboard.append([InlineKeyboardButton("Cancel ❌", callback_data="cancel_yt")])
        
        await status_msg.edit(
            f"**Title:** {info.get('title')}\n\nSelect Quality (Click Quality for direct download, or 'Add' for multiple):",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )

    except Exception as e:
        logger.error(f"YT-DLP Error: {e}")
        await status_msg.edit(f"Failed to fetch YouTube formats: {e}")

# Callbacks for Advanced YT Panel
@app.on_callback_query(filters.regex(r"^yt_dl_"))
async def yt_direct_dl_callback(c: Client, cb: CallbackQuery):
    cb_data = cb.data
    parts = cb_data.split("_")
    session_id = f"{parts[2]}_{parts[3]}_{parts[4]}"
    fmt_index = int(parts[5])
    
    uid = cb.from_user.id
    if str(uid) not in session_id:
        await cb.answer("Unauthorized.", show_alert=True)
        return
        
    session = YT_SESSIONS.get(session_id)
    if not session:
        await cb.answer("Session expired.", show_alert=True)
        return
        
    fmt_data = session['formats_data'][fmt_index]
    
    # Save to last selection for direct too? Optional, let's just do it
    YT_LAST_SELECTION[uid] = [fmt_data['res']]
    
    await cb.message.edit_text("Queuing direct YouTube download...", reply_markup=progress_keyboard())
    await add_to_queue(uid, c, cb.message, "yt_video", is_yt=True, url=session['url'], yt_fmt=fmt_data['format'], yt_title=session['title'])

@app.on_callback_query(filters.regex(r"^yt_add_"))
async def yt_add_callback(c: Client, cb: CallbackQuery):
    cb_data = cb.data
    parts = cb_data.split("_")
    session_id = f"{parts[2]}_{parts[3]}_{parts[4]}"
    fmt_index = int(parts[5])
    
    uid = cb.from_user.id
    if str(uid) not in session_id:
        await cb.answer("Unauthorized.", show_alert=True)
        return
        
    session = YT_SESSIONS.get(session_id)
    if not session:
        await cb.answer("Session expired.", show_alert=True)
        return
        
    if fmt_index not in session['selected']:
        session['selected'].append(fmt_index)
        await cb.answer("Quality added to list!")
        
        # Rebuild keyboard
        keyboard = []
        for i, fmt in session['formats_data'].items():
            btn_direct = InlineKeyboardButton(f"{fmt['res']}p - {fmt['size_str']}", callback_data=f"yt_dl_{session_id}_{i}")
            if i in session['selected']:
                btn_add = InlineKeyboardButton("✅ Added", callback_data=f"yt_add_{session_id}_{i}")
            else:
                btn_add = InlineKeyboardButton("➕ Add", callback_data=f"yt_add_{session_id}_{i}")
            keyboard.append([btn_direct, btn_add])
            
        keyboard.append([InlineKeyboardButton("✅ Download Selected (OK)", callback_data=f"yt_ok_{session_id}")])
        if uid in YT_LAST_SELECTION and len(YT_LAST_SELECTION[uid]) > 0:
            keyboard.append([InlineKeyboardButton("🔄 Add Same Quality", callback_data=f"yt_same_{session_id}")])
        keyboard.append([InlineKeyboardButton("Cancel ❌", callback_data="cancel_yt")])
        
        try:
            await cb.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup(keyboard))
        except: pass
    else:
        # Toggle off if clicked again
        session['selected'].remove(fmt_index)
        await cb.answer("Quality removed from list.")
        # Rebuild keyboard code again...
        keyboard = []
        for i, fmt in session['formats_data'].items():
            btn_direct = InlineKeyboardButton(f"{fmt['res']}p - {fmt['size_str']}", callback_data=f"yt_dl_{session_id}_{i}")
            if i in session['selected']:
                btn_add = InlineKeyboardButton("✅ Added", callback_data=f"yt_add_{session_id}_{i}")
            else:
                btn_add = InlineKeyboardButton("➕ Add", callback_data=f"yt_add_{session_id}_{i}")
            keyboard.append([btn_direct, btn_add])
            
        keyboard.append([InlineKeyboardButton("✅ Download Selected (OK)", callback_data=f"yt_ok_{session_id}")])
        if uid in YT_LAST_SELECTION and len(YT_LAST_SELECTION[uid]) > 0:
            keyboard.append([InlineKeyboardButton("🔄 Add Same Quality", callback_data=f"yt_same_{session_id}")])
        keyboard.append([InlineKeyboardButton("Cancel ❌", callback_data="cancel_yt")])
        
        try:
            await cb.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup(keyboard))
        except: pass

@app.on_callback_query(filters.regex(r"^yt_ok_"))
async def yt_ok_callback(c: Client, cb: CallbackQuery):
    cb_data = cb.data
    session_id = cb_data.replace("yt_ok_", "")
    
    uid = cb.from_user.id
    if str(uid) not in session_id:
        await cb.answer("Unauthorized.", show_alert=True)
        return
        
    session = YT_SESSIONS.get(session_id)
    if not session:
        await cb.answer("Session expired.", show_alert=True)
        return
        
    if not session['selected']:
        await cb.answer("Please add at least one quality first!", show_alert=True)
        return
        
    # Save to last selection memory
    resolutions = []
    for i in session['selected']:
        resolutions.append(session['formats_data'][i]['res'])
    YT_LAST_SELECTION[uid] = resolutions
    
    await cb.message.edit_text(f"Queuing {len(session['selected'])} YouTube downloads...", reply_markup=None)
    
    for i in session['selected']:
        fmt_data = session['formats_data'][i]
        await add_to_queue(uid, c, cb.message, "yt_video", is_yt=True, url=session['url'], yt_fmt=fmt_data['format'], yt_title=session['title'])

@app.on_callback_query(filters.regex(r"^yt_same_"))
async def yt_same_callback(c: Client, cb: CallbackQuery):
    cb_data = cb.data
    session_id = cb_data.replace("yt_same_", "")
    
    uid = cb.from_user.id
    if str(uid) not in session_id:
        await cb.answer("Unauthorized.", show_alert=True)
        return
        
    session = YT_SESSIONS.get(session_id)
    if not session:
        await cb.answer("Session expired.", show_alert=True)
        return
        
    last_res_list = YT_LAST_SELECTION.get(uid, [])
    if not last_res_list:
        await cb.answer("No previous quality memory found.", show_alert=True)
        return
        
    # Match resolutions
    matched_indices = []
    for i, fmt in session['formats_data'].items():
        if fmt['res'] in last_res_list:
            matched_indices.append(i)
            
    if not matched_indices:
        await cb.answer("None of the previously selected qualities are available for this video.", show_alert=True)
        return
        
    await cb.message.edit_text(f"Queuing {len(matched_indices)} matching YouTube downloads...", reply_markup=None)
    
    for i in matched_indices:
        fmt_data = session['formats_data'][i]
        await add_to_queue(uid, c, cb.message, "yt_video", is_yt=True, url=session['url'], yt_fmt=fmt_data['format'], yt_title=session['title'])

@app.on_callback_query(filters.regex("cancel_yt"))
async def cancel_yt_cb(c, cb: CallbackQuery):
    try:
        await cb.message.delete()
    except: pass

async def process_youtube_download(c, status_msg, uid, url, fmt, title, queued=False, original_message=None):
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    
    safe_title = re.sub(r"[\\/*?\"<>|:]", "_", title)
    if len(safe_title) > 100: safe_title = safe_title[:100]
    
    out_tmpl = str(TMP / f"yt_{uid}_{int(datetime.now().timestamp())}_{safe_title}.%(ext)s")
    
    ydl_opts = {
        'format': fmt,
        'outtmpl': out_tmpl,
        'quiet': True,
        'no_warnings': True,
        'merge_output_format': 'mkv',
    }
    if os.path.exists(COOKIE_FILE_PATH):
        ydl_opts['cookiefile'] = COOKIE_FILE_PATH
    if uid in USER_PROXY:
        ydl_opts['proxy'] = USER_PROXY[uid]
    
    last_edit = 0
    loop = asyncio.get_running_loop()
    def my_hook(d):
        nonlocal last_edit
        if d['status'] == 'downloading':
            if cancel_event.is_set():
                raise Exception("Operation cancelled by user.")
            now = time.time()
            if now - last_edit >= 5:
                last_edit = now
                downloaded = d.get('downloaded_bytes', 0)
                total = d.get('total_bytes', 0) or d.get('total_bytes_estimate', 0)
                speed = d.get('speed', 0)
                if total > 0:
                    percent = (downloaded / total) * 100
                    make_bar = make_progress_bar(percent)
                    text = (
                        f"**Downloading YouTube Video...**\n"
                        f"`[{make_bar}]` **{percent:.2f}%**\n"
                        f"**Size:** `{format_size(downloaded)} / {format_size(total)}`\n"
                        f"**Speed:** `{format_size(speed)}/s`"
                    )
                    try:
                        asyncio.run_coroutine_threadsafe(
                            status_msg.edit_text(text, reply_markup=progress_keyboard()), 
                            loop
                        )
                    except Exception:
                        pass

    ydl_opts['progress_hooks'] = [my_hook]

    try:
        def run_dl():
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=True)
                if 'requested_downloads' in info:
                    return info['requested_downloads'][0]['filepath']
                return ydl.prepare_filename(info)
        
        downloaded_file = await asyncio.to_thread(run_dl)
        actual_path = Path(downloaded_file)
        
        if cancel_event.is_set() or not actual_path.exists():
             raise Exception("Cancelled or download failed.")
             
        await status_msg.edit_text("Download complete, uploading to Telegram...", reply_markup=None)
        
        original_name = actual_path.name
        renamed_file = generate_new_filename(original_name)
        
        # New Caption Logic for YT
        custom_caption = None
        if uid not in USER_CAPTIONS:
             custom_caption = f"**{title}**"
        
        msg_context = original_message if original_message else status_msg.reply_to_message or status_msg
        
        if queued:
            # If queued, run upload task here inside worker
            await sequential_upload_task(uid, c, msg_context, actual_path, renamed_file, status_msg.id, cancel_event, custom_caption=custom_caption)
        else:
            asyncio.create_task(
                sequential_upload_task(uid, c, msg_context, actual_path, renamed_file, status_msg.id, cancel_event, custom_caption=custom_caption)
            )

    except Exception as e:
        logger.error(f"YT-DLP DL Error: {e}")
        try:
            await status_msg.edit_text(f"YouTube Download Error: {e}")
        except Exception:
            pass
        if cancel_event in TASKS.get(uid, []):
            TASKS[uid].remove(cancel_event)
# -----------------------------

# ---- handlers ----
@app.on_message(filters.command("start") & filters.private)
async def start_handler(c, m: Message):
    await set_bot_commands()
    SUBSCRIBERS.add(m.chat.id)
    text = (
        "Hi! I am URL uploader bot.\n\n"
        "Note: Many commands can only be used by the Admin (owner).\n\n"
        "Commands:\n"
        "/upload_url <url> - Download & Upload file from URL (admin only)\n"
        "/youtube - Toggle YouTube Multi-download mode (admin only)\n"
        "/file - Load cookies.txt for yt-dlp (admin only)\n"
        "/proxy - Select Proxy for yt-dlp (admin only)\n"
        "/setthumb - Send an image to set as your thumbnail (admin only)\n"
        "/view_thumb - View your thumbnail (admin only)\n"
        "/del_thumb - Delete your thumbnail (admin only)\n"
        "/set_caption - Set custom caption (admin only)\n"
        "/view_caption - View your caption (admin only)\n"
        "/edit_caption_mode - Toggle edit caption mode (admin only)\n"
        "/rename <newname.ext> - Rename replied video (admin only)\n"
        "/mkv_video_audio_change - MKV audio track change mode (admin only)\n"
        "/create_post - Create new post (admin only)\n" 
        "/mode_check - Check current mode status (admin only)\n" 
        "/progress_bar - Toggle progress bar ON/OFF (admin only)\n"
        "/broadcast <text> - Broadcast (admin only)\n"
        "/help - Help"
    )
    await m.reply_text(text)

@app.on_message(filters.command("help") & filters.private)
async def help_handler(c, m):
    await start_handler(c, m)

@app.on_message(filters.command("youtube") & filters.private)
async def youtube_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    if uid in YOUTUBE_MODE:
        YOUTUBE_MODE.discard(uid)
        await m.reply_text("YouTube Multi-download Mode is now **OFF**.")
    else:
        YOUTUBE_MODE.add(uid)
        await m.reply_text("YouTube Multi-download Mode is now **ON**.\nSend any YouTube link to see the advanced panel.")

@app.on_message(filters.command("file") & filters.private)
async def file_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    AWAITING_COOKIE_FILE.add(uid)
    await m.reply_text("Please send the `cookies.txt` file as a document, OR paste the raw text inside a message.")

@app.on_message(filters.command("proxy") & filters.private)
async def proxy_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    
    keyboard = []
    for country, proxy_url in PROXY_LIST.items():
        keyboard.append([InlineKeyboardButton(f"🌐 {country}", callback_data=f"proxy_set_{country}")])
    keyboard.append([InlineKeyboardButton("❌ Turn OFF Proxy", callback_data="proxy_set_off")])
    
    current_status = USER_PROXY.get(uid, "None (OFF)")
    await m.reply_text(f"**Proxy Selection for YT-DLP**\n\nCurrent Proxy: `{current_status}`\nSelect a proxy below:", reply_markup=InlineKeyboardMarkup(keyboard))

@app.on_callback_query(filters.regex(r"^proxy_set_"))
async def proxy_set_cb(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("Unauthorized.", show_alert=True)
        return
    
    selection = cb.data.replace("proxy_set_", "")
    if selection == "off":
        USER_PROXY.pop(uid, None)
        await cb.message.edit_text("Proxy has been turned **OFF**.")
    else:
        if selection in PROXY_LIST:
            USER_PROXY[uid] = PROXY_LIST[selection]
            await cb.message.edit_text(f"Proxy set to **{selection}**.\n`{PROXY_LIST[selection]}`")
        else:
            await cb.answer("Invalid selection.", show_alert=True)


@app.on_message(filters.command("progress_bar") & filters.private)
async def progress_bar_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    if uid in HIDE_PROGRESS_BAR:
        HIDE_PROGRESS_BAR.discard(uid)
        await m.reply_text("Progress bar is now ON.")
    else:
        HIDE_PROGRESS_BAR.add(uid)
        await m.reply_text("Progress bar is now OFF.")

@app.on_message(filters.command("setthumb") & filters.private)
async def setthumb_prompt(c, m):
    if not is_admin(m.from_user.id):
        await m.reply_text("You are not authorized to use this command.")
        return
    
    uid = m.from_user.id
    if len(m.command) > 1:
        time_str = " ".join(m.command[1:])
        seconds = parse_time(time_str)
        if seconds > 0:
            USER_THUMB_TIME[uid] = seconds
            await m.reply_text(f"Thumbnail generation time set to: {seconds} seconds.")
        else:
            await m.reply_text("Please provide time in correct format. Example: `/setthumb 5s`, `/setthumb 1m`, `/setthumb 1m 30s`")
    else:
        SET_THUMB_REQUEST.add(uid)
        await m.reply_text("Send an image (photo) — it will be set as your thumbnail.")


@app.on_message(filters.command("view_thumb") & filters.private)
async def view_thumb_cmd(c, m: Message):
    if not is_admin(m.from_user.id):
        await m.reply_text("You are not authorized to use this command.")
        return
    uid = m.from_user.id
    thumb_path = USER_THUMBS.get(uid)
    thumb_time = USER_THUMB_TIME.get(uid)
    
    if thumb_path and Path(thumb_path).exists():
        await c.send_photo(chat_id=m.chat.id, photo=thumb_path, caption="This is your saved thumbnail.")
    elif thumb_time:
        await m.reply_text(f"Your thumbnail generation time is set to: {thumb_time} seconds.")
    else:
        await m.reply_text("You don't have any thumbnail or thumbnail time saved. Use /setthumb to set one.")

@app.on_message(filters.command("del_thumb") & filters.private)
async def del_thumb_cmd(c, m: Message):
    if not is_admin(m.from_user.id):
        await m.reply_text("You are not authorized to use this command.")
        return
    uid = m.from_user.id
    thumb_path = USER_THUMBS.get(uid)
    if thumb_path and Path(thumb_path).exists():
        try:
            Path(thumb_path).unlink()
        except Exception:
            pass
        USER_THUMBS.pop(uid, None)
    
    if uid in USER_THUMB_TIME:
        USER_THUMB_TIME.pop(uid)

    if not (thumb_path or uid in USER_THUMB_TIME):
        await m.reply_text("You don't have any saved thumbnail.")
    else:
        await m.reply_text("Your thumbnail/thumbnail time has been deleted.")


@app.on_message(filters.photo & filters.private)
async def photo_handler(c, m: Message):
    if not is_admin(m.from_user.id):
        return
    uid = m.from_user.id
    
    # --- NEW: Handle Create Post Mode ---
    if uid in CREATE_POST_MODE and uid in POST_CREATION_STATE and POST_CREATION_STATE[uid]['state'] == 'awaiting_image':
        
        state_data = POST_CREATION_STATE[uid]
        state_data['message_ids'].append(m.id) 
        
        out = TMP / f"post_img_{uid}.jpg"
        try:
            download_msg = await m.reply_text("Downloading image...")
            state_data['message_ids'].append(download_msg.id)
            
            await m.download(file_name=str(out))
            img = Image.open(out)
            img.thumbnail((1080, 1080)) 
            img = img.convert("RGB")
            img.save(out, "JPEG")
            
            state_data['image_path'] = str(out)
            state_data['state'] = 'awaiting_name_change'
            
            initial_caption = generate_post_caption(state_data['post_data'])
            
            post_msg = await c.send_photo(
                chat_id=m.chat.id, 
                photo=str(out), 
                caption=initial_caption, 
                parse_mode=ParseMode.MARKDOWN
            )
            state_data['post_message_id'] = post_msg.id 
            state_data['message_ids'].append(post_msg.id) 
            
            prompt_msg = await m.reply_text(
                f"✅ Post image has been set.\n\n**Now change the image name.**\n"
                f"Current name: `{state_data['post_data']['image_name']}`\n"
                f"Please send only the **name**. Example: `One Piece`"
            )
            state_data['message_ids'].append(prompt_msg.id)

        except Exception as e:
            logger.error(f"Post creation image error: {e}")
            await m.reply_text(f"Error saving image: {e}")
            CREATE_POST_MODE.discard(uid)
            POST_CREATION_STATE.pop(uid, None)
            if out.exists(): out.unlink(missing_ok=True)
        return
    # --- END NEW: Handle Create Post Mode ---
    
    if uid in SET_THUMB_REQUEST:
        SET_THUMB_REQUEST.discard(uid)
        out = TMP / f"thumb_{uid}.jpg"
        try:
            await m.download(file_name=str(out))
            img = Image.open(out)
            img.thumbnail((320, 320))
            img = img.convert("RGB")
            img.save(out, "JPEG")
            USER_THUMBS[uid] = str(out)
            USER_THUMB_TIME.pop(uid, None)
            await m.reply_text("Your thumbnail has been saved.")
        except Exception as e:
            await m.reply_text(f"Error saving thumbnail: {e}")
    else:
        pass

# Handlers for caption
@app.on_message(filters.command("set_caption") & filters.private)
async def set_caption_prompt(c, m: Message):
    if not is_admin(m.from_user.id):
        await m.reply_text("You are not authorized to use this command.")
        return
    SET_CAPTION_REQUEST.add(m.from_user.id)
    USER_COUNTERS.pop(m.from_user.id, None)
    
    await m.reply_text(
        "Provide a caption. You can use these codes:\n"
        "1. **Number Increment:** `[01]`, `[(01)]` (Number will auto-increment)\n"
        "2. **Quality Cycle:** `[re (480p, 720p)]`\n"
        "3. **Conditional Text:** `[TEXT (XX)]` - e.g.: `[End (02)]`, `[hi (05)]` (If current episode is XX, TEXT will be added)."
    )

@app.on_message(filters.command("view_caption") & filters.private)
async def view_caption_cmd(c, m: Message):
    if not is_admin(m.from_user.id):
        await m.reply_text("You are not authorized to use this command.")
        return
    uid = m.from_user.id
    caption = USER_CAPTIONS.get(uid)
    if caption:
        await m.reply_text(f"Your saved caption:\n\n`{caption}`", reply_markup=delete_caption_keyboard())
    else:
        await m.reply_text("You don't have any saved caption. Use /set_caption to set one.")

@app.on_callback_query(filters.regex("delete_caption"))
async def delete_caption_cb(c, cb):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("You are not authorized.", show_alert=True)
        return
    if uid in USER_CAPTIONS:
        USER_CAPTIONS.pop(uid)
        USER_COUNTERS.pop(uid, None) 
        await cb.message.edit_text("Your caption has been deleted.")
    else:
        await cb.answer("You don't have any saved caption.", show_alert=True)

# Handler to toggle edit caption mode
@app.on_message(filters.command("edit_caption_mode") & filters.private)
async def toggle_edit_caption_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return

    if uid in EDIT_CAPTION_MODE:
        EDIT_CAPTION_MODE.discard(uid)
        # Clear batch if active
        if uid in BATCH_CAPTION_MODE:
            BATCH_CAPTION_MODE.discard(uid)
            BATCH_DATA.pop(uid, None)
            BATCH_STATUS_MSG.pop(uid, None)
        await m.reply_text("edit video caption mode **OFF**.\nFrom now on, uploaded videos will be renamed, thumbnails changed, and saved caption added.")
    else:
        EDIT_CAPTION_MODE.add(uid)
        await m.reply_text("edit video caption mode **ON**.\nFrom now on, only the saved caption will be added. Video name and thumbnail will remain the same.\n\n**New Feature:** Type `on` to enable file ID save mode. Type `off` to disable.")

# --- HANDLER: /mkv_video_audio_change ---
@app.on_message(filters.command("mkv_video_audio_change") & filters.private)
async def toggle_audio_change_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return

    if uid in MKV_AUDIO_CHANGE_MODE:
        MKV_AUDIO_CHANGE_MODE.discard(uid)
        await m.reply_text("MKV audio change mode has been **TURNED OFF**.")
    else:
        MKV_AUDIO_CHANGE_MODE.add(uid)
        await m.reply_text("MKV audio change mode has been **TURNED ON**. Now send an **MKV file** or any other **video file**.\n(This mode stays on until manually turned off.)")

# --- NEW HANDLER: /create_post ---
@app.on_message(filters.command("create_post") & filters.private)
async def toggle_create_post_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return

    if uid in CREATE_POST_MODE:
        CREATE_POST_MODE.discard(uid)
        if uid in POST_CREATION_STATE:
            state_data = POST_CREATION_STATE.pop(uid)
            try:
                if state_data.get('image_path'):
                    Path(state_data['image_path']).unlink(missing_ok=True)
                messages_to_delete = state_data.get('message_ids', [])
                post_id = state_data.get('post_message_id')
                if post_id and post_id in messages_to_delete:
                    messages_to_delete.remove(post_id) 
                if messages_to_delete:
                    await c.delete_messages(m.chat.id, messages_to_delete)
            except Exception as e:
                logger.warning(f"Post mode OFF cleanup error: {e}")
                
        await m.reply_text("Create Post Mode has been **TURNED OFF**.")
    else:
        CREATE_POST_MODE.add(uid)
        POST_CREATION_STATE[uid] = {
            'image_path': None, 
            'message_ids': [m.id], 
            'state': 'awaiting_image', 
            'post_data': DEFAULT_POST_DATA.copy(),
            'post_message_id': None
        }
        await m.reply_text("Create Post Mode has been **TURNED ON**.\nSend an image (**Photo**) to be used for the post.")
# ---------------------------------------------


# --- NEW HANDLER: /mode_check ---
@app.on_message(filters.command("mode_check") & filters.private)
async def mode_check_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    
    audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
    caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
    youtube_status = "✅ ON" if uid in YOUTUBE_MODE else "❌ OFF"
    
    waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
    waiting_status_text = f"{waiting_count} file(s) waiting for track order." if waiting_count > 0 else "No files are waiting."
    
    status_text = (
        "🤖 **Current Mode Status:**\n\n"
        f"1. **MKV Audio Change Mode:** `{audio_status}`\n"
        f"   - *Task:* Changes audio track order of forwarded/downloaded MKV/video files. (Stays ON until manually off)\n"
        f"   - *Status:* {waiting_status_text}\n\n"
        f"2. **Edit Caption Mode:** `{caption_status}`\n"
        f"   - *Task:* Adds saved caption without changing rename or thumbnail of forwarded videos.\n\n"
        f"3. **YouTube Mode:** `{youtube_status}`\n"
        f"   - *Task:* Multi-quality download option for YT links.\n\n"
        "Click the buttons below to toggle modes."
    )
    
    await m.reply_text(status_text, reply_markup=mode_check_keyboard(uid), parse_mode=ParseMode.MARKDOWN)

# --- NEW CALLBACK: Mode Toggle Buttons ---
@app.on_callback_query(filters.regex("toggle_(audio|caption|youtube)_mode"))
async def mode_toggle_callback(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("You are not authorized.", show_alert=True)
        return

    action = cb.data
    
    if action == "toggle_audio_mode":
        if uid in MKV_AUDIO_CHANGE_MODE:
            MKV_AUDIO_CHANGE_MODE.discard(uid)
            message = "MKV Audio Change Mode OFF."
        else:
            MKV_AUDIO_CHANGE_MODE.add(uid)
            message = "MKV Audio Change Mode ON."
            
    elif action == "toggle_caption_mode":
        if uid in EDIT_CAPTION_MODE:
            EDIT_CAPTION_MODE.discard(uid)
            message = "Edit Caption Mode OFF."
        else:
            EDIT_CAPTION_MODE.add(uid)
            message = "Edit Caption Mode ON."
            
    elif action == "toggle_youtube_mode":
        if uid in YOUTUBE_MODE:
            YOUTUBE_MODE.discard(uid)
            message = "YouTube Mode OFF."
        else:
            YOUTUBE_MODE.add(uid)
            message = "YouTube Mode ON."
            
    try:
        audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
        caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
        youtube_status = "✅ ON" if uid in YOUTUBE_MODE else "❌ OFF"
        
        waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
        waiting_status_text = f"{waiting_count} file(s) waiting for track order." if waiting_count > 0 else "No files are waiting."

        status_text = (
            "🤖 **Current Mode Status:**\n\n"
            f"1. **MKV Audio Change Mode:** `{audio_status}`\n"
            f"   - *Task:* Changes audio track order of forwarded/downloaded MKV/video files. (Stays ON until manually off)\n"
            f"   - *Status:* {waiting_status_text}\n\n"
            f"2. **Edit Caption Mode:** `{caption_status}`\n"
            f"   - *Task:* Adds saved caption without changing rename or thumbnail of forwarded videos.\n\n"
            f"3. **YouTube Mode:** `{youtube_status}`\n"
            f"   - *Task:* Multi-quality download option for YT links.\n\n"
            "Click the buttons below to toggle modes."
        )
        
        await cb.message.edit_text(status_text, reply_markup=mode_check_keyboard(uid), parse_mode=ParseMode.MARKDOWN)
        await cb.answer(message, show_alert=True)
    except Exception as e:
        logger.error(f"Callback edit error: {e}")
        await cb.answer(message, show_alert=True)


@app.on_message(filters.text & filters.private)
async def text_handler(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    text = m.text.strip()
    
    # --- HANDLE TEXT AS COOKIES FILE ---
    if uid in AWAITING_COOKIE_FILE:
        try:
            with open(COOKIE_FILE_PATH, "w", encoding="utf-8") as f:
                f.write(text)
            AWAITING_COOKIE_FILE.discard(uid)
            await m.reply_text("✅ Cookies loaded successfully from text message.")
        except Exception as e:
            await m.reply_text(f"Error saving cookies from text: {e}")
        return
    # -----------------------------------

    # --- BATCH CAPTION & UPLOAD COMMANDS (NEW) ---
    text_lower = text.lower()
    if text_lower in ["on", "off", "ok"]:
        if uid in EDIT_CAPTION_MODE:
            if text_lower == "on":
                BATCH_CAPTION_MODE.add(uid)
                BATCH_DATA[uid] = []
                await m.reply_text("Batch Caption Mode ON. Forward videos to save file IDs.")
            elif text_lower == "off":
                BATCH_CAPTION_MODE.discard(uid)
                BATCH_DATA.pop(uid, None)
                BATCH_STATUS_MSG.pop(uid, None)
                await m.reply_text("Batch Caption Mode OFF. Forwarded videos will have caption changed directly.")
            elif text_lower == "ok":
                if uid in BATCH_CAPTION_MODE and uid in BATCH_DATA and BATCH_DATA[uid]:
                    items = BATCH_DATA[uid]
                    await m.reply_text(f"Processing started for {len(items)} items...")
                    
                    for item in items:
                        msg_obj = item['message']
                        file_info_obj = item['file_info']
                        await handle_caption_only_upload_with_file(c, msg_obj, file_info_obj)
                        await asyncio.sleep(0.5)
                    
                    BATCH_DATA[uid] = []
                    if uid in BATCH_STATUS_MSG:
                        try:
                            await c.delete_messages(m.chat.id, BATCH_STATUS_MSG[uid])
                        except: pass
                        BATCH_STATUS_MSG.pop(uid, None)
                    
                    complete_msg = await m.reply_text("Batch processing complete.")
                    async def auto_delete():
                        await asyncio.sleep(5) 
                        try: await complete_msg.delete()
                        except: pass
                    asyncio.ensure_future(auto_delete())
                else:
                    await m.reply_text("Batch list is empty or mode is not ON.")
            return
        else:
            if text_lower == "on":
                BATCH_UPLOAD_MODE.add(uid)
                BATCH_DATA[uid] = []
                await m.reply_text("Batch Upload Mode ON. Send/Forward videos or URLs to queue them.")
            elif text_lower == "off":
                BATCH_UPLOAD_MODE.discard(uid)
                BATCH_DATA.pop(uid, None)
                BATCH_STATUS_MSG.pop(uid, None)
                await m.reply_text("Batch Upload Mode OFF.")
            elif text_lower == "ok":
                if uid in BATCH_UPLOAD_MODE and uid in BATCH_DATA and BATCH_DATA[uid]:
                    items = BATCH_DATA[uid]
                    await m.reply_text(f"Batch processing started for {len(items)} items...")
                    
                    for item in items:
                        if item.get('is_url'):
                            await add_to_queue(uid, c, item['message'], item['original_name'], is_url=True, url=item['url'])
                        else:
                            await add_to_queue(uid, c, item['message'], item['original_name'], is_url=False)
                        await asyncio.sleep(0.5)
                    
                    BATCH_DATA[uid] = []
                    if uid in BATCH_STATUS_MSG:
                        try:
                            await c.delete_messages(m.chat.id, BATCH_STATUS_MSG[uid])
                        except: pass
                        BATCH_STATUS_MSG.pop(uid, None)
                    
                    complete_msg = await m.reply_text("Batch queueing complete.")
                    async def auto_delete():
                        await asyncio.sleep(5) 
                        try: await complete_msg.delete()
                        except: pass
                    asyncio.ensure_future(auto_delete())
                else:
                    await m.reply_text("Batch list is empty or mode is not ON.")
            return
    # ------------------------------------

    # Handle set caption request
    if uid in SET_CAPTION_REQUEST:
        SET_CAPTION_REQUEST.discard(uid)
        USER_CAPTIONS[uid] = text
        USER_COUNTERS.pop(uid, None) 
        await m.reply_text("Your caption has been saved. Uploaded videos will use this caption.")
        return

    # --- Handle audio order input (MODIFIED) ---
    if m.reply_to_message and m.reply_to_message.id in PENDING_AUDIO_ORDERS:
        prompt_message_id = m.reply_to_message.id
        file_data = PENDING_AUDIO_ORDERS.get(prompt_message_id)
        
        if file_data['uid'] != uid:
             await m.reply_text("You cannot provide orders for this file.")
             return

        tracks = file_data['tracks']
        try:
            # Parse input like "1,3" or "2"
            new_order_str = [x.strip() for x in text.split(',') if x.strip()]
            num_tracks_in_file = len(tracks)
            
            # --- UPDATED VALIDATION: Allow any subset ---
            if not new_order_str:
                 await m.reply_text("You must provide at least one track number.")
                 return

            new_stream_map = []
            valid_user_indices = list(range(1, num_tracks_in_file + 1))
            
            for user_track_num_str in new_order_str:
                user_track_num = int(user_track_num_str) 
                if user_track_num not in valid_user_indices:
                     await m.reply_text(f"Invalid track number: {user_track_num}. Track numbers must be: {', '.join(map(str, valid_user_indices))}")
                     return
                
                stream_index_to_map = tracks[user_track_num - 1]['stream_index']
                new_stream_map.append(f"0:{stream_index_to_map}") 
            # --------------------------------------------

            asyncio.create_task(
                handle_audio_remux(
                    c, m, file_data['path'], 
                    file_data['original_name'], 
                    new_stream_map, 
                    messages_to_delete=[prompt_message_id, m.id]
                )
            )

            PENDING_AUDIO_ORDERS.pop(prompt_message_id, None) 
            return

        except ValueError:
            await m.reply_to_message.reply_text("Invalid format. Provide comma-separated numbers. Example: `1,3`")
            return
        except Exception as e:
            logger.error(f"Audio remux preparation error: {e}")
            await m.reply_to_message.reply_text(f"Error starting audio change process: {e}")
            
            try: Path(file_data['path']).unlink(missing_ok=True)
            except Exception: pass
            PENDING_AUDIO_ORDERS.pop(prompt_message_id, None)
            return
    # -----------------------------------------------------

    # --- NEW: Handle Post Creation Editing Steps ---
    if uid in CREATE_POST_MODE and uid in POST_CREATION_STATE:
        state_data = POST_CREATION_STATE[uid]
        state_data['message_ids'].append(m.id) 
        
        current_state = state_data['state']
        
        if current_state == 'awaiting_name_change':
            if not text:
                prompt_msg = await m.reply_text("Name cannot be empty. Provide a valid name.")
                state_data['message_ids'].append(prompt_msg.id)
                return
            
            state_data['post_data']['image_name'] = text
            state_data['state'] = 'awaiting_genres_add'
            
            new_caption = generate_post_caption(state_data['post_data'])
            try:
                await c.edit_message_caption(m.chat.id, state_data['post_message_id'], caption=new_caption, parse_mode=ParseMode.MARKDOWN)
            except Exception as e:
                logger.error(f"Edit caption error in name change: {e}")
                await m.reply_text("Error editing caption. Process cancelled. Turn off mode using /create_post.")
                return

            prompt_msg = await m.reply_text(
                f"✅ Image name set: `{text}`\n\n**Now add Genres.**\n"
                f"Example: `Comedy, Romance, Action`"
            )
            state_data['message_ids'].append(prompt_msg.id)
            
        elif current_state == 'awaiting_genres_add':
            state_data['post_data']['genres'] = text 
            state_data['state'] = 'awaiting_season_list'
            
            new_caption = generate_post_caption(state_data['post_data'])
            try:
                await c.edit_message_caption(m.chat.id, state_data['post_message_id'], caption=new_caption, parse_mode=ParseMode.MARKDOWN)
            except Exception as e:
                logger.error(f"Edit caption error in genres add: {e}")
                await m.reply_text("Error editing caption. Process cancelled. Turn off mode using /create_post.")
                return

            prompt_msg = await m.reply_text(
                f"✅ Genres set: `{text}`\n\n**Now change Season List.**\n"
                f"How many seasons of \"{state_data['post_data']['image_name']}\" should we add?\n"
                f"Format: Season number or range, comma or space-separated.\n"
                f"Example:\n"
                f"‣ `1` (Season 01)\n"
                f"‣ `1-2` (Season 01 to Season 02)\n"
                f"‣ `1-2 4-5` or `1-2, 4-5` (Season 01-02 and 04-05)"
            )
            state_data['message_ids'].append(prompt_msg.id)
            
        elif current_state == 'awaiting_season_list':
            if not text.strip():
                state_data['post_data']['season_list_raw'] = ""
            else:
                state_data['post_data']['season_list_raw'] = text
            
            new_caption = generate_post_caption(state_data['post_data'])
            try:
                await c.edit_message_caption(m.chat.id, state_data['post_message_id'], caption=new_caption, parse_mode=ParseMode.MARKDOWN)
            except Exception as e:
                logger.error(f"Edit caption error in season list: {e}")
                await m.reply_text("Error editing caption. Process cancelled. Turn off mode using /create_post.")
                return

            all_messages = state_data.get('message_ids', [])
            post_id = state_data.get('post_message_id')
            if post_id and post_id in all_messages:
                all_messages.remove(post_id) 
            if all_messages:
                try:
                    await c.delete_messages(m.chat.id, all_messages)
                except Exception as e:
                    logger.warning(f"Error deleting post creation messages: {e}")
            
            image_path = state_data['image_path']
            if image_path and Path(image_path).exists():
                Path(image_path).unlink(missing_ok=True)
            
            CREATE_POST_MODE.discard(uid)
            POST_CREATION_STATE.pop(uid, None)
            
            await m.reply_text("✅ Post creation successfully completed and additional messages deleted.")
            return
    # --- END NEW: Handle Post Creation Editing Steps ---


    if text.startswith("http://") or text.startswith("https://"):
        url = text
        if is_youtube_url(url):
            await fetch_youtube_formats(c, m, url)
            return

        original_name = url.split("/")[-1].split("?")[0] or "url_download"
        if uid in BATCH_UPLOAD_MODE:
            if uid not in BATCH_DATA:
                BATCH_DATA[uid] = []
            BATCH_DATA[uid].append({
                'message': m,
                'original_name': original_name,
                'is_url': True,
                'url': url
            })
            count = len(BATCH_DATA[uid])
            status_text = f"{count} items saved for batch upload."
            await update_batch_status(c, m, uid, status_text)
        else:
            await add_to_queue(uid, c, m, original_name, is_url=True, url=url)
    
@app.on_message(filters.command("upload_url") & filters.private)
async def upload_url_cmd(c, m: Message):
    if not is_admin(m.from_user.id):
        await m.reply_text("You are not authorized to use this command.")
        return
    if not m.command or len(m.command) < 2:
        await m.reply_text("Usage: /upload_url <url>\nExample: /upload_url https://example.com/file.mp4")
        return
    url = m.text.split(None, 1)[1].strip()
    
    if is_youtube_url(url):
        await fetch_youtube_formats(c, m, url)
        return

    original_name = url.split("/")[-1].split("?")[0] or "url_download"
    uid = m.from_user.id
    if uid in BATCH_UPLOAD_MODE:
        if uid not in BATCH_DATA:
            BATCH_DATA[uid] = []
        BATCH_DATA[uid].append({
            'message': m,
            'original_name': original_name,
            'is_url': True,
            'url': url
        })
        count = len(BATCH_DATA[uid])
        status_text = f"{count} items saved for batch upload."
        await update_batch_status(c, m, uid, status_text)
    else:
        await add_to_queue(uid, c, m, original_name, is_url=True, url=url)

async def handle_url_download_and_upload(c: Client, m: Message, url: str):
    uid = m.from_user.id
    try:
        status_msg = await m.reply_text("Downloading...", reply_markup=progress_keyboard())
        await download_and_process_generic(c, m, url, status_msg)
    except Exception as e:
        logger.error(f"URL Error: {e}")
        try:
            await status_msg.edit(f"Error: {e}")
        except:
            await m.reply_text(f"Error: {e}")

async def download_and_process_generic(c, m, url, status_msg):
    """Fallback for direct URLs or Google Drive if YT-DLP fails/skips"""
    uid = m.from_user.id
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    
    try:
        fname = url.split("/")[-1].split("?")[0] or f"download_{int(datetime.now().timestamp())}"
        safe_name = re.sub(r"[\\/*?\"<>|:]", "_", fname)

        # ADDED: Truncate safe_name to prevent [Errno 36] File name too long
        if len(safe_name) > 100:
            safe_name = safe_name[:100]

        video_exts = {".mp4", ".mkv", ".avi", ".mov", ".flv", ".wmv", ".webm"}
        if not any(safe_name.lower().endswith(ext) for ext in video_exts):
            safe_name += ".mp4"

        tmp_in = TMP / f"dl_{uid}_{int(datetime.now().timestamp())}_{safe_name}"
        ok, err = False, None
        
        if is_drive_url(url):
            fid = extract_drive_id(url)
            if not fid:
                await status_msg.edit("Google Drive ID not found.")
                TASKS[uid].remove(cancel_event)
                return
            ok, err = await download_drive_file(fid, tmp_in, status_msg, cancel_event=cancel_event)
        else:
            ok, err = await download_url_generic(url, tmp_in, status_msg, cancel_event=cancel_event)

        if not ok:
            await status_msg.edit(f"Download Failed: {err}")
            if tmp_in.exists(): tmp_in.unlink()
            TASKS[uid].remove(cancel_event)
            return

        await status_msg.edit("Download complete. Uploading...", reply_markup=None)
        renamed_file = generate_new_filename(safe_name)
        
        # ADDED MKV AUDIO CHANGE MODE FOR URL
        if uid in MKV_AUDIO_CHANGE_MODE:
            try:
                await status_msg.edit("Checking file for audio track analysis...", reply_markup=progress_keyboard())
                audio_tracks = await asyncio.to_thread(get_audio_tracks_ffprobe, tmp_in)
                
                if not audio_tracks:
                    await status_msg.edit("No audio tracks found in this video or FFprobe failed. Uploading directly...")
                    asyncio.create_task(
                        sequential_upload_task(uid, c, m, tmp_in, renamed_file, status_msg.id, cancel_event)
                    )
                    return
                
                track_list_text = "Audio tracks in the file:\n\n"
                for i, track in enumerate(audio_tracks, 1):
                    track_list_text += f"{i}. **Stream Index:** {track['stream_index']}, **Language:** {track['language']}, **Title:** {track['title']}\n"
                    
                track_list_text += (
                    "\n**Reply to this message with a comma-separated list of numbers** to set the audio order.\n"
                    "Example: `1,3` will keep tracks 1 and 3. `2` will keep only track 2. The rest will be removed.\n"
                )
                    
                track_list_text += (
                    "\nIf you don't want to change audio, use the `Cancel` button below or type `/mkv_video_audio_change` to turn off the mode."
                )
                
                await status_msg.edit(track_list_text, reply_markup=progress_keyboard()) 
                
                PENDING_AUDIO_ORDERS[status_msg.id] = {
                    'uid': uid,
                    'path': tmp_in, 
                    'original_name': renamed_file,
                    'tracks': audio_tracks
                }
                return # Stop here, wait for user reply
            except Exception as e:
                logger.error(f"URL Audio track analysis error: {e}")
                await status_msg.edit(f"Error analyzing audio tracks: {e}. Uploading directly...")
                # Fallback to normal upload
                asyncio.create_task(
                    sequential_upload_task(uid, c, m, tmp_in, renamed_file, status_msg.id, cancel_event)
                )
                return

        # Normal upload for URL if MKV mode is off
        asyncio.create_task(
            sequential_upload_task(uid, c, m, tmp_in, renamed_file, status_msg.id, cancel_event)
        )
    except Exception as e:
        await status_msg.edit(f"Error: {e}")
    finally:
        pass # Task cleanup in upload

async def handle_caption_only_upload(c: Client, m: Message):
    """Wrapper for handling caption change from message object"""
    file_info = m.video or m.document
    await handle_caption_only_upload_with_file(c, m, file_info)

async def handle_caption_only_upload_with_file(c: Client, m: Message, file_info):
    uid = m.from_user.id
    caption_to_use = USER_CAPTIONS.get(uid)
    if not caption_to_use:
        await m.reply_text("Edit caption mode is ON but no caption is saved. Set a caption using /set_caption.")
        return

    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    
    try:
        status_msg = await m.reply_text("Editing caption...", reply_markup=progress_keyboard())
    except Exception:
        status_msg = await m.reply_text("Editing caption...", reply_markup=progress_keyboard())
    
    try:
        source_message = m
        
        if not file_info:
            try:
                await status_msg.edit("This is not a video or document file.")
            except Exception:
                await m.reply_text("This is not a video or document file.")
            return
        
        final_caption = process_dynamic_caption(uid, caption_to_use)
        
        if file_info.file_id:
            try:
                if source_message.video or (file_info and getattr(file_info, 'duration', 0) > 0): # Treat as video
                    await c.send_video(
                        chat_id=m.chat.id,
                        video=file_info.file_id,
                        caption=final_caption,
                        thumb=file_info.thumbs[0].file_id if file_info.thumbs else None,
                        duration=file_info.duration,
                        width=file_info.width,       
                        height=file_info.height,     
                        supports_streaming=True,
                        parse_mode=ParseMode.MARKDOWN
                    )
                else:
                    await c.send_document(
                        chat_id=m.chat.id,
                        document=file_info.file_id,
                        file_name=file_info.file_name,
                        caption=final_caption,
                        thumb=file_info.thumbs[0].file_id if file_info.thumbs else None,
                        parse_mode=ParseMode.MARKDOWN
                    )
                try:
                    await status_msg.delete() # SILENT SUCCESS
                except Exception:
                    pass
            except Exception as e:
                try:
                    await status_msg.edit(f"Caption edit error: {e}", reply_markup=None)
                except Exception:
                    await m.reply_text(f"Caption edit error: {e}", reply_markup=None)
                return
        else:
            try:
                await status_msg.edit("File ID not found.", reply_markup=None)
            except Exception:
                await m.reply_text("File ID not found.", reply_markup=None)
            return

    except Exception as e:
        traceback.print_exc()
        try:
            await status_msg.edit(f"Caption edit error: {e}", reply_markup=None)
        except Exception:
            await m.reply_text(f"Caption edit error: {e}", reply_markup=None)
    finally:
        try:
            TASKS[uid].remove(cancel_event)
        except Exception:
            pass

@app.on_message(filters.private & (filters.video | filters.document))
async def forwarded_file_or_direct_file(c: Client, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return

    # --- NEW: HANDLE DOCUMENT AS COOKIES FILE ---
    if uid in AWAITING_COOKIE_FILE and m.document:
        try:
            await m.download(file_name=COOKIE_FILE_PATH)
            AWAITING_COOKIE_FILE.discard(uid)
            await m.reply_text("✅ Cookies loaded successfully from document.")
        except Exception as e:
            await m.reply_text(f"Error saving cookies from document: {e}")
        return
    # --------------------------------------------

    # --- Check for MKV Audio Change Mode first ---
    if uid in MKV_AUDIO_CHANGE_MODE:
        await handle_audio_change_file(c, m)
        return
    # -------------------------------------------------

    # Check if the user is in edit caption mode
    if uid in EDIT_CAPTION_MODE: 
        # --- NEW BATCH LOGIC ---
        if uid in BATCH_CAPTION_MODE:
            file_info = m.video or m.document
            if not file_info: 
                return
            
            if uid not in BATCH_DATA: 
                BATCH_DATA[uid] = []
            
            BATCH_DATA[uid].append({
                'message': m,
                'file_info': file_info
            })
            
            count = len(BATCH_DATA[uid])
            status_text = f"{count} video file IDs saved."
            await update_batch_status(c, m, uid, status_text)
            return
        # ------------------------

        await handle_caption_only_upload(c, m)
        return

    # --- SEQUENTIAL QUEUE LOGIC START ---
    file_info = m.video or m.document
    
    if file_info and file_info.file_name:
        original_name = file_info.file_name
    elif m.video:
        original_name = f"video_{file_info.file_unique_id}.mp4"
    else:
        original_name = f"file_{file_info.file_unique_id}"

    if uid in BATCH_UPLOAD_MODE:
        if uid not in BATCH_DATA: 
            BATCH_DATA[uid] = []
        BATCH_DATA[uid].append({
            'message': m,
            'original_name': original_name,
            'is_url': False
        })
        count = len(BATCH_DATA[uid])
        status_text = f"{count} files saved for batch upload."
        await update_batch_status(c, m, uid, status_text)
        return

    await add_to_queue(uid, c, m, original_name, is_url=False)
    # --- SEQUENTIAL QUEUE LOGIC END ---

# --- HANDLER FUNCTION: Handle file in audio change mode ---
async def handle_audio_change_file(c: Client, m: Message):
    uid = m.from_user.id
    file_info = m.video or m.document
    
    if not file_info:
        await m.reply_text("This is not a video file.")
        return
    
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    
    tmp_path = None
    status_msg = None
    try:
        original_name = file_info.file_name or f"video_{file_info.file_unique_id}.mkv"
        if not '.' in original_name:
            original_name += '.mkv'
            
        tmp_path = TMP / f"audio_change_{uid}_{int(datetime.now().timestamp())}_{original_name}"
        
        status_msg = await m.reply_text("Downloading file to analyze audio tracks...", reply_markup=progress_keyboard())
        
        start_t = time.time()
        async def dl_prog(current, total):
            if cancel_event.is_set():
                c.stop_transmission()
            if status_msg:
                await progress_callback(current, total, "Downloading...", status_msg, start_t)
                
        await m.download(file_name=str(tmp_path), progress=dl_prog)
        
        audio_tracks = await asyncio.to_thread(get_audio_tracks_ffprobe, tmp_path)
        
        if not audio_tracks:
            await status_msg.edit("No audio tracks found in this video or FFprobe failed.")
            tmp_path.unlink(missing_ok=True)
            return

        track_list_text = "Audio tracks in the file:\n\n"
        for i, track in enumerate(audio_tracks, 1):
            track_list_text += f"{i}. **Stream Index:** {track['stream_index']}, **Language:** {track['language']}, **Title:** {track['title']}\n"
            
        track_list_text += (
            "\n**Reply to this message with a comma-separated list of numbers** to set the audio order.\n"
            "Example: `1,3` will keep tracks 1 and 3. `2` will keep only track 2. The rest will be removed.\n"
        )
            
        track_list_text += (
            "\nIf you don't want to change audio, use the `Cancel` button below or type `/mkv_video_audio_change` to turn off the mode."
        )
        
        await status_msg.edit(track_list_text, reply_markup=progress_keyboard()) 
        
        PENDING_AUDIO_ORDERS[status_msg.id] = {
            'uid': uid,
            'path': tmp_path, 
            'original_name': original_name,
            'tracks': audio_tracks
        }
        
    except Exception as e:
        logger.error(f"Audio track analysis error: {e}")
        if status_msg:
            await status_msg.edit(f"Error analyzing audio tracks: {e}")
        else:
            await m.reply_text(f"Error analyzing audio tracks: {e}")
        if tmp_path and tmp_path.exists():
            tmp_path.unlink(missing_ok=True)
    finally:
        try:
            TASKS[uid].remove(cancel_event)
        except Exception:
            pass

# --- HANDLER FUNCTION: Handle audio remux ---
async def handle_audio_remux(c: Client, m: Message, in_path: Path, original_name: str, new_stream_map: list, messages_to_delete: list = None):
    uid = m.from_user.id
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    
    out_name = generate_new_filename(original_name)
    if not out_name.lower().endswith(".mkv"):
        out_name = Path(out_name).stem + ".mkv"
    
    asyncio.create_task(
        sequential_remux_upload_task(uid, c, m, in_path, out_name, new_stream_map, messages_to_delete, cancel_event)
    )

async def sequential_remux_upload_task(uid, c, m, in_path, out_name, new_stream_map, messages_to_delete, cancel_event):
    if uid not in USER_UPLOAD_LOCKS:
        USER_UPLOAD_LOCKS[uid] = asyncio.Lock()
    
    async with USER_UPLOAD_LOCKS[uid]:
        if cancel_event.is_set():
             if in_path.exists(): in_path.unlink()
             return

        out_path = TMP / f"remux_{uid}_{int(datetime.now().timestamp())}_{out_name}"
        
        map_args = ["-map", "0:v", "-map", "0:s?", "-map", "0:d?"] 
        for stream_index in new_stream_map:
            map_args.extend(["-map", stream_index])
            
        cmd = [
            "ffmpeg",
            "-i", str(in_path),
            "-disposition:a", "0",            
            *map_args,
            "-disposition:a:0", "default",
            "-metadata:s:a", "title=[@TA_HD_Anime] Telegram Channel", 
            "-c", "copy",
            "-metadata", "handler_name=", 
            str(out_path)
        ]

        status_msg = None
        if messages_to_delete:
             pass

        try:
            status_msg = await m.reply_text("Changing audio track order (Remuxing)...", reply_markup=progress_keyboard())
            
            result = await asyncio.to_thread(
                subprocess.run,
                cmd,
                capture_output=True,
                text=True,
                check=False,
                timeout=3600
            )
            
            if result.returncode != 0:
                logger.error(f"FFmpeg Remux failed: {result.stderr}")
                out_path.unlink(missing_ok=True)
                raise Exception(f"FFmpeg Remux failed. Error: {result.stderr[:500]}...")

            if not out_path.exists() or out_path.stat().st_size == 0:
                raise Exception("Modified file not found or size is zero.")

            await status_msg.edit("Audio change complete, uploading file...", reply_markup=progress_keyboard())
            
            all_messages_to_delete = messages_to_delete if messages_to_delete else []
            all_messages_to_delete.append(status_msg.id)

            await process_file_and_upload(c, m, out_path, original_name=out_name, messages_to_delete=all_messages_to_delete, cancel_event_passed=cancel_event) 

        except Exception as e:
            logger.error(f"Audio remux process error: {e}")
            try:
                if status_msg:
                    await status_msg.edit(f"Audio change process failed: {e}")
                else:
                    await m.reply_text(f"Audio change process failed: {e}")
            except Exception:
                pass
        finally:
            try:
                in_path.unlink(missing_ok=True)
                if out_path.exists(): out_path.unlink(missing_ok=True)
                TASKS[uid].remove(cancel_event)
            except Exception:
                pass


@app.on_message(filters.command("rename") & filters.private)
async def rename_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    if not m.reply_to_message or not (m.reply_to_message.video or m.reply_to_message.document):
        await m.reply_text("Reply to a video/document file with this command.\nUsage: /rename new_name.mp4")
        return
    if len(m.command) < 2:
        await m.reply_text("Provide a new file name. Example: /rename new_video.mp4")
        return
    new_name = m.text.split(None, 1)[1].strip()
    new_name = re.sub(r"[\\/*?\"<>|:]", "_", new_name)
    
    await m.reply_text(f"Video will be renamed to: {new_name}\n(The replied file will be downloaded and re-uploaded for renaming)")

    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    try:
        status_msg = await m.reply_text("Downloading file for renaming...", reply_markup=progress_keyboard())
    except Exception:
        status_msg = await m.reply_text("Downloading file for renaming...", reply_markup=progress_keyboard())
    tmp_out = TMP / f"rename_{uid}_{int(datetime.now().timestamp())}_{new_name}"
    try:
        start_t = time.time()
        async def dl_prog(current, total):
            if cancel_event.is_set():
                c.stop_transmission()
            if status_msg:
                await progress_callback(current, total, "Downloading...", status_msg, start_t)
                
        await m.reply_to_message.download(file_name=str(tmp_out), progress=dl_prog)
        
        try:
            await status_msg.edit("Download complete, uploading with new name...", reply_markup=None)
        except Exception:
            await m.reply_text("Download complete, uploading with new name...", reply_markup=None)
        
        # Use sequential upload logic
        asyncio.create_task(
            sequential_upload_task(uid, c, m, tmp_out, new_name, status_msg.id, cancel_event)
        )
    except Exception as e:
        await m.reply_text(f"Rename error: {e}")
    finally:
        # Cancel event cleanup handled in upload task
        pass

@app.on_callback_query(filters.regex("cancel_task"))
async def cancel_task_cb(c, cb):
    uid = cb.from_user.id
    prompt_message_id = cb.message.id

    if prompt_message_id in PENDING_AUDIO_ORDERS:
        file_data = PENDING_AUDIO_ORDERS.pop(prompt_message_id)
        if file_data['uid'] == uid:
            try:
                Path(file_data['path']).unlink(missing_ok=True)
            except Exception:
                pass
            
            # Find and set specific events if possible, but for simplicity we trigger user events
            for ev in list(TASKS.get(uid, [])):
                try: ev.set()
                except: pass

            await cb.answer("Audio change process cancelled.", show_alert=True)
            try:
                await cb.message.delete()
            except Exception:
                pass
            return
    
    # Trigger cancellation for tasks
    if uid in TASKS and TASKS[uid]:
        count = 0
        for ev in list(TASKS[uid]):
            try:
                ev.set()
                count += 1
            except:
                pass
        
        await cb.answer(f"{count} operation(s) cancelled.", show_alert=True)
        try:
            await cb.message.delete()
        except Exception:
            pass
    else:
        await cb.answer("No operations are running.", show_alert=True)

async def generate_video_thumbnail(video_path: Path, thumb_path: Path, timestamp_sec: int = 1):
    try:
        cmd = [
            "ffmpeg",
            "-y",
            "-i", str(video_path),
            "-ss", str(timestamp_sec),
            "-vframes", "1",
            "-vf", "scale=320:-1",
            str(thumb_path)
        ]
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
        return thumb_path.exists() and thumb_path.stat().st_size > 0
    except Exception as e:
        logger.warning("Thumbnail generate error: %s", e)
        return False


def process_dynamic_caption(uid, caption_template):
    if uid not in USER_COUNTERS:
        USER_COUNTERS[uid] = {'uploads': 0, 'episode_numbers': {}, 'dynamic_counters': {}, 're_options_count': 0}

    USER_COUNTERS[uid]['uploads'] += 1

    quality_match = re.search(r"\[re\s*\((.*?)\)\]", caption_template)
    if quality_match:
        options_str = quality_match.group(1)
        options = [opt.strip() for opt in options_str.split(',')]
        
        if not USER_COUNTERS[uid]['re_options_count']:
            USER_COUNTERS[uid]['re_options_count'] = len(options)
        
        current_index = (USER_COUNTERS[uid]['uploads'] - 1) % len(options)
        current_quality = options[current_index]
        
        caption_template = caption_template.replace(quality_match.group(0), current_quality)

        if (USER_COUNTERS[uid]['uploads'] - 1) % USER_COUNTERS[uid]['re_options_count'] == 0 and USER_COUNTERS[uid]['uploads'] > 1:
            for key in USER_COUNTERS[uid]['dynamic_counters']:
                USER_COUNTERS[uid]['dynamic_counters'][key]['value'] += 1
    elif USER_COUNTERS[uid]['uploads'] > 1: 
        for key in USER_COUNTERS[uid].get('dynamic_counters', {}):
             USER_COUNTERS[uid]['dynamic_counters'][key]['value'] += 1


    counter_matches = re.findall(r"\[\s*(\(?\d+\)?)\s*\]", caption_template)
    
    if USER_COUNTERS[uid]['uploads'] == 1:
        for match in counter_matches:
            has_paren = match.startswith('(') and match.endswith(')')
            clean_match = re.sub(r'[()]', '', match)
            USER_COUNTERS[uid]['dynamic_counters'][match] = {'value': int(clean_match), 'has_paren': has_paren}
    
    for match, data in USER_COUNTERS[uid]['dynamic_counters'].items():
        value = data['value']
        has_paren = data['has_paren']
        
        original_num_len = len(re.sub(r'[()]', '', match))
        formatted_value = f"{value:0{original_num_len}d}"

        final_value = f"({formatted_value})" if has_paren else formatted_value
        
        caption_template = re.sub(re.escape(f"[{match}]"), final_value, caption_template)


    current_episode_num = 0
    if USER_COUNTERS[uid].get('dynamic_counters'):
        current_episode_num = min(data['value'] for data in USER_COUNTERS[uid]['dynamic_counters'].values())

    conditional_matches = re.findall(r"\[([a-zA-Z0-9\s]+)\s*\((.*?)\)\]", caption_template)

    for match in conditional_matches:
        text_to_add = match[0].strip() 
        target_num_str = re.sub(r'[^0-9]', '', match[1]).strip() 

        placeholder = re.escape(f"[{match[0].strip()} ({match[1].strip()})]")
        
        try:
            target_num = int(target_num_str)
        except ValueError:
            caption_template = re.sub(placeholder, "", caption_template)
            continue
        
        if current_episode_num == target_num:
            caption_template = re.sub(placeholder, text_to_add, caption_template)
        else:
            caption_template = re.sub(placeholder, "", caption_template)

    return "**" + "\n".join(caption_template.splitlines()) + "**"


async def recursive_split_video(input_path: Path, target_name_stem: str, target_name_ext: str, duration: float, uid: int, cancel_event) -> list:
    MAX_FILE_SIZE = 1.95 * 1024 * 1024 * 1024 # Safe margin under 2GB
    if not input_path.exists():
        return []
    
    if input_path.stat().st_size <= MAX_FILE_SIZE or duration <= 0:
        return [(input_path, duration)]
        
    num_parts = math.ceil(input_path.stat().st_size / MAX_FILE_SIZE)
    base_chunk = duration / num_parts
    
    parts = []
    for i in range(num_parts):
        s_time = i * base_chunk
        e_time = (i + 1) * base_chunk
        
        if i > 0:
            s_time -= 5 # overlap
        if i < num_parts - 1:
            e_time += 5 # overlap
            
        s_time = max(0, s_time)
        e_time = min(duration, e_time)
        part_duration = e_time - s_time
        
        part_path = TMP / f"split_{uid}_{int(datetime.now().timestamp())}_{i}_{input_path.name}"
        
        cmd = [
            "ffmpeg",
            "-y",
            "-i", str(input_path),
            "-ss", str(s_time),
            "-to", str(e_time),
            "-c", "copy",
            str(part_path)
        ]
        
        if cancel_event.is_set(): raise Exception("Cancelled")
        await asyncio.to_thread(subprocess.run, cmd, capture_output=True, text=True, check=False)
        
        if part_path.exists() and part_path.stat().st_size > 0:
            if part_path.stat().st_size > MAX_FILE_SIZE:
                # Recursively split again if the resulting part is still over 1.95 GB
                sub_parts = await recursive_split_video(part_path, target_name_stem, target_name_ext, part_duration, uid, cancel_event)
                parts.extend(sub_parts)
                try: part_path.unlink() # Cleanup intermediate
                except: pass
            else:
                parts.append((part_path, part_duration))
    return parts

async def process_file_and_upload(c: Client, m: Message, in_path: Path, original_name: str = None, messages_to_delete: list = None, cancel_event_passed: asyncio.Event = None, custom_caption_override: str = None):
    uid = m.from_user.id
    # Use passed cancel event or create new one (though logically should be passed)
    cancel_event = cancel_event_passed
    if not cancel_event:
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
    
    upload_path = in_path
    temp_thumb_path = None
    final_caption_template = USER_CAPTIONS.get(uid)
    status_msg = None 
    parts_to_upload = []

    try:
        # Check cancel early
        if cancel_event.is_set():
             raise Exception("Cancelled")

        input_name = in_path.name
        target_name = original_name or input_name
        
        video_exts = {".mp4", ".mkv", ".avi", ".mov", ".flv", ".wmv", ".webm"}
        audio_exts = {".mp3", ".m4a", ".flac", ".wav", ".aac"}
        
        is_video_file = bool(m.video) or any(input_name.lower().endswith(ext) for ext in video_exts)
        is_audio_file = any(input_name.lower().endswith(ext) for ext in audio_exts)
        
        if is_video_file:
            # Check conditions
            is_mp4_container = input_name.lower().endswith(".mp4")
            is_mkv_container = input_name.lower().endswith(".mkv")
            has_opus = has_opus_audio(in_path)
            
            # Determine final extension
            if is_mp4_container:
                if has_opus:
                    final_ext = ".mkv" # MP4 + OPUS -> MKV
                else:
                    final_ext = ".mp4" # MP4 (No OPUS) -> MP4
            elif is_mkv_container:
                final_ext = ".mkv" # MKV -> MKV
            else:
                final_ext = ".mkv" # Others -> MKV
            
            # Adjust target_name extension
            target_stem = Path(target_name).stem
            target_name = target_stem + final_ext
            
            # Prepare for processing
            processed_path = TMP / f"proc_{uid}_{int(datetime.now().timestamp())}_{target_name}"
            
            try:
                status_text = "Processing video (Metadata & Format Check)..."
                if messages_to_delete:
                     # Try to edit existing msg if possible, but msg object not passed here, just ID
                     pass 
                status_msg = await m.reply_text(status_text, reply_markup=progress_keyboard())
            except Exception:
                status_msg = await m.reply_text(status_text, reply_markup=progress_keyboard())
            
            if messages_to_delete:
                messages_to_delete.append(status_msg.id)
            else:
                messages_to_delete = [status_msg.id]

            # --- FFmpeg Command for Processing ---
            cmd = [
                "ffmpeg",
                "-i", str(in_path),
                "-map", "0", # Copy all streams
                "-c", "copy", # Copy codec (fast)
                "-metadata:s:a", "title=[@TA_HD_Anime] Telegram Channel", # Set audio title
                "-metadata", "handler_name=",
                str(processed_path)
            ]
            
            if cancel_event.is_set(): raise Exception("Cancelled")
            
            result = await asyncio.to_thread(subprocess.run, cmd, capture_output=True, text=True, check=False, timeout=3600)
            
            if result.returncode == 0 and processed_path.exists() and processed_path.stat().st_size > 0:
                upload_path = processed_path
            else:
                logger.warning(f"Processing failed: {result.stderr}. Uploading original.")
                pass

        if is_video_file:
            thumb_path = USER_THUMBS.get(uid)
            if not thumb_path:
                temp_thumb_path = TMP / f"thumb_{uid}_{int(datetime.now().timestamp())}.jpg"
                thumb_time_sec = USER_THUMB_TIME.get(uid, 1) 
                ok = await generate_video_thumbnail(upload_path, temp_thumb_path, timestamp_sec=thumb_time_sec)
                if ok:
                    thumb_path = str(temp_thumb_path)

        try:
            if status_msg:
                await status_msg.edit("Starting upload...", reply_markup=progress_keyboard())
            else:
                status_msg = await m.reply_text("Starting upload...", reply_markup=progress_keyboard())
        except Exception:
             status_msg = await m.reply_text("Starting upload...", reply_markup=progress_keyboard())
             
        if messages_to_delete:
            if status_msg.id not in messages_to_delete:
                messages_to_delete.append(status_msg.id)
        else:
            messages_to_delete = [status_msg.id]

        if cancel_event.is_set():
            raise Exception("Cancelled")
        
        video_metadata = get_video_metadata(upload_path) if (is_video_file and upload_path.exists()) else {'duration': 0, 'width': 0, 'height': 0}
        duration_sec = video_metadata.get('duration', 0)
        width_px = video_metadata.get('width', 0)
        height_px = video_metadata.get('height', 0)
        
        # --- NEW CAPTION OVERRIDE LOGIC ---
        caption_to_use = f"**{target_name}**" # Default to Bold Filename
        if final_caption_template:
            caption_to_use = process_dynamic_caption(uid, final_caption_template)
        elif custom_caption_override:
            caption_to_use = custom_caption_override
        # ----------------------------------

        parts_to_upload = [(upload_path, target_name, None, duration_sec)]
        
        # --- SPLIT LOGIC IF GREATER THAN 2GB ---
        MAX_FILE_SIZE = 1.95 * 1024 * 1024 * 1024
        if is_video_file and upload_path.exists() and upload_path.stat().st_size > MAX_FILE_SIZE and duration_sec > 0:
            try:
                if status_msg:
                    await status_msg.edit("Video is over 2GB, splitting video recursively...", reply_markup=progress_keyboard())
            except Exception: pass
            
            target_stem = Path(target_name).stem
            target_ext = Path(target_name).suffix
            
            raw_parts = await recursive_split_video(upload_path, target_stem, target_ext, duration_sec, uid, cancel_event)
            
            split_parts = []
            for i, (p_path, p_dur) in enumerate(raw_parts):
                part_target_name = f"{target_stem} - Part {i+1:02d}{target_ext}"
                split_parts.append((p_path, part_target_name, i+1, p_dur))
                
            if split_parts:
                parts_to_upload = split_parts
        # ---------------------------------------

        last_exc = None
        for current_upload_path, current_target_name, part_num, current_duration in parts_to_upload:
            if cancel_event.is_set(): raise Exception("Cancelled")
            
            part_caption = caption_to_use
            if part_num is not None:
                if part_caption.endswith("**"):
                    part_caption = part_caption[:-2] + f"\n✔️ Part - {part_num:02d}**"
                else:
                    part_caption += f"\n✔️ Part - {part_num:02d}"
            
            try:
                if status_msg:
                    action_text = f"Starting upload... {'(Part ' + str(part_num) + ')' if part_num else ''}"
                    await status_msg.edit(action_text, reply_markup=progress_keyboard())
            except Exception: pass
            
            upload_attempts = 3
            part_success = False
            for attempt in range(1, upload_attempts + 1):
                try:
                    if cancel_event.is_set(): raise Exception("Cancelled")

                    start_t = time.time()
                    async def ul_prog(current, total):
                        if cancel_event.is_set():
                            c.stop_transmission()
                        action_text = f"Uploading... {'(Part ' + str(part_num) + ')' if part_num else ''}"
                        if status_msg:
                            await progress_callback(current, total, action_text, status_msg, start_t)

                    if is_video_file:
                        await c.send_video(
                            chat_id=m.chat.id,
                            video=str(current_upload_path),
                            caption=part_caption,
                            thumb=thumb_path,
                            duration=int(current_duration),
                            width=width_px,
                            height=height_px,
                            supports_streaming=True,
                            file_name=current_target_name, 
                            parse_mode=ParseMode.MARKDOWN,
                            progress=ul_prog
                        )
                    elif is_audio_file:
                         await c.send_audio(
                            chat_id=m.chat.id,
                            audio=str(current_upload_path),
                            file_name=current_target_name,
                            caption=part_caption,
                            parse_mode=ParseMode.MARKDOWN,
                            progress=ul_prog
                        )
                    else:
                        await c.send_document(
                            chat_id=m.chat.id,
                            document=str(current_upload_path),
                            file_name=current_target_name,
                            caption=part_caption,
                            parse_mode=ParseMode.MARKDOWN,
                            progress=ul_prog
                        )
                    
                    part_success = True
                    last_exc = None
                    break
                except Exception as e:
                    last_exc = e
                    if "Cancelled" in str(e):
                        break
                    logger.warning("Upload attempt %s failed for part %s: %s", attempt, part_num, e)
                    await asyncio.sleep(2 * attempt)
            
            if not part_success:
                break 

        if not last_exc:
            if messages_to_delete:
                try:
                    await c.delete_messages(chat_id=m.chat.id, message_ids=messages_to_delete)
                except Exception:
                    pass
        
        if last_exc:
            msg_text = "Operation cancelled by user." if "Cancelled" in str(last_exc) else f"Upload failed: {last_exc}"
            if status_msg:
                await status_msg.edit(msg_text, reply_markup=None)
            else:
                await m.reply_text(msg_text, reply_markup=None)

    except Exception as e:
        msg_text = "Operation cancelled by user." if "Cancelled" in str(e) else f"Upload error: {e}"
        if status_msg:
            await status_msg.edit(msg_text)
        else:
            await m.reply_text(msg_text)
    finally:
        try:
            if upload_path != in_path and upload_path.exists():
                upload_path.unlink()
            if in_path.exists():
                in_path.unlink()
            if temp_thumb_path and Path(temp_thumb_path).exists():
                Path(temp_thumb_path).unlink()
            
            # Clean up split parts
            for p_path, _, p_num, _ in parts_to_upload:
                 if p_num is not None and p_path.exists():
                      p_path.unlink()
                      
            TASKS[uid].remove(cancel_event)
        except Exception:
            pass

@app.on_message(filters.command("broadcast") & filters.private)
async def broadcast_cmd_no_reply(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    if not m.reply_to_message:
        await m.reply_text("To broadcast, **reply** to any message (image, video, or text) with this command.")
        return

@app.on_message(filters.command("broadcast") & filters.private & filters.reply)
async def broadcast_cmd_reply(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    
    source_message = m.reply_to_message
    if not source_message:
        await m.reply_text("To broadcast, reply to any message with this command.")
        return

    await m.reply_text(f"Broadcast starting to {len(SUBSCRIBERS)} subscribers...", quote=True)
    failed = 0
    sent = 0
    for chat_id in list(SUBSCRIBERS):
        if chat_id == m.chat.id:
            continue
        try:
            await c.forward_messages(chat_id=chat_id, from_chat_id=source_message.chat.id, message_ids=source_message.id)
            sent += 1
            await asyncio.sleep(0.08)
        except Exception as e:
            failed += 1
            logger.warning("Broadcast to %s failed: %s", chat_id, e)

    await m.reply_text(f"Broadcast complete. Sent: {sent}, Failed: {failed}")

@flask_app.route('/')
def home():
    html_content = """
    <!DOCTYPE-html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>Bot Status</title>
        <style>
            body {
                font-family: Arial, sans-serif;
                background-color: #f0f2f5;
                color: #333;
                text-align: center;
                padding-top: 50px;
            }
            .container {
                background-color: #fff;
                padding: 30px;
                border-radius: 10px;
                box-shadow: 0 4px 8px rgba(0,0,0,0.1);
                display: inline-block;
            }
            h1 {
                color: #28a745;
            }
        </style>
    </head>
    <body>
        <div class="container">
            <h1>TA File Share Bot is running! ✅</h1>
            <p>This page confirms that the bot's web server is active.</p>
        </div>
    </body>
    </html>
    """
    return render_template_string(html_content)

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

if __name__ == "__main__":
    print("Bot is starting... Starting Flask and Ping threads, then Pyrogram will start.")
    t = threading.Thread(target=run_flask_and_ping, daemon=True)
    t.start()
    try:
        loop = asyncio.get_event_loop()
        loop.create_task(periodic_cleanup())
    except RuntimeError:
        pass
    app.run()
