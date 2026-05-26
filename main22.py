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
import urllib.parse
import zipfile
import shutil
import socket
import tarfile

# Extended Archive Support
try:
    import rarfile
except ImportError:
    pass
try:
    import py7zr
except ImportError:
    pass
try:
    from pyunpack import Archive
except ImportError:
    pass
try:
    import patoolib
except ImportError:
    pass

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Environment Variables
API_ID = int(os.getenv("API_ID"))
API_HASH = os.getenv("API_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
PORT = int(os.getenv("PORT", "10000")) 
RENDER_EXTERNAL_HOSTNAME = os.getenv("RENDER_EXTERNAL_HOSTNAME")
COOKIES_TXT = os.getenv("COOKIES_TXT") 
ADMIN_ID = int(os.getenv("ADMIN_ID", "0"))

TMP = Path("tmp")
TMP.mkdir(parents=True, exist_ok=True)

# State Management
USER_THUMBS = {}
TASKS = {}
USER_TASK_EVENTS = {} 
SET_THUMB_REQUEST = set()
SET_CAPTION_REQUEST = set()
USER_CAPTIONS = {}
USER_COUNTERS = {}
EDIT_CAPTION_MODE = set()
USER_THUMB_TIME = {}
HIDE_PROGRESS_BAR = set()
USER_PROGRESS_INTERVAL = {} 

USER_QUEUE_PAUSED = set()
AUTO_UPLOAD_ALL = set()

MKV_AUDIO_CHANGE_MODE = set()
PENDING_AUDIO_ORDERS = {} 

BATCH_AUDIO_MODE = set()
BATCH_AUDIO_STATE = {}
BATCH_AUDIO_QUEUES = {}
BATCH_AUDIO_WORKERS = {}

CONVERT_MODE = set()
CONVERT_ZIP_MODE = set()
CONVERT_SESSIONS = {}
ACTIVE_CONVERT_SESSION = {} 
CONVERT_QUEUE = {} 
CONVERT_WORKERS = {}

CREATE_POST_MODE = set()
POST_CREATION_STATE = {} 

DEFAULT_POST_DATA = {
    'image_name': "Image Name",
    'genres': "",
    'season_list_raw': "1, 2" 
}

BATCH_CAPTION_MODE = set()  
BATCH_UPLOAD_MODE = set()
BATCH_DATA = {}            
BATCH_STATUS_MSG = {}      

USER_QUEUES = {}           
USER_WORKERS = {}          
USER_UPLOAD_LOCKS = {}     

MULTI_GROUP_BATCH_MODE = set()
MULTI_GROUP_DATA = {}
USE_ORIGINAL_CAPTION_IN_MULTI_GROUP = set()
MULTI_GROUP_DONE_MSG = {}

ZIP_DOWNLOAD_MODE = set()
ZIP_NAV_STATE = {}
ZIP_READY_LIST = {} 
ZIP_DL_QUEUES = {}  
ZIP_DL_WORKERS = {} 

NAV_PATHS = {} 

YT_SESSIONS = {}
YT_DLP_MODE = set()
SAVED_YT_QUALITIES = {}

MAX_SIZE = 1000 * 1024 * 1024 * 1024 

app = Client("mybot", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN, workers=1000, sleep_threshold=86400)
flask_app = Flask(__name__)

# ---- Utility Functions ----
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
    BASE_NEW_NAME = "[@TA_HD_Anime] Telegram Channel"
    file_path = Path(original_name)
    file_ext = file_path.suffix.lower()
    file_ext = "." + file_ext.lstrip('.')
    if not file_ext or file_ext == '.':
        return BASE_NEW_NAME + ".mp4"
    return BASE_NEW_NAME + file_ext

def get_video_metadata(file_path: Path) -> dict:
    data = {'duration': 0, 'width': 0, 'height': 0}
    try:
        cmd = ["ffprobe", "-v", "quiet", "-print_format", "json", "-show_streams", "-show_format", str(file_path)]
        result = subprocess.run(cmd, capture_output=True, text=True, check=True, timeout=60)
        metadata = json.loads(result.stdout)
        video_stream = next((s for s in metadata.get('streams', []) if s.get('codec_type') == 'video'), None)
        if video_stream:
            data['width'] = int(video_stream.get('width', 0))
            data['height'] = int(video_stream.get('height', 0))
        duration_str = metadata.get('format', {}).get('duration') or (video_stream.get('duration') if video_stream else None)
        if duration_str:
            data['duration'] = int(float(duration_str))
    except Exception as e:
        logger.warning(f"FFprobe failed: {e}. Falling back to Hachoir...")
        try:
            parser = createParser(str(file_path))
            if parser:
                with parser:
                    h_metadata = extractMetadata(parser)
                if h_metadata:
                    if h_metadata.has("duration"): data['duration'] = int(h_metadata.get("duration").total_seconds())
                    if h_metadata.has("width"): data['width'] = int(h_metadata.get("width"))
                    if h_metadata.has("height"): data['height'] = int(h_metadata.get("height"))
        except Exception as he:
            logger.error(f"Hachoir fallback failed: {he}")
    return data

def get_detailed_metadata(file_path: Path) -> dict:
    data = {'duration': 0, 'width': 0, 'height': 0, 'v_bitrate': 0, 'audio_streams': [], 'filesize': 0}
    try:
        data['filesize'] = os.path.getsize(file_path)
        cmd = ["ffprobe", "-v", "quiet", "-print_format", "json", "-show_format", "-show_streams", str(file_path)]
        result = subprocess.run(cmd, capture_output=True, text=True, check=True, timeout=60)
        metadata = json.loads(result.stdout)
        duration_str = metadata.get('format', {}).get('duration', '0')
        data['duration'] = float(duration_str) if duration_str else 0
        total_bitrate = float(metadata.get('format', {}).get('bitrate', 0))
        if total_bitrate == 0 and data['duration'] > 0:
            total_bitrate = (data['filesize'] * 8) / data['duration']
        for stream in metadata.get('streams', []):
            if stream.get('codec_type') == 'video':
                data['width'] = int(stream.get('width', 0))
                data['height'] = int(stream.get('height', 0))
                vb = stream.get('bit_rate')
                if vb: data['v_bitrate'] = int(float(vb))
            elif stream.get('codec_type') == 'audio':
                ab = stream.get('bit_rate')
                ab_val = int(float(ab)) if ab else 128000
                data['audio_streams'].append({
                    'index': stream.get('index'),
                    'codec': stream.get('codec_name'),
                    'bitrate': ab_val
                })
        if data['v_bitrate'] == 0 and total_bitrate > 0:
            audio_total = sum([a['bitrate'] for a in data['audio_streams']])
            data['v_bitrate'] = max(100000, int(total_bitrate - audio_total))
    except Exception as e:
        logger.error(f"Detailed FFprobe error: {e}")
    return data

def calculate_estimated_size(duration, v_bitrate_kbps, a_bitrate_kbps, num_audios):
    total_kbps = v_bitrate_kbps + (a_bitrate_kbps * num_audios)
    return (total_kbps * 1000 * duration) / 8

def format_duration(seconds):
    if not seconds or math.isnan(seconds): return "0s"
    seconds = int(seconds)
    h, m, s = seconds // 3600, (seconds % 3600) // 60, seconds % 60
    if h > 0: return f"{h}h {m}m {s}s"
    if m > 0: return f"{m}m {s}s"
    return f"{s}s"

def format_size(bytes_size):
    if not bytes_size or bytes_size == 0: return "N/A"
    size_name = ("B", "KB", "MB", "GB", "TB")
    i = int(math.floor(math.log(bytes_size, 1024)))
    p = math.pow(1024, i)
    s = round(bytes_size / p, 2)
    return f"{s} {size_name[i]}"

def make_progress_bar(percent):
    filled = int(percent / 5)
    return "█" * filled + "░" * (20 - filled)

PROGRESS_CACHE = {}

async def progress_callback(current, total, action, message, start_time, is_time_based=False, original_name=None):
    if message.chat.id in HIDE_PROGRESS_BAR: return
    if total == 0: return
    now = time.time()
    msg_id = message.id
    interval = USER_PROGRESS_INTERVAL.get(message.chat.id, 5)
    if msg_id in PROGRESS_CACHE and now - PROGRESS_CACHE[msg_id] < interval: return
    PROGRESS_CACHE[msg_id] = now
    percent = min((current / total) * 100, 100)
    elapsed = now - start_time
    speed = current / elapsed if elapsed > 0 else 0
    eta = (total - current) / speed if speed > 0 else 0
    
    if is_time_based:
        size_str = f"{format_duration(current)} / {format_duration(total)}"
        speed_str = f"{speed:.2f}x"
    else:
        size_str = f"{format_size(current)} / {format_size(total)}"
        speed_str = f"{format_size(speed)}/s"
        
    orig_name_str = f"**File:** `{original_name}`\n" if original_name else ""
    text = (
        f"**{action}**\n{orig_name_str}"
        f"`[{make_progress_bar(percent)}]` **{percent:.2f}%**\n"
        f"**Processed:** `{size_str}`\n**Speed:** `{speed_str}`\n"
        f"**Elapsed:** `{format_duration(elapsed)}` | **ETA:** `{format_duration(eta)}`"
    )
    try:
        await message.edit_text(text, reply_markup=progress_keyboard())
    except:
        pass

def progress_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("Refresh 🔄", callback_data="refresh_btn")],
        [InlineKeyboardButton("Cancel ❌", callback_data="cancel_single"),
         InlineKeyboardButton("All Cancel ❌", callback_data="cancel_all")]
    ])

def mode_check_keyboard(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"Convert Mode {'✅ ON' if uid in CONVERT_MODE else '❌ OFF'}", callback_data="toggle_convert_mode")],
        [InlineKeyboardButton(f"MKV Audio Mode {'✅ ON' if uid in MKV_AUDIO_CHANGE_MODE else '❌ OFF'}", callback_data="toggle_audio_mode")],
        [InlineKeyboardButton(f"Edit Caption Mode {'✅ ON' if uid in EDIT_CAPTION_MODE else '❌ OFF'}", callback_data="toggle_caption_mode")],
        [InlineKeyboardButton(f"YT-DLP Mode {'✅ ON' if uid in YT_DLP_MODE else '❌ OFF'}", callback_data="toggle_ytdlp_mode")],
        [InlineKeyboardButton(f"ZIP Mode {'✅ ON' if uid in ZIP_DOWNLOAD_MODE else '❌ OFF'}", callback_data="toggle_zip_mode")]
    ])

def process_dynamic_caption(uid, template, filename):
    if not template: return filename
    if uid not in USER_COUNTERS:
        USER_COUNTERS[uid] = {'uploads': 0}
    USER_COUNTERS[uid]['uploads'] += 1
    caption = template.replace("{filename}", filename)
    caption = caption.replace("{counter}", str(USER_COUNTERS[uid]['uploads']))
    return caption

def generate_post_caption(data: dict) -> str:
    image_name = data.get('image_name', DEFAULT_POST_DATA['image_name'])
    genres = data.get('genres', DEFAULT_POST_DATA['genres'])
    season_list_raw = data.get('season_list_raw', DEFAULT_POST_DATA['season_list_raw'])
    season_entries = []
    parts = [p.strip() for p in re.split(r'[,\s]+', season_list_raw.strip()) if p.strip()]
    for part in parts:
        if '-' in part:
            try:
                start, end = map(int, part.split('-'))
                if start > end: start, end = end, start
                for i in range(start, end + 1): season_entries.append(f"**{image_name} Season {i:02d}**")
            except: continue
        else:
            try:
                num = int(part)
                season_entries.append(f"**{image_name} Season {num:02d}**")
            except: continue
    unique_seasons = list(dict.fromkeys(season_entries))
    if not unique_seasons: unique_seasons.append("**Coming Soon...**")
    else: unique_seasons.append("**Coming Soon...**")
    season_text = "\n".join(unique_seasons)
    base_caption = (
        f"**{image_name}**\n**────────────────────**\n"
        f"**‣ Audio - Hindi Official**\n**‣ Quality - 480p, 720p, 1080p**\n"
        f"**‣ Genres - {genres}**\n**────────────────────**"
    )
    collapsible = [f"> **{image_name} All Season List :-**", "> "]
    for line in season_text.split('\n'):
        collapsible.append(f"> {line}")
        collapsible.append("> ")
    if collapsible[-1] == "> ": collapsible.pop()
    return f"{base_caption}\n\n" + "\n".join(collapsible)

async def generate_video_thumbnail(video_path: Path, thumb_path: Path, timestamp_sec: int = 1):
    try:
        cmd = ["ffmpeg", "-y", "-i", str(video_path), "-ss", str(timestamp_sec), "-vframes", "1", "-vf", "scale=320:-1", str(thumb_path)]
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
        return thumb_path.exists() and thumb_path.stat().st_size > 0
    except:
        return False

# ---- Core Core Processing & Upload Logic ----
async def process_file_and_upload(client, message, tmp_path, target_name, original_download_name=None, messages_to_delete=None, cancel_event_passed=None, passed_uid=None, default_caption=None, original_caption_passed=None):
    uid = passed_uid or message.from_user.id
    status_msg = await message.reply_text("Preparing upload metadata...")
    try:
        renamed_path = tmp_path.parent / target_name
        tmp_path.rename(renamed_path)
        metadata = get_video_metadata(renamed_path)
        
        # Thumbnail selection
        thumb = USER_THUMBS.get(uid)
        generated_thumb = False
        if not thumb and renamed_path.suffix.lower() in ['.mp4', '.mkv', '.webm']:
            thumb_p = TMP / f"thumb_{uid}_{int(time.time())}.jpg"
            if await generate_video_thumbnail(renamed_path, thumb_p, timestamp_sec=2):
                thumb = str(thumb_p)
                generated_thumb = True

        # Caption configuration
        if uid in USER_CAPTIONS:
            caption = process_dynamic_caption(uid, USER_CAPTIONS[uid], target_name)
        else:
            caption = original_caption_passed or default_caption or target_name

        start_t = time.time()
        async def up_prog(current, total):
            if cancel_event_passed and cancel_event_passed.is_set():
                client.stop_transmission()
            await progress_callback(current, total, "Uploading to Telegram...", status_msg, start_t, original_name=target_name)

        if renamed_path.suffix.lower() in ['.mp4', '.mkv'] and metadata['duration'] > 0:
            await client.send_video(
                chat_id=message.chat.id, video=str(renamed_path), caption=caption,
                duration=metadata['duration'], width=metadata['width'], height=metadata['height'],
                thumb=thumb, progress=up_prog
            )
        else:
            await client.send_document(chat_id=message.chat.id, document=str(renamed_path), caption=caption, thumb=thumb, progress=up_prog)

        await status_msg.delete()
        if generated_thumb and thumb and os.path.exists(thumb): os.unlink(thumb)
        if renamed_path.exists(): renamed_path.unlink()
    except Exception as e:
        logger.error(f"Upload Error: {e}")
        await status_msg.edit(f"❌ Upload Failed: {e}")
    finally:
        if messages_to_delete:
            for mid in messages_to_delete:
                try: await client.delete_messages(message.chat.id, mid)
                except: pass

async def get_filename_from_url(url):
    try:
        connector = aiohttp.TCPConnector(limit=0, family=socket.AF_INET, use_dns_cache=True)
        async with aiohttp.ClientSession(connector=connector) as sess:
            async with sess.head(url, allow_redirects=True, timeout=10) as resp:
                cd = resp.headers.get('Content-Disposition')
                if cd:
                    fname_match = re.findall(r'filename\*?=(?:UTF-8\'\')?["\']?([^"\';\n]+)', cd, re.IGNORECASE)
                    if fname_match: return urllib.parse.unquote(fname_match[0])
    except: pass
    fname = urllib.parse.unquote(url.split("/")[-1].split("?")[0])
    return fname if fname else "file.mp4"

async def download_stream(resp, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    total = out_path.stat().st_size if out_path.exists() else 0
    try: size = int(resp.headers.get("Content-Length", 0)) + total
    except: size = 0
    start_t = time.time()
    mode = "ab" if total > 0 else "wb"
    with out_path.open(mode) as f:
        async for chunk in resp.content.iter_chunked(1024*1024):
            if cancel_event and cancel_event.is_set(): return False, "Cancelled"
            if not chunk: break
            total += len(chunk)
            f.write(chunk)
            if message and size > 0:
                await progress_callback(total, size, "Downloading URL...", message, start_t, original_name=original_name)
    return True, None

async def download_url_generic(url: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    headers = {"User-Agent": "Mozilla/5.0"}
    if out_path.exists(): headers["Range"] = f"bytes={out_path.stat().st_size}-"
    connector = aiohttp.TCPConnector(family=socket.AF_INET, use_dns_cache=True)
    async with aiohttp.ClientSession(connector=connector) as sess:
        async with sess.get(url, headers=headers, allow_redirects=True) as resp:
            if resp.status in [200, 206]: return await download_stream(resp, out_path, message, cancel_event, original_name)
            return False, f"HTTP Error {resp.status}"

async def download_drive_file(file_id: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    url = f"https://drive.google.com/uc?export=download&id={file_id}"
    connector = aiohttp.TCPConnector(family=socket.AF_INET, use_dns_cache=True)
    async with aiohttp.ClientSession(connector=connector) as sess:
        async with sess.get(url, allow_redirects=True) as resp:
            if resp.status in [200, 206]: return await download_stream(resp, out_path, message, cancel_event, original_name)
    return False, "Google Drive Download Error"

async def download_and_process_generic(client, m, url, status_msg, cancel_event):
    uid = m.from_user.id
    orig_name = await get_filename_from_url(url)
    tmp_path = TMP / f"dl_{uid}_{int(time.time())}_{orig_name}"
    status = await status_msg.edit(f"Downloading: `{orig_name}`", reply_markup=progress_keyboard())
    
    if is_drive_url(url):
        drive_id = extract_drive_id(url)
        ok, err = await download_drive_file(drive_id, tmp_path, status, cancel_event, orig_name)
    else:
        ok, err = await download_url_generic(url, tmp_path, status, cancel_event, orig_name)
        
    if ok:
        target_name = generate_new_filename(orig_name)
        asyncio.create_task(sequential_upload_task(uid, client, m, tmp_path, target_name, status.id, cancel_event, default_caption=orig_name))
    else:
        await status.edit(f"❌ Download Failed: {err}")

async def sequential_upload_task(uid, client, message, tmp_path, renamed_file, status_msg_id, cancel_event, default_caption=None):
    if uid not in USER_UPLOAD_LOCKS: USER_UPLOAD_LOCKS[uid] = asyncio.Lock()
    async with USER_UPLOAD_LOCKS[uid]:
        if cancel_event.is_set():
            if tmp_path.exists(): tmp_path.unlink()
            return
        await process_file_and_upload(client, message, tmp_path, target_name=renamed_file, messages_to_delete=[status_msg_id] if status_msg_id else [], cancel_event_passed=cancel_event, passed_uid=uid, default_caption=default_caption)

# ---- Queue Handler Worker Engine ----
async def process_queue_handler(uid, client):
    queue = USER_QUEUES[uid]
    while not queue.empty():
        while uid in USER_QUEUE_PAUSED: await asyncio.sleep(1)
        task_data = await queue.get()
        m = task_data.get('message')
        original_name = task_data.get('original_name')
        status_msg = task_data.get('status_msg')
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        if status_msg: USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
        
        try:
            if task_data.get('is_yt_dlp'):
                # YT-DLP Core Processing Logic
                url, fmt, title, res = task_data['url'], task_data['fmt'], task_data['title'], task_data.get('res', 'Best')
                out_tmpl = str(TMP / f"yt_{uid}_{int(time.time())}_{res}p_video.%(ext)s")
                ydl_opts = {'format': fmt, 'outtmpl': out_tmpl, 'quiet': True, 'merge_output_format': 'mkv'}
                if COOKIES_TXT and os.path.exists(COOKIES_TXT): ydl_opts['cookiefile'] = COOKIES_TXT
                
                def run_ydl():
                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        info = ydl.extract_info(url, download=True)
                        return ydl.prepare_filename(info)
                        
                downloaded_file = await asyncio.to_thread(run_ydl)
                actual_path = Path(downloaded_file)
                renamed_name = generate_new_filename(title)
                asyncio.create_task(sequential_upload_task(uid, client, m, actual_path, renamed_name, status_msg.id if status_msg else None, cancel_event, default_caption=title))
            elif task_data.get('is_url'):
                await download_and_process_generic(client, m, task_data['url'], status_msg, cancel_event)
            else:
                tmp_path = TMP / f"file_{uid}_{int(time.time())}_{original_name}"
                start_t = time.time()
                async def dl_p(c, t):
                    if cancel_event.is_set(): client.stop_transmission()
                    await progress_callback(c, t, "Downloading Telegram File...", status_msg, start_t, original_name=original_name)
                await m.download(file_name=str(tmp_path), progress=dl_p)
                renamed_name = generate_new_filename(original_name)
                asyncio.create_task(sequential_upload_task(uid, client, m, tmp_path, renamed_name, status_msg.id if status_msg else None, cancel_event, default_caption=original_name))
        except Exception as e:
            logger.error(f"Worker Task processing failed: {e}")
            if status_msg: await status_msg.edit(f"⚠️ Task Error: {e}")
        finally:
            queue.task_done()
    del USER_WORKERS[uid]

async def add_to_queue(uid, c, m, original_name, is_url=False, url=None, is_yt_dlp=False, fmt=None, title=None, res=None):
    if uid not in USER_QUEUES: USER_QUEUES[uid] = asyncio.Queue()
    status_msg = await m.reply_text(f"Added to queue: `{original_name or title}`")
    await USER_QUEUES[uid].put({
        'message': m, 'original_name': original_name, 'status_msg': status_msg,
        'is_url': is_url, 'url': url, 'is_yt_dlp': is_yt_dlp, 'fmt': fmt, 'title': title, 'res': res
    })
    if uid not in USER_WORKERS or USER_WORKERS[uid].done():
        USER_WORKERS[uid] = asyncio.create_task(process_queue_handler(uid, c))

# ---- Bot Command Telegram Event Handlers ----
@app.on_message(filters.command("start") & filters.private)
async def start_handler(c, m: Message):
    await m.reply_text(
        "👋 Welcome! Media Uploader & Converter Robot.\n\n"
        "**Available Commands:**\n"
        "/zip_file_download - Toggle ZIP Downloader Mode\n"
        "/yt_dlp - Toggle global YouTube Downloader mode\n"
        "/convert - Toggle Audio/Video Encoding Engine\n"
        "/setthumb - Set a persistent unique thumbnail\n"
        "/set_caption - Setup dynamic custom caption block\n"
        "/create_post - Open advanced interactive channel post editor\n"
        "/mode_check - Look up all configuration and active states\n"
        "/continue - Resume engine workers operations\n"
        "/restart - View storage configuration and wipe tracking registers"
    )

@app.on_message(filters.command("mode_check") & filters.private)
async def status_check(c, m: Message):
    if not is_admin(m.from_user.id): return
    await m.reply_text("🎛 **Current Engine Configuration Modes System Status Registers:**", reply_markup=mode_check_keyboard(m.from_user.id))

@app.on_message(filters.command("setthumb") & filters.private)
async def set_thumbnail_trigger(c, m: Message):
    if not is_admin(m.from_user.id): return
    SET_THUMB_REQUEST.add(m.from_user.id)
    await m.reply_text("📸 Send the picture file you want to use as custom thumbnail layout wrapper.")

@app.on_message(filters.command("set_caption") & filters.private)
async def set_caption_trigger(c, m: Message):
    if not is_admin(m.from_user.id): return
    SET_CAPTION_REQUEST.add(m.from_user.id)
    await m.reply_text("📝 Send text string template format layout profile.\nPlaceholders: `{filename}`, `{counter}`")

@app.on_message(filters.command("create_post") & filters.private)
async def create_post_trigger(c, m: Message):
    if not is_admin(m.from_user.id): return
    CREATE_POST_MODE.add(m.from_user.id)
    POST_CREATION_STATE[m.from_user.id] = {}
    await m.reply_text("🎬 [Step 1/3]: Enter the Name or Title for the Post Builder Interface.")

@app.on_message(filters.command("yt_dlp") & filters.private)
async def toggle_yt_dlp_mode(c, m: Message):
    if not is_admin(m.from_user.id): return
    uid = m.from_user.id
    if uid in YT_DLP_MODE:
        YT_DLP_MODE.discard(uid)
        await m.reply_text("❌ YT-DLP Streaming mode disabled.")
    else:
        YT_DLP_MODE.add(uid)
        await m.reply_text("✅ YT-DLP Streaming mode active.")

@app.on_message(filters.command("convert") & filters.private)
async def toggle_convert_mode_cmd(c, m: Message):
    if not is_admin(m.from_user.id): return
    uid = m.from_user.id
    if uid in CONVERT_MODE:
        CONVERT_MODE.discard(uid)
        await m.reply_text("❌ FFMPEG Audio/Video Transcoder processing mode disabled.")
    else:
        CONVERT_MODE.add(uid)
        await m.reply_text("✅ FFMPEG Audio/Video Transcoder processing mode active.")

@app.on_message(filters.command("zip_file_download") & filters.private)
async def toggle_zip_download_mode(c, m: Message):
    if not is_admin(m.from_user.id): return
    uid = m.from_user.id
    if uid in ZIP_DOWNLOAD_MODE:
        ZIP_DOWNLOAD_MODE.discard(uid)
        await m.reply_text("❌ Archive extraction mode disabled.")
    else:
        ZIP_DOWNLOAD_MODE.add(uid)
        await m.reply_text("✅ Archive extraction mode active.")

@app.on_message(filters.command("restart") & filters.private)
async def storage_reset_handler(c, m: Message):
    if not is_admin(m.from_user.id): return
    total, used, free = shutil.disk_usage("/")
    text = (
        f"📊 **System Storage Architecture Allocations:**\n\n"
        f"• Total Capacity: `{format_size(total)}`\n"
        f"• Used Space: `{format_size(used)}`\n"
        f"• Free Available: `{format_size(free)}`"
    )
    markup = InlineKeyboardMarkup([[InlineKeyboardButton("Clear Cache Directory Data 🗑", callback_data="clear_tmp_data")]])
    await m.reply_text(text, reply_markup=markup)

# ---- Callback Inline Interaction Route Handlers ----
@app.on_callback_query()
async def global_callback_router(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    data = cb.data
    
    if data == "clear_tmp_data":
        shutil.rmtree(TMP, ignore_errors=True)
        TMP.mkdir(parents=True, exist_ok=True)
        await cb.answer("Cache wiped successfully!", show_alert=True)
        await cb.message.edit_text("🗑 Cache and system working directory formatted.")
        
    elif data.startswith("toggle_"):
        mode = data.split("_")[1]
        if mode == "convert":
            CONVERT_MODE.symmetric_difference_update([uid])
        elif mode == "audio":
            MKV_AUDIO_CHANGE_MODE.symmetric_difference_update([uid])
        elif mode == "caption":
            EDIT_CAPTION_MODE.symmetric_difference_update([uid])
        elif mode == "ytdlp":
            YT_DLP_MODE.symmetric_difference_update([uid])
        elif mode == "zip":
            ZIP_DOWNLOAD_MODE.symmetric_difference_update([uid])
        await cb.message.edit_reply_markup(mode_check_keyboard(uid))
        await cb.answer("Configuration updated.")
        
    elif data == "refresh_btn":
        await cb.answer("Refreshed! Progress statistics updated.", show_alert=False)
        
    elif data == "cancel_single":
        if uid in USER_TASK_EVENTS:
            for ev in USER_TASK_EVENTS[uid].values(): ev.set()
        await cb.answer("Operation cancellation signal broad-casted.", show_alert=True)
        try: await cb.message.delete()
        except: pass
        
    elif data == "cancel_all":
        if uid in USER_QUEUES:
            while not USER_QUEUES[uid].empty(): USER_QUEUES[uid].get_nowait()
        if uid in USER_TASK_EVENTS:
            for ev in USER_TASK_EVENTS[uid].values(): ev.set()
        await cb.answer("Entire systemic user worker context engine pipelines cancelled.", show_alert=True)
        try: await cb.message.delete()
        except: pass

# ---- Message Fallback Processing Catch-All Routes ----
@app.on_message(filters.private & (filters.document | filters.video | filters.audio | filters.photo | filters.text))
async def primary_incoming_message_dispatcher(c: Client, m: Message):
    uid = m.from_user.id
    if not is_admin(uid): return

    # Custom Thumbnail setup logic
    if uid in SET_THUMB_REQUEST:
        SET_THUMB_REQUEST.discard(uid)
        if m.photo:
            path = await m.download(file_name=str(TMP / f"saved_thumb_{uid}.jpg"))
            USER_THUMBS[uid] = path
            await m.reply_text("✅ Persistent Custom Thumbnail profile applied.")
        else:
            await m.reply_text("❌ Attachment mismatch payload. Operation dropped.")
        return

    # Custom Caption setup logic
    if uid in SET_CAPTION_REQUEST:
        SET_CAPTION_REQUEST.discard(uid)
        if m.text:
            USER_CAPTIONS[uid] = m.text
            await m.reply_text(f"✅ Layout template saved:\n`{m.text}`")
        return

    # Advanced Channel Post Builder logic step loop
    if uid in CREATE_POST_MODE:
        state = POST_CREATION_STATE[uid]
        if 'image_name' not in state:
            state['image_name'] = m.text
            await m.reply_text("🎭 [Step 2/3]: Provide Genres criteria attributes identifiers.")
        elif 'genres' not in state:
            state['genres'] = m.text
            await m.reply_text("📅 [Step 3/3]: Provide active seasons intervals array set string (e.g., `1-3, 5`).")
        elif 'season_list_raw' not in state:
            state['season_list_raw'] = m.text
            CREATE_POST_MODE.discard(uid)
            caption = generate_post_caption(state)
            await m.reply_text(f"📋 **Generated Channel Formatted Post Output:**\n\n{caption}")
            POST_CREATION_STATE.pop(uid, None)
        return

    # File or URL download processing queue setup dispatchers logic block
    if m.text:
        url = m.text.strip()
        if url.startswith("http://") or url.startswith("https://"):
            if uid in YT_DLP_MODE or is_youtube_url(url):
                # Handle via YT-DLP
                await add_to_queue(uid, c, m, original_name=None, is_url=True, url=url, is_yt_dlp=True, fmt="bestvideo+bestaudio/best", title="Streaming Video", res="Best")
            else:
                # Direct URL Processing File Queue Handler
                filename = await get_filename_from_url(url)
                await add_to_queue(uid, c, m, original_name=filename, is_url=True, url=url)
            return

    # Telegram native file documents attachments extraction processing loops
    file_obj = m.video or m.document or m.audio
    if file_obj:
        orig_name = getattr(file_obj, 'file_name', None) or "file.mp4"
        await add_to_queue(uid, c, m, original_name=orig_name)

# ---- Flask Background Ping Context Integration Routing Web Engine ----
@flask_app.route('/')
def home_index_ping():
    return render_template_string("<h1>Uploader Core Pipeline Active Processing Framework Online Matrix Stack</h1>")

def ping_service():
    if not RENDER_EXTERNAL_HOSTNAME: return
    url = f"http://{RENDER_EXTERNAL_HOSTNAME}"
    while True:
        try: requests.get(url, timeout=10)
        except: pass
        time.sleep(600)

def run_flask_web_server():
    flask_app.run(host="0.0.0.0", port=PORT, use_reloader=False)

async def periodic_cleanup_loop():
    while True:
        try:
            now = datetime.now()
            for p in TMP.iterdir():
                if p.is_file() and now - datetime.fromtimestamp(p.stat().st_mtime) > timedelta(days=2):
                    p.unlink()
        except: pass
        await asyncio.sleep(3600)

# ---- Application Entry Execution Point Setup Bootstrapping Main Engine Block ----
if __name__ == "__main__":
    logger.info("Initializing Core Client Application Module Stack Engines Framework...")
    threading.Thread(target=run_flask_web_server, daemon=True).start()
    threading.Thread(target=ping_service, daemon=True).start()
    
    loop = asyncio.get_event_loop()
    loop.create_task(periodic_cleanup_loop())
    
    app.run()
