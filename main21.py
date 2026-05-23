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

# For extended archive support (if available in environment)
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

# env
API_ID = int(os.getenv("API_ID"))
API_HASH = os.getenv("API_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
PORT = int(os.getenv("PORT", "10000")) 
RENDER_EXTERNAL_HOSTNAME = os.getenv("RENDER_EXTERNAL_HOSTNAME")
COOKIES_TXT = os.getenv("COOKIES_TXT") # Added for yt-dlp cookies

TMP = Path("tmp")
TMP.mkdir(parents=True, exist_ok=True)

# state
USER_THUMBS = {}
TASKS = {}
USER_TASK_EVENTS = {} # New: uid -> {msg_id: cancel_event} for specific task cancel
SET_THUMB_REQUEST = set()
SET_CAPTION_REQUEST = set()
USER_CAPTIONS = {}
USER_COUNTERS = {}
EDIT_CAPTION_MODE = set()
USER_THUMB_TIME = {}
HIDE_PROGRESS_BAR = set()
USER_PROGRESS_INTERVAL = {} # New: custom interval for progress bar

# --- NEW STATE FOR PAUSE/CONTINUE & AUTO ZIP ---
USER_QUEUE_PAUSED = set()
AUTO_UPLOAD_ALL = set()
# -----------------------------------------------

# --- STATE FOR AUDIO CHANGE ---
MKV_AUDIO_CHANGE_MODE = set()
PENDING_AUDIO_ORDERS = {} 
# ------------------------------

# --- NEW STATE FOR CONVERT MODE ---
CONVERT_MODE = set()
CONVERT_SESSIONS = {}
ACTIVE_CONVERT_SESSION = {} # New: track active session to receive custom bitrate via message
# ----------------------------------

# --- NEW STATE FOR AUDIO ADD MODE ---
AUDIO_ADD_MODE = set()
AUDIO_ADD_STATE = {}
AUDIO_ADD_QUEUES = {}
AUDIO_ADD_WORKERS = {}
# ------------------------------------

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

# --- NEW STATE FOR MULTI GROUP BATCH & CAPTION OVERRIDE & ZIP ---
MULTI_GROUP_BATCH_MODE = set()
MULTI_GROUP_DATA = {}
USE_ORIGINAL_CAPTION_IN_MULTI_GROUP = set()
MULTI_GROUP_DONE_MSG = {}

# --- NEW ZIP DOWNLOAD MODE STATE ---
ZIP_DOWNLOAD_MODE = set()
ZIP_NAV_STATE = {}
ZIP_READY_LIST = {} # New: uid -> list of extracted zip info for serial display
ZIP_DL_QUEUES = {}  # New: queue for serial zip downloading
ZIP_DL_WORKERS = {} # New: worker for serial zip downloading
# ------------------------------------------------

# --- NEW STATE FOR PATH NAVIGATOR ---
NAV_PATHS = {} # uid -> {"current": Path, "items": list, "selected_file": Path}
# ------------------------------------------------

# --- YT-DLP STATE & MODES ---
YT_SESSIONS = {}
YT_DLP_MODE = set()
SAVED_YT_QUALITIES = {}
# --------------------

ADMIN_ID = int(os.getenv("ADMIN_ID", ""))
MAX_SIZE = 1000 * 1024 * 1024 * 1024 # Increased to 1000GB

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

def get_detailed_metadata(file_path: Path) -> dict:
    """Extracts very detailed metadata for conversion purposes."""
    data = {'duration': 0, 'width': 0, 'height': 0, 'v_bitrate': 0, 'audio_streams': [], 'filesize': 0}
    try:
        data['filesize'] = os.path.getsize(file_path)
        cmd = [
            "ffprobe", "-v", "quiet", "-print_format", "json",
            "-show_format", "-show_streams", str(file_path)
        ]
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
                if vb:
                    data['v_bitrate'] = int(float(vb))
            elif stream.get('codec_type') == 'audio':
                ab = stream.get('bit_rate')
                ab_val = int(float(ab)) if ab else 128000
                data['audio_streams'].append({
                    'index': stream.get('index'),
                    'codec': stream.get('codec_name'),
                    'bitrate': ab_val
                })
                
        # Estimate video bitrate if missing
        if data['v_bitrate'] == 0 and total_bitrate > 0:
            audio_total = sum([a['bitrate'] for a in data['audio_streams']])
            data['v_bitrate'] = max(100000, int(total_bitrate - audio_total))
            
    except Exception as e:
        logger.error(f"Detailed FFprobe error: {e}")
    return data

def calculate_estimated_size(duration, v_bitrate_kbps, a_bitrate_kbps, num_audios):
    total_kbps = v_bitrate_kbps + (a_bitrate_kbps * num_audios)
    size_bytes = (total_kbps * 1000 * duration) / 8
    return size_bytes

def build_convert_ui(session_id):
    session = CONVERT_SESSIONS.get(session_id)
    if not session: return None, None
    
    meta = session['meta']
    configs = session['configs']
    
    v_kbps = session['curr_v_bitrate'] // 1000
    a_kbps = session['curr_a_bitrate'] // 1000
    res = session['curr_res']
    
    est_size = calculate_estimated_size(meta['duration'], v_kbps, a_kbps, len(meta['audio_streams']))
    
    orig_v_kbps = meta['v_bitrate'] // 1000
    
    text = (
        f"**🎥 Video Convert Options**\n\n"
        f"**File:** `{session['original_name']}`\n"
        f"**Original Size:** `{format_size(meta['filesize'])}`\n"
        f"**Original Video:** `{meta['width']}x{meta['height']} @ {orig_v_kbps} kbps`\n"
        f"**Audio Tracks:** `{len(meta['audio_streams'])}`\n\n"
        f"**--- Live Conversion Target ---**\n"
        f"**Target Quality:** `{res if res else 'Original'}p`\n"
        f"**Target Video Bitrate:** `{v_kbps} kbps`\n"
        f"**Target Audio Bitrate (All):** `{a_kbps} kbps`\n"
        f"**Estimated Size:** `{format_size(est_size)}`\n\n"
        f"*(Added to Queue: {len(configs)} conversions)*\n"
        f"*(You can also send a number like `200` to set video bitrate directly)*"
    )
    
    orig_h = meta['height']
    res_buttons = []
    if orig_h > 0:
        res_buttons.append(InlineKeyboardButton(f"✅ Orig" if res is None else "Orig", callback_data=f"cv_res_{session_id}_Orig"))
        for r in [2160, 1080, 720, 480, 360]:
            if orig_h >= r or orig_h >= (r-50): 
                res_buttons.append(InlineKeyboardButton(f"✅ {r}p" if res == r else f"{r}p", callback_data=f"cv_res_{session_id}_{r}"))
    
    keyboard = []
    if res_buttons:
        keyboard.append(res_buttons)
        
    keyboard.append([
        InlineKeyboardButton("➖ 100 kbps", callback_data=f"cv_vb_minus_{session_id}"),
        InlineKeyboardButton(f"🎬 Vid Bitrate: {v_kbps}k", callback_data="ignore"),
        InlineKeyboardButton("➕ 100 kbps", callback_data=f"cv_vb_plus_{session_id}")
    ])
    
    keyboard.append([
        InlineKeyboardButton("➖ 32 kbps", callback_data=f"cv_ab_minus_{session_id}"),
        InlineKeyboardButton(f"🎵 All Audio: {a_kbps}k", callback_data="ignore"),
        InlineKeyboardButton("➕ 32 kbps", callback_data=f"cv_ab_plus_{session_id}")
    ])
    
    orig_toggle_text = "✅ Original: Uploading" if session['upload_original'] else "❌ Original: Skipped"
    
    keyboard.append([
        InlineKeyboardButton(orig_toggle_text, callback_data=f"cv_orig_{session_id}")
    ])
    
    keyboard.append([
        InlineKeyboardButton("Next (Add ➕)", callback_data=f"cv_next_{session_id}"),
        InlineKeyboardButton("OK ✅", callback_data=f"cv_ok_{session_id}")
    ])
    keyboard.append([InlineKeyboardButton("Cancel ❌", callback_data="cancel_single")])
    
    return text, InlineKeyboardMarkup(keyboard)

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

def format_duration(seconds):
    if not seconds or math.isnan(seconds): return "0s"
    seconds = int(seconds)
    h = seconds // 3600
    m = (seconds % 3600) // 60
    s = seconds % 60
    if h > 0: return f"{h}h {m}m {s}s"
    if m > 0: return f"{m}m {s}s"
    return f"{s}s"

def progress_keyboard():
    # Included Refresh button as per requirement
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("Refresh 🔄", callback_data="refresh_btn")],
        [InlineKeyboardButton("Cancel ❌", callback_data="cancel_single"),
         InlineKeyboardButton("All Cancel ❌", callback_data="cancel_all")]
    ])

def delete_caption_keyboard():
    return InlineKeyboardMarkup([[InlineKeyboardButton("Delete Caption 🗑️", callback_data="delete_caption")]])

def mode_check_keyboard(uid: int) -> InlineKeyboardMarkup:
    audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
    caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
    yt_dlp_status = "✅ ON" if uid in YT_DLP_MODE else "❌ OFF"
    zip_status = "✅ ON" if uid in ZIP_DOWNLOAD_MODE else "❌ OFF"
    convert_status = "✅ ON" if uid in CONVERT_MODE else "❌ OFF"
    audio_add_status = "✅ ON" if uid in AUDIO_ADD_MODE else "❌ OFF"
    
    waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
    waiting_status = f" ({waiting_count} orders pending)" if waiting_count > 0 else ""
    
    keyboard = [
        [InlineKeyboardButton(f"Convert Mode {convert_status}", callback_data="toggle_convert_mode")],
        [InlineKeyboardButton(f"Audio Add Mode {audio_add_status}", callback_data="toggle_audio_add_mode")],
        [InlineKeyboardButton(f"MKV Audio Change Mode {audio_status}{waiting_status}", callback_data="toggle_audio_mode")],
        [InlineKeyboardButton(f"Edit Caption Mode {caption_status}", callback_data="toggle_caption_mode")],
        [InlineKeyboardButton(f"YT-DLP Mode {yt_dlp_status}", callback_data="toggle_ytdlp_mode")],
        [InlineKeyboardButton(f"ZIP Download Mode {zip_status}", callback_data="toggle_zip_mode")]
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

def format_size(bytes_size):
    if not bytes_size or bytes_size == 0:
        return "N/A"
    size_name = ("B", "KB", "MB", "GB", "TB")
    i = int(math.floor(math.log(bytes_size, 1024)))
    p = math.pow(1024, i)
    s = round(bytes_size / p, 2)
    return "%s %s" % (s, size_name[i])

def make_bold(text):
    """Utility to ensure text is bold formatted correctly"""
    if not text: return text
    text_str = str(text).strip()
    if not text_str.startswith("**"):
        text_str = f"**{text_str}"
    if not text_str.endswith("**"):
        text_str = f"{text_str}**"
    return text_str

PROGRESS_CACHE = {}

def make_progress_bar(percent):
    filled = int(percent / 5)
    return "█" * filled + "░" * (20 - filled)

async def progress_callback(current, total, action, message, start_time, is_time_based=False, original_name=None):
    if message.chat.id in HIDE_PROGRESS_BAR:
        return
    if total == 0: return
    now = time.time()
    msg_id = message.id
    
    interval = USER_PROGRESS_INTERVAL.get(message.chat.id, 5)
    
    if msg_id in PROGRESS_CACHE:
        if now - PROGRESS_CACHE[msg_id] < interval: 
            return
    PROGRESS_CACHE[msg_id] = now
    
    percent = (current / total) * 100
    if percent > 100: percent = 100
    
    elapsed = now - start_time
    
    if is_time_based:
        speed = current / elapsed if elapsed > 0 else 0
        eta = (total - current) / speed if speed > 0 else 0
        size_str = f"{format_duration(current)} / {format_duration(total)}"
        speed_str = f"{speed:.2f}x"
    else:
        speed = current / elapsed if elapsed > 0 else 0
        eta = (total - current) / speed if speed > 0 else 0
        size_str = f"{format_size(current)} / {format_size(total)}"
        speed_str = f"{format_size(speed)}/s"
    
    # Original Name added to progress bar
    orig_name_str = f"**File:** `{original_name}`\n" if original_name else ""
    
    text = (
        f"**{action}**\n"
        f"{orig_name_str}"
        f"`[{make_progress_bar(percent)}]` **{percent:.2f}%**\n"
        f"**Processed:** `{size_str}`\n"
        f"**Speed:** `{speed_str}`\n"
        f"**Elapsed:** `{format_duration(elapsed)}` | **ETA:** `{format_duration(eta)}`"
    )
    try:
        await message.edit_text(text, reply_markup=progress_keyboard())
    except Exception:
        pass

async def update_batch_status(c, m, uid, status_text, reply_markup=None):
    if uid in BATCH_STATUS_MSG:
        try:
            await c.edit_message_text(m.chat.id, BATCH_STATUS_MSG[uid], status_text, reply_markup=reply_markup)
        except Exception:
            msg = await m.reply_text(status_text, reply_markup=reply_markup)
            BATCH_STATUS_MSG[uid] = msg.id
            async def auto_delete(msg_obj):
                await asyncio.sleep(15)
                try: await msg_obj.delete()
                except: pass
            asyncio.ensure_future(auto_delete(msg))
    else:
        msg = await m.reply_text(status_text, reply_markup=reply_markup)
        BATCH_STATUS_MSG[uid] = msg.id
        async def auto_delete(msg_obj, u):
            await asyncio.sleep(15)
            try: 
                await msg_obj.delete()
                if u in BATCH_STATUS_MSG:
                    del BATCH_STATUS_MSG[u]
            except: pass
        asyncio.ensure_future(auto_delete(msg, uid))

async def add_to_queue(uid, c, m, original_name, is_url=False, url=None, is_yt_dlp=False, fmt=None, title=None, res=None, original_caption=None):
    if uid not in USER_QUEUES:
        USER_QUEUES[uid] = asyncio.Queue()
    
    try:
        if is_yt_dlp:
            status_msg = await m.reply_text(f"Queue: YT-DLP processing started for `{title}` ({res}p)...")
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
        'is_yt_dlp': is_yt_dlp,
        'fmt': fmt,
        'title': title,
        'res': res,
        'original_caption': original_caption
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


async def get_filename_from_url(url):
    """Accurately detect filename from URL/Headers using regex without deprecated cgi module."""
    try:
        # Optimized with IPv4 forcing to prevent slow DNS timeouts
        connector = aiohttp.TCPConnector(limit=0, family=socket.AF_INET, use_dns_cache=True, ttl_dns_cache=300)
        async with aiohttp.ClientSession(connector=connector) as sess:
            async with sess.head(url, allow_redirects=True, timeout=10) as resp:
                cd = resp.headers.get('Content-Disposition')
                if cd:
                    # Using regex instead of deprecated cgi module
                    fname_match = re.findall(r'filename\*?=(?:UTF-8\'\')?["\']?([^"\';\n]+)', cd, re.IGNORECASE)
                    if fname_match:
                        extracted_name = urllib.parse.unquote(fname_match[0])
                        # Prevent OS filename length errors (Linux/Windows max is usually ~255 bytes)
                        if len(extracted_name) > 200:
                            ext = Path(extracted_name).suffix
                            extracted_name = extracted_name[:200 - len(ext)] + ext
                        return extracted_name
    except Exception:
        pass
        
    fname = url.split("/")[-1].split("?")[0]
    fname = urllib.parse.unquote(fname)
    
    # Prevent OS filename length errors for very long URLs
    if len(fname) > 200:
        ext = Path(fname).suffix
        if not ext or len(ext) > 20: 
            ext = ".mp4"
        fname = fname[:200 - len(ext)] + ext
        
    return fname

async def download_stream(resp, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    total = 0
    if out_path.exists():
        total = out_path.stat().st_size
    try:
        size = int(resp.headers.get("Content-Length", 0)) + total
    except:
        size = 0
    chunk_size = 1024 * 1024
    start_t = time.time()
    try:
        mode = "ab" if total > 0 else "wb"
        with out_path.open(mode) as f:
            async for chunk in resp.content.iter_chunked(chunk_size):
                if cancel_event and cancel_event.is_set():
                    return False, "Operation cancelled by user."
                if not chunk:
                    break
                if total > MAX_SIZE:
                    return False, "File size cannot exceed limit."
                total += len(chunk)
                f.write(chunk)
                
                if message and size > 0:
                    await progress_callback(total, size, "Downloading...", message, start_t, original_name=original_name)
    except Exception as e:
        return False, str(e)
    return True, None

async def download_url_generic(url: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    for attempt in range(1, 11):
        timeout = aiohttp.ClientTimeout(total=7200, sock_connect=120)
        headers = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"}
        if out_path.exists():
            downloaded = out_path.stat().st_size
            headers["Range"] = f"bytes={downloaded}-"
            
        # Cloudflare DNS/IPv4 optimization for faster connection speed
        connector = aiohttp.TCPConnector(limit=0, family=socket.AF_INET, use_dns_cache=True, ttl_dns_cache=300)
        try:
            async with aiohttp.ClientSession(timeout=timeout, headers=headers, connector=connector) as sess:
                async with sess.get(url, allow_redirects=True) as resp:
                    if resp.status in (404, 403) or resp.status >= 500:
                        if attempt < 10:
                            await asyncio.sleep(2)
                            continue
                        return False, f"HTTP {resp.status}"
                    if resp.status in (200, 206):
                        ok, err = await download_stream(resp, out_path, message, cancel_event=cancel_event, original_name=original_name)
                        if ok: return True, None
                        else:
                            if attempt < 10: await asyncio.sleep(2); continue
                            return False, err
        except Exception as e:
            if attempt < 10:
                await asyncio.sleep(2)
                continue
            return False, str(e)
    return False, "Failed after 10 attempts"

async def download_drive_file(file_id: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    base = f"https://drive.google.com/uc?export=download&id={file_id}"
    for attempt in range(1, 11):
        timeout = aiohttp.ClientTimeout(total=7200, sock_connect=120)
        headers = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"}
        
        if out_path.exists():
            downloaded = out_path.stat().st_size
            headers["Range"] = f"bytes={downloaded}-"
            
        # DNS optimization for faster connectivity
        connector = aiohttp.TCPConnector(limit=0, family=socket.AF_INET, use_dns_cache=True, ttl_dns_cache=300)
        try:
            async with aiohttp.ClientSession(timeout=timeout, headers=headers, connector=connector) as sess:
                async with sess.get(base, allow_redirects=True) as resp:
                    if resp.status in (200, 206) and "content-disposition" in (k.lower() for k in resp.headers.keys()):
                        ok, err = await download_stream(resp, out_path, message, cancel_event=cancel_event, original_name=original_name)
                        if ok: return True, None
                        if attempt < 10: await asyncio.sleep(2); continue
                        
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
                            if resp2.status not in (200, 206):
                                return False, f"HTTP {resp2.status}"
                            ok, err = await download_stream(resp2, out_path, message, cancel_event=cancel_event, original_name=original_name)
                            if ok: return True, None
                            if attempt < 10: await asyncio.sleep(2); continue
                            
                    for k, v in resp.cookies.items():
                        if k.startswith("download_warning"):
                            token = v.value
                            download_url = f"https://drive.google.com/uc?export=download&confirm={token}&id={file_id}"
                            async with sess.get(download_url, allow_redirects=True) as resp2:
                                if resp2.status == 404 or resp2.status >= 500:
                                    if attempt < 10:
                                        await asyncio.sleep(2)
                                        continue
                                if resp2.status not in (200, 206):
                                    return False, f"HTTP {resp2.status}"
                                ok, err = await download_stream(resp2, out_path, message, cancel_event=cancel_event, original_name=original_name)
                                if ok: return True, None
                                if attempt < 10: await asyncio.sleep(2); continue
                    
                    if attempt < 10 and resp.status not in (200, 206):
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
        BotCommand("zip_file_download", "Toggle ZIP Download Mode (admin only)"),
        BotCommand("setthumb", "Set custom thumbnail (admin only)"),
        BotCommand("view_thumb", "View your thumbnail (admin only)"),
        BotCommand("del_thumb", "Delete your thumbnail (admin only)"),
        BotCommand("set_caption", "Set custom caption (admin only)"),
        BotCommand("view_caption", "View your caption (admin only)"),
        BotCommand("edit_caption_mode", "Toggle edit caption mode (admin only)"),
        BotCommand("rename", "Rename replied video (admin only)"),
        BotCommand("mkv_video_audio_change", "MKV audio track change mode (admin only)"),
        BotCommand("yt_dlp", "Toggle YT-DLP mode for all URLs (admin only)"),
        BotCommand("convert", "Convert Video/Audio quality, bitrate & format (admin only)"),
        BotCommand("audio_add", "Add audio track to a video (admin only)"),
        BotCommand("create_post", "Create new post (admin only)"), 
        BotCommand("mode_check", "Check current mode status (admin only)"), 
        BotCommand("progress_bar", "Toggle progress bar ON/OFF or Custom Interval (admin only)"),
        BotCommand("continue", "Resume paused queue / Restore buttons"),
        BotCommand("restart", "Show Storage info and Clear Data"),
        BotCommand("help", "Help")
    ]
    try:
        await app.set_bot_commands(cmds)
    except Exception as e:
        logger.warning("Set commands error: %s", e)

async def sequential_upload_task(uid, client, message, tmp_path, renamed_file, status_msg_id, cancel_event, default_caption=None, original_caption=None, original_download_name=None):
    """Background task that waits for upload lock to ensure sequential uploads."""
    if uid not in USER_UPLOAD_LOCKS:
        USER_UPLOAD_LOCKS[uid] = asyncio.Lock()
    
    async with USER_UPLOAD_LOCKS[uid]:
        if cancel_event.is_set():
            if tmp_path.exists(): tmp_path.unlink()
            return
        await process_file_and_upload(client, message, tmp_path, target_name=renamed_file, original_download_name=original_download_name, messages_to_delete=[status_msg_id] if status_msg_id else [], cancel_event_passed=cancel_event, passed_uid=uid, default_caption=default_caption, original_caption_passed=original_caption)

# --- QUEUE WORKER WITH PAUSE LOGIC ---
async def process_queue_handler(uid, client):
    """Worker function that processes tasks sequentially for a user."""
    queue = USER_QUEUES[uid]
    while not queue.empty():
        # Pause Logic handling
        while uid in USER_QUEUE_PAUSED:
            await asyncio.sleep(1)
            
        task_data = await queue.get()
        try:
            m = task_data.get('message')
            original_name = task_data.get('original_name')
            status_msg = task_data.get('status_msg') 
            is_url = task_data.get('is_url', False)
            is_yt_dlp = task_data.get('is_yt_dlp', False)
            original_caption = task_data.get('original_caption')
            
            cancel_event = asyncio.Event()
            TASKS.setdefault(uid, []).append(cancel_event)
            if status_msg:
                USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            
            if is_yt_dlp:
                url = task_data.get('url')
                fmt = task_data.get('fmt')
                title = task_data.get('title')
                res = task_data.get('res', 'Unknown')
                
                safe_title = re.sub(r"[\\/*?\"<>|:]", "_", title)
                if len(safe_title) > 100: safe_title = safe_title[:100]
                
                out_tmpl = str(TMP / f"yt_{uid}_{int(datetime.now().timestamp())}_{res}p_{safe_title}.%(ext)s")
                
                ydl_opts = {
                    'format': fmt,
                    'outtmpl': out_tmpl,
                    'quiet': True,
                    'no_warnings': True,
                    'merge_output_format': 'mkv',
                }

                if COOKIES_TXT and os.path.exists(COOKIES_TXT):
                    ydl_opts['cookiefile'] = COOKIES_TXT
                    
                last_edit = 0
                loop = asyncio.get_running_loop()
                start_t = time.time()
                def my_hook(d):
                    nonlocal last_edit
                    if d['status'] == 'downloading':
                        if cancel_event.is_set():
                            raise Exception("Operation cancelled by user.")
                        now = time.time()
                        interval = USER_PROGRESS_INTERVAL.get(uid, 5)
                        if now - last_edit >= interval:
                            last_edit = now
                            downloaded = d.get('downloaded_bytes', 0)
                            total = d.get('total_bytes', 0) or d.get('total_bytes_estimate', 0)
                            if total > 0:
                                asyncio.run_coroutine_threadsafe(
                                    progress_callback(downloaded, total, f"Downloading YT-DLP ({res}p)...", status_msg, start_t, original_name=title),
                                    loop
                                )
                ydl_opts['progress_hooks'] = [my_hook]
                
                try:
                    def run_dl():
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            info = ydl.extract_info(url, download=True)
                            if 'requested_downloads' in info:
                                return info['requested_downloads'][0]['filepath']
                            return ydl.prepare_filename(info)
                    
                    if status_msg:
                        await status_msg.edit(f"Starting YT-DLP Download for {res}p...", reply_markup=progress_keyboard())
                    downloaded_file = await asyncio.to_thread(run_dl)
                    actual_path = Path(downloaded_file)
                    
                    if cancel_event.is_set() or not actual_path.exists():
                         raise Exception("Cancelled or download failed.")
                         
                    if status_msg:
                        await status_msg.edit_text(f"Download complete ({res}p), uploading to Telegram...", reply_markup=None)
                    
                    original_name = actual_path.name
                    renamed_file = generate_new_filename(original_name)
                    
                    yt_caption = f"{title} - {res}p" if title else original_name
                    
                    asyncio.create_task(
                        sequential_upload_task(uid, client, m, actual_path, renamed_file, status_msg.id if status_msg else None, cancel_event, default_caption=yt_caption, original_caption=original_caption, original_download_name=original_name)
                    )
                except Exception as e:
                    logger.error(f"YT-DLP Queue DL Error: {e}")
                    raise e
                        
            elif is_url:
                url = task_data.get('url')
                await download_and_process_generic(client, m, url, status_msg, cancel_event)
            else:
                # Start Processing
                file_info = m.video or m.document
                
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
                            await progress_callback(current, total, "Downloading...", status_msg, start_t, original_name=original_name)
                            
                    await m.download(file_name=str(tmp_path), progress=dl_prog)
                    
                    if cancel_event.is_set():
                         if tmp_path.exists(): tmp_path.unlink()
                         if cancel_event in TASKS.get(uid, []):
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
                        sequential_upload_task(uid, client, m, tmp_path, renamed_file, status_msg.id if status_msg else None, cancel_event, default_caption=original_name, original_caption=original_caption, original_download_name=original_name)
                    )
                
                except Exception as e:
                    if tmp_path.exists():
                        tmp_path.unlink()
                    raise e

        except Exception as e:
            logger.error(f"Queue Loop Error: {e}")
            USER_QUEUE_PAUSED.add(uid)
            markup = InlineKeyboardMarkup([
                [InlineKeyboardButton("Continue ▶️", callback_data="queue_continue"),
                 InlineKeyboardButton("Delete 🗑️", callback_data="queue_delete")]
            ])
            err_msg = f"Task Failed for `{original_name}`: {e}\n\n⚠️ **Queue is Paused.** Please select an option to resume or cancel remaining queue."
            if status_msg:
                try: await status_msg.reply_text(err_msg, reply_markup=markup, quote=True)
                except: pass
            elif m:
                try: await m.reply_text(err_msg, reply_markup=markup, quote=True)
                except: pass
        finally:
            queue.task_done()
    
    # Cleanup when queue is empty
    if uid in USER_WORKERS: del USER_WORKERS[uid]
    if uid in USER_QUEUES: del USER_QUEUES[uid]


@app.on_callback_query(filters.regex("refresh_btn"))
async def refresh_btn_cb(c, cb):
    # Sends a small refresh acknowledgment. AIOHTTP handles its own chunk restarts in generic.
    await cb.answer("Refreshed! Progress will update shortly...", show_alert=False)

@app.on_callback_query(filters.regex("queue_continue"))
async def queue_continue_cb(c, cb):
    uid = cb.from_user.id
    USER_QUEUE_PAUSED.discard(uid)
    await cb.answer("Queue Resumed!", show_alert=True)
    try: await cb.message.delete()
    except: pass

@app.on_callback_query(filters.regex("queue_delete"))
async def queue_delete_cb(c, cb):
    uid = cb.from_user.id
    # Clear queues
    if uid in USER_QUEUES:
        while not USER_QUEUES[uid].empty():
            try: 
                item = USER_QUEUES[uid].get_nowait()
                if 'status_msg' in item and item['status_msg']:
                    try: await item['status_msg'].delete()
                    except: pass
                USER_QUEUES[uid].task_done()
            except: pass
            
    if uid in ZIP_DL_QUEUES:
        while not ZIP_DL_QUEUES[uid].empty():
            try: 
                item = ZIP_DL_QUEUES[uid].get_nowait()
                if 'queue_msg' in item and item['queue_msg']:
                    try: await item['queue_msg'].delete()
                    except: pass
                ZIP_DL_QUEUES[uid].task_done()
            except: pass
            
    if uid in AUDIO_ADD_QUEUES:
        while not AUDIO_ADD_QUEUES[uid].empty():
            try:
                item = AUDIO_ADD_QUEUES[uid].get_nowait()
                if 'queue_msg' in item and item['queue_msg']:
                    try: await item['queue_msg'].delete()
                    except: pass
                AUDIO_ADD_QUEUES[uid].task_done()
            except: pass
            
    if uid in USER_WORKERS:
        USER_WORKERS[uid].cancel()
        del USER_WORKERS[uid]
        
    USER_QUEUE_PAUSED.discard(uid)
    await cb.answer("All Queues Deleted & Cancelled!", show_alert=True)
    try: await cb.message.delete()
    except: pass


# --- YT-DLP CORE FUNCTIONS ---
def build_yt_keyboard(session_id):
    session = YT_SESSIONS.get(session_id)
    if not session: return []
    keyboard = []
    
    sorted_res = sorted(session['formats'].keys(), reverse=True)
    for res in sorted_res:
        fmt_data = session['formats'][res]
        size_str = fmt_data['size_str']
        is_selected = res in session['selected']
        
        sel_text = f"✅ {res}p" if is_selected else f"🔲 Select {res}p"
        
        row = [
            InlineKeyboardButton(f"⬇️ {res}p ({size_str})", callback_data=f"ytdir_{session_id}_{res}"),
            InlineKeyboardButton(sel_text, callback_data=f"ytsel_{session_id}_{res}")
        ]
        keyboard.append(row)
        
    keyboard.append([InlineKeyboardButton("OK ✅", callback_data=f"ytok_{session_id}")])
    keyboard.append([InlineKeyboardButton("Add Save Quality 💾", callback_data=f"ytsave_{session_id}")])
    keyboard.append([InlineKeyboardButton("Load Saved Quality 🔄", callback_data=f"ytload_{session_id}")])
    keyboard.append([InlineKeyboardButton("Cancel ❌", callback_data="cancel_yt")])
    return InlineKeyboardMarkup(keyboard)

async def queue_yt_dlp(uid, c, m, url, fmt, title, res):
    if uid not in USER_QUEUES:
        USER_QUEUES[uid] = asyncio.Queue()
    try:
        status_msg = await m.reply_text(f"Queue: YT-DLP added to queue for `{title}` ({res}p)...")
    except:
        status_msg = None

    await USER_QUEUES[uid].put({
        'message': m,
        'original_name': title,
        'status_msg': status_msg,
        'is_url': True, 
        'is_yt_dlp': True,
        'url': url,
        'fmt': fmt,
        'title': title,
        'res': res
    })
    
    if uid not in USER_WORKERS or USER_WORKERS[uid].done():
         USER_WORKERS[uid] = asyncio.create_task(process_queue_handler(uid, c))

async def fetch_youtube_formats(c, m, url):
    uid = m.from_user.id
    status_msg = await m.reply_text("Fetching YouTube formats...", quote=True)
    
    try:
        ydl_opts = {'quiet': True, 'no_warnings': True}

        if COOKIES_TXT and os.path.exists(COOKIES_TXT):
            ydl_opts['cookiefile'] = COOKIES_TXT

        def extract():
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                return ydl.extract_info(url, download=False)
        
        info = await asyncio.to_thread(extract)
        formats = info.get('formats', [])
        
        ts = int(time.time())
        session_id = f"{uid}_{ts}"
        
        YT_SESSIONS[session_id] = {
            'url': url,
            'title': info.get('title', 'Video'),
            'formats': {},
            'selected': []
        }
        
        for f in formats:
            ext = f.get('ext', '')
            res = f.get('height')
            size = f.get('filesize') or f.get('filesize_approx')
            vcodec = f.get('vcodec', 'none')
            
            if vcodec != 'none' and res and size:
                if res not in YT_SESSIONS[session_id]['formats']:
                    format_id = f.get('format_id')
                    dl_format = f"{format_id}+bestaudio/best" if f.get('acodec') == 'none' else format_id
                    YT_SESSIONS[session_id]['formats'][res] = {
                        'format_id': dl_format,
                        'size_str': format_size(size),
                        'ext': ext
                    }
        
        if not YT_SESSIONS[session_id]['formats']:
            await status_msg.edit("No suitable video formats found.")
            return
        
        await status_msg.edit(
            f"**Title:** {info.get('title')}\n\nSelect Qualities:",
            reply_markup=build_yt_keyboard(session_id)
        )

    except Exception as e:
        logger.error(f"YT-DLP Error: {e}")
        await status_msg.edit(f"Failed to fetch YouTube formats: {e}")

@app.on_callback_query(filters.regex(r"^yt(dir|sel|ok|save|load)_"))
async def yt_multi_callback(c: Client, cb: CallbackQuery):
    data = cb.data.split('_')
    action = data[0]
    uid_str = data[1]
    ts = data[2]
    session_id = f"{uid_str}_{ts}"
    
    if cb.from_user.id != int(uid_str):
        await cb.answer("You are not authorized for this action.", show_alert=True)
        return
        
    session = YT_SESSIONS.get(session_id)
    if not session:
        await cb.answer("Session expired or invalid.", show_alert=True)
        return
        
    uid = cb.from_user.id
    
    if action == "ytsel":
        res = int(data[3])
        if res in session['selected']:
            session['selected'].remove(res)
        else:
            session['selected'].append(res)
        await cb.message.edit_reply_markup(build_yt_keyboard(session_id))
        
    elif action == "ytdir":
        res = int(data[3])
        fmt_data = session['formats'][res]
        await queue_yt_dlp(uid, c, cb.message, session['url'], fmt_data['format_id'], session['title'], res)
        await cb.message.edit_text(f"Added {res}p to processing queue.")
        
    elif action == "ytok":
        if not session['selected']:
            await cb.answer("Select at least one quality!", show_alert=True)
            return
        for res in session['selected']:
            fmt_data = session['formats'][res]
            await queue_yt_dlp(uid, c, cb.message, session['url'], fmt_data['format_id'], session['title'], res)
        await cb.message.edit_text(f"Added {len(session['selected'])} selected qualities to queue.")
        
    elif action == "ytsave":
        if not session['selected']:
            await cb.answer("Select at least one quality to save!", show_alert=True)
            return
        SAVED_YT_QUALITIES[uid] = session['selected'].copy()
        for res in session['selected']:
            fmt_data = session['formats'][res]
            await queue_yt_dlp(uid, c, cb.message, session['url'], fmt_data['format_id'], session['title'], res)
        await cb.message.edit_text(f"Saved {len(session['selected'])} qualities and added to queue.")
        
    elif action == "ytload":
        saved = SAVED_YT_QUALITIES.get(uid, [])
        if not saved:
            await cb.answer("No saved qualities found!", show_alert=True)
            return
        loaded_count = 0
        for res in saved:
            if res in session['formats']:
                fmt_data = session['formats'][res]
                await queue_yt_dlp(uid, c, cb.message, session['url'], fmt_data['format_id'], session['title'], res)
                loaded_count += 1
        if loaded_count > 0:
            await cb.message.edit_text(f"Loaded {loaded_count} saved qualities and added to queue.")
        else:
            await cb.answer("Saved qualities not available for this video.", show_alert=True)

@app.on_callback_query(filters.regex("cancel_yt"))
async def cancel_yt_cb(c, cb: CallbackQuery):
    try:
        await cb.message.delete()
    except: pass
# -----------------------------

@app.on_callback_query(filters.regex("multi_group_done"))
async def multi_group_done_cb(c, cb):
    uid = cb.from_user.id
    if uid in MULTI_GROUP_BATCH_MODE:
        if uid not in MULTI_GROUP_DATA:
            MULTI_GROUP_DATA[uid] = [[]]
        MULTI_GROUP_DATA[uid].append([])
        group_num = len(MULTI_GROUP_DATA[uid])
        try:
            await cb.message.delete()
        except Exception: pass
        
        if uid in MULTI_GROUP_DONE_MSG:
            MULTI_GROUP_DONE_MSG.pop(uid, None)
            
        await c.send_message(cb.message.chat.id, f"New group created (Group {group_num}). Forward/send videos for this group.")
        await cb.answer("New group created.", show_alert=False)
    else:
        await cb.answer("Multi-group mode is not active.", show_alert=True)

# ---- handlers ----
@app.on_message(filters.command("start") & filters.private)
async def start_handler(c, m: Message):
    await set_bot_commands()
    text = (
        "Hi! I am URL uploader bot.\n\n"
        "Note: Many commands can only be used by the Admin (owner).\n\n"
        "Commands:\n"
        "/upload_url <url> - Download & Upload file from URL (admin only)\n"
        "/zip_file_download - Toggle ZIP Download Mode (admin only)\n"
        "/setthumb - Send an image to set as your thumbnail (admin only)\n"
        "/view_thumb - View your thumbnail (admin only)\n"
        "/del_thumb - Delete your thumbnail (admin only)\n"
        "/set_caption - Set custom caption (admin only)\n"
        "/view_caption - View your caption (admin only)\n"
        "/edit_caption_mode - Toggle edit caption mode (admin only)\n"
        "/rename <newname.ext> - Rename replied video (admin only)\n"
        "/mkv_video_audio_change - MKV audio track change mode (admin only)\n"
        "/yt_dlp - Toggle YT-DLP mode for all URLs (admin only)\n"
        "/convert - Convert Video/Audio quality, bitrate & format (admin only)\n"
        "/audio_add - Add audio track to a video (admin only)\n"
        "/create_post - Create new post (admin only)\n" 
        "/mode_check - Check current mode status (admin only)\n" 
        "/progress_bar - Toggle progress bar ON/OFF or Custom Interval (admin only)\n"
        "/continue - Resume paused queue / Restore buttons\n"
        "/restart - Show Storage info and Clear Data\n"
        "/help - Help"
    )
    await m.reply_text(text)

@app.on_message(filters.command("help") & filters.private)
async def help_handler(c, m):
    await start_handler(c, m)

@app.on_message(filters.command("continue") & filters.private)
async def continue_cmd(c, m: Message):
    uid = m.from_user.id
    if uid in USER_QUEUE_PAUSED:
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("Continue ▶️", callback_data="queue_continue"),
             InlineKeyboardButton("Delete 🗑️", callback_data="queue_delete")]
        ])
        await m.reply_text("Queue is currently paused due to an error. Select an option to resume or delete:", reply_markup=markup)
    else:
        await m.reply_text("Your queue is not paused right now.")

@app.on_message(filters.command("restart") & filters.private)
async def restart_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    total, used, free = shutil.disk_usage("/")
    text = (f"**📊 Storage Status:**\n\n"
            f"**Total Storage:** `{format_size(total)}`\n"
            f"**Used Storage:** `{format_size(used)}`\n"
            f"**Free Storage:** `{format_size(free)}`\n\n"
            f"Use the buttons below to manage bot data.")
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("Clear Tmp Data 🗑", callback_data="clear_tmp_data")],
        [InlineKeyboardButton("Clean & Reset Bot 🔄", callback_data="full_reset_bot")]
    ])
    await m.reply_text(text, reply_markup=markup)

@app.on_callback_query(filters.regex("clear_tmp_data"))
async def clear_tmp_data_cb(c, cb):
    uid = cb.from_user.id
    if not is_admin(uid): return
    shutil.rmtree(TMP, ignore_errors=True)
    TMP.mkdir(parents=True, exist_ok=True)
    await cb.answer("Storage Formatted / Data Cleared!", show_alert=True)
    await cb.message.edit_text(cb.message.text + "\n\n*(Data Successfully Cleared)*")

@app.on_callback_query(filters.regex("full_reset_bot"))
async def full_reset_bot_cb(c, cb):
    uid = cb.from_user.id
    if not is_admin(uid): return
    
    # Fully Clear All State Vars
    USER_THUMBS.clear()
    TASKS.clear()
    USER_TASK_EVENTS.clear()
    SET_THUMB_REQUEST.clear()
    SET_CAPTION_REQUEST.clear()
    USER_CAPTIONS.clear()
    USER_COUNTERS.clear()
    EDIT_CAPTION_MODE.clear()
    USER_THUMB_TIME.clear()
    HIDE_PROGRESS_BAR.clear()
    USER_PROGRESS_INTERVAL.clear()
    USER_QUEUE_PAUSED.clear()
    AUTO_UPLOAD_ALL.clear()
    MKV_AUDIO_CHANGE_MODE.clear()
    PENDING_AUDIO_ORDERS.clear()
    CONVERT_MODE.clear()
    ACTIVE_CONVERT_SESSION.clear()
    for s_id in list(CONVERT_SESSIONS.keys()):
        try:
            CONVERT_SESSIONS[s_id]['path'].unlink(missing_ok=True)
        except: pass
    CONVERT_SESSIONS.clear()
    AUDIO_ADD_MODE.clear()
    AUDIO_ADD_STATE.clear()
    if uid in AUDIO_ADD_QUEUES:
        while not AUDIO_ADD_QUEUES[uid].empty():
            try: AUDIO_ADD_QUEUES[uid].get_nowait(); AUDIO_ADD_QUEUES[uid].task_done()
            except: pass
    AUDIO_ADD_QUEUES.clear()
    for worker in AUDIO_ADD_WORKERS.values():
        worker.cancel()
    AUDIO_ADD_WORKERS.clear()
    
    CREATE_POST_MODE.clear()
    POST_CREATION_STATE.clear()
    BATCH_CAPTION_MODE.clear()
    BATCH_UPLOAD_MODE.clear()
    BATCH_DATA.clear()
    BATCH_STATUS_MSG.clear()
    
    if uid in USER_QUEUES:
        while not USER_QUEUES[uid].empty():
            try: USER_QUEUES[uid].get_nowait(); USER_QUEUES[uid].task_done()
            except: pass
    USER_QUEUES.clear()
    
    for worker in USER_WORKERS.values():
        worker.cancel()
    USER_WORKERS.clear()
    USER_UPLOAD_LOCKS.clear()
    MULTI_GROUP_BATCH_MODE.clear()
    MULTI_GROUP_DATA.clear()
    USE_ORIGINAL_CAPTION_IN_MULTI_GROUP.clear()
    MULTI_GROUP_DONE_MSG.clear()
    ZIP_DOWNLOAD_MODE.clear()
    ZIP_NAV_STATE.clear()
    ZIP_READY_LIST.clear()
    
    if uid in ZIP_DL_QUEUES:
        while not ZIP_DL_QUEUES[uid].empty():
            try: ZIP_DL_QUEUES[uid].get_nowait(); ZIP_DL_QUEUES[uid].task_done()
            except: pass
    ZIP_DL_QUEUES.clear()
    
    for worker in ZIP_DL_WORKERS.values():
        worker.cancel()
    ZIP_DL_WORKERS.clear()
    NAV_PATHS.clear()
    YT_SESSIONS.clear()
    YT_DLP_MODE.clear()
    SAVED_YT_QUALITIES.clear()
    
    # Clear Files
    shutil.rmtree(TMP, ignore_errors=True)
    TMP.mkdir(parents=True, exist_ok=True)
    
    await cb.answer("Bot completely reset to fresh state!", show_alert=True)
    await cb.message.edit_text(cb.message.text + "\n\n*(Bot Fully Reset & Cleaned)*")


@app.on_message(filters.command("zip_file_download") & filters.private)
async def zip_file_download_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    if uid in ZIP_DOWNLOAD_MODE:
        ZIP_DOWNLOAD_MODE.discard(uid)
        ZIP_READY_LIST.pop(uid, None)
        ZIP_NAV_STATE.pop(uid, None)
        AUTO_UPLOAD_ALL.discard(uid)
        if uid in ZIP_DL_QUEUES:
            while not ZIP_DL_QUEUES[uid].empty():
                try: 
                    item = ZIP_DL_QUEUES[uid].get_nowait()
                    if 'queue_msg' in item and item['queue_msg']:
                        try: await item['queue_msg'].delete()
                        except: pass
                    ZIP_DL_QUEUES[uid].task_done()
                except: pass
        await m.reply_text("ZIP File Download Mode **OFF**.")
    else:
        ZIP_DOWNLOAD_MODE.add(uid)
        await m.reply_text("ZIP File Download Mode **ON**.\nSend direct links or Telegram Files. Multiple items will be queued automatically.\nType `clear` to reset. Type `all` for auto upload all.")


@app.on_message(filters.command("yt_dlp") & filters.private)
async def toggle_yt_dlp(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    if uid in YT_DLP_MODE:
        YT_DLP_MODE.discard(uid)
        await m.reply_text("YT-DLP Mode **OFF**. Normal URLs will use direct download.")
    else:
        YT_DLP_MODE.add(uid)
        await m.reply_text("YT-DLP Mode **ON**. All URLs given to the bot will be processed via YT-DLP.")

@app.on_message(filters.command("convert") & filters.private)
async def toggle_convert_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    if uid in CONVERT_MODE:
        CONVERT_MODE.discard(uid)
        await m.reply_text("Convert Mode **OFF**.")
    else:
        CONVERT_MODE.add(uid)
        await m.reply_text("Convert Mode **ON**.\nSend or forward any video, audio, or link to compress and convert it.")

@app.on_message(filters.command("audio_add") & filters.private)
async def toggle_audio_add_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    if uid in AUDIO_ADD_MODE:
        AUDIO_ADD_MODE.discard(uid)
        AUDIO_ADD_STATE.pop(uid, None)
        if uid in AUDIO_ADD_QUEUES:
            while not AUDIO_ADD_QUEUES[uid].empty():
                try: AUDIO_ADD_QUEUES[uid].get_nowait(); AUDIO_ADD_QUEUES[uid].task_done()
                except: pass
        await m.reply_text("Audio Add Mode **OFF**.")
    else:
        AUDIO_ADD_MODE.add(uid)
        AUDIO_ADD_STATE[uid] = {
            'phase': 1, 
            'list1': [], 
            'list2': [], 
            'mapping': {}, 
            'source_audios': {}, 
            'selected_audios': {}, 
            'ui_msgs': []
        }
        await m.reply_text("Audio Add Mode **ON**.\n\n**Phase 1:** Please send/forward the TARGET videos/links/files/zips (the videos where audio will be added).\nOnce done, type `next`.")


@app.on_message(filters.command("progress_bar") & filters.private)
async def progress_bar_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    
    if len(m.command) > 1:
        time_str = " ".join(m.command[1:])
        if time_str.lower() in ['off', 'hide']:
            HIDE_PROGRESS_BAR.add(uid)
            await m.reply_text("Progress bar is now OFF.")
        elif time_str.lower() in ['on', 'show']:
            HIDE_PROGRESS_BAR.discard(uid)
            await m.reply_text("Progress bar is now ON.")
        else:
            seconds = parse_time(time_str)
            if seconds > 0:
                USER_PROGRESS_INTERVAL[uid] = seconds
                HIDE_PROGRESS_BAR.discard(uid)
                await m.reply_text(f"Progress bar update interval set to: {seconds} seconds.")
            else:
                await m.reply_text("Invalid format. Use /progress_bar 5s or /progress_bar 1m.")
    else:
        if uid in HIDE_PROGRESS_BAR:
            HIDE_PROGRESS_BAR.discard(uid)
            await m.reply_text(f"Progress bar is now ON (Interval: {USER_PROGRESS_INTERVAL.get(uid, 5)}s).")
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
    
    # --- Handle Create Post Mode ---
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
        if uid in MULTI_GROUP_BATCH_MODE:
            MULTI_GROUP_BATCH_MODE.discard(uid)
            MULTI_GROUP_DATA.pop(uid, None)
        if uid in BATCH_STATUS_MSG:
            BATCH_STATUS_MSG.pop(uid, None)
        if uid in MULTI_GROUP_DONE_MSG:
            MULTI_GROUP_DONE_MSG.pop(uid, None)
            
        USE_ORIGINAL_CAPTION_IN_MULTI_GROUP.discard(uid)
            
        await m.reply_text("edit video caption mode **OFF**.\nFrom now on, uploaded videos will be renamed, thumbnails changed, and saved caption added.")
    else:
        EDIT_CAPTION_MODE.add(uid)
        await m.reply_text("edit video caption mode **ON**.\nFrom now on, only the saved caption will be added. Video name and thumbnail will remain the same.\n\n**New Feature:** Type `on` to enable file ID save mode. Type `no` to enable Multi-group Batch mode. Type `off` to disable.")

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

# --- HANDLER: /create_post ---
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


# --- HANDLER: /mode_check ---
@app.on_message(filters.command("mode_check") & filters.private)
async def mode_check_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    
    audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
    caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
    yt_dlp_status = "✅ ON" if uid in YT_DLP_MODE else "❌ OFF"
    zip_status = "✅ ON" if uid in ZIP_DOWNLOAD_MODE else "❌ OFF"
    convert_status = "✅ ON" if uid in CONVERT_MODE else "❌ OFF"
    audio_add_status = "✅ ON" if uid in AUDIO_ADD_MODE else "❌ OFF"
    
    waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
    waiting_status_text = f"{waiting_count} file(s) waiting for track order." if waiting_count > 0 else "No files are waiting."
    
    status_text = (
        "🤖 **Current Mode Status:**\n\n"
        f"1. **Convert Mode:** `{convert_status}`\n"
        f"   - *Task:* Change Quality/Bitrate of Videos/Audio interactively.\n\n"
        f"2. **Audio Add Mode:** `{audio_add_status}`\n"
        f"   - *Task:* Add/merge audio tracks from one video/file to another seamlessly.\n\n"
        f"3. **MKV Audio Change Mode:** `{audio_status}`\n"
        f"   - *Task:* Changes audio track order of forwarded/downloaded MKV/video files. (Stays ON until manually off)\n"
        f"   - *Status:* {waiting_status_text}\n\n"
        f"4. **Edit Caption Mode:** `{caption_status}`\n"
        f"   - *Task:* Adds saved caption without changing rename or thumbnail of forwarded videos.\n\n"
        f"5. **YT-DLP Mode:** `{yt_dlp_status}`\n"
        f"   - *Task:* Processes URLs using YT-DLP engine.\n\n"
        f"6. **ZIP Download Mode:** `{zip_status}`\n"
        f"   - *Task:* Direct ZIP link processing.\n\n"
        "Click the buttons below to toggle modes."
    )
    
    await m.reply_text(status_text, reply_markup=mode_check_keyboard(uid), parse_mode=ParseMode.MARKDOWN)

# --- CALLBACK: Mode Toggle Buttons ---
@app.on_callback_query(filters.regex("toggle_(audio|caption|ytdlp|zip|convert|audio_add)_mode"))
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

    elif action == "toggle_ytdlp_mode":
        if uid in YT_DLP_MODE:
            YT_DLP_MODE.discard(uid)
            message = "YT-DLP Mode OFF."
        else:
            YT_DLP_MODE.add(uid)
            message = "YT-DLP Mode ON."

    elif action == "toggle_zip_mode":
        if uid in ZIP_DOWNLOAD_MODE:
            ZIP_DOWNLOAD_MODE.discard(uid)
            message = "ZIP Download Mode OFF."
        else:
            ZIP_DOWNLOAD_MODE.add(uid)
            message = "ZIP Download Mode ON."
            
    elif action == "toggle_convert_mode":
        if uid in CONVERT_MODE:
            CONVERT_MODE.discard(uid)
            message = "Convert Mode OFF."
        else:
            CONVERT_MODE.add(uid)
            message = "Convert Mode ON."
            
    elif action == "toggle_audio_add_mode":
        if uid in AUDIO_ADD_MODE:
            AUDIO_ADD_MODE.discard(uid)
            AUDIO_ADD_STATE.pop(uid, None)
            if uid in AUDIO_ADD_QUEUES:
                while not AUDIO_ADD_QUEUES[uid].empty():
                    try: AUDIO_ADD_QUEUES[uid].get_nowait(); AUDIO_ADD_QUEUES[uid].task_done()
                    except: pass
            message = "Audio Add Mode OFF."
        else:
            AUDIO_ADD_MODE.add(uid)
            AUDIO_ADD_STATE[uid] = {
                'phase': 1, 
                'list1': [], 
                'list2': [], 
                'mapping': {}, 
                'source_audios': {}, 
                'selected_audios': {}, 
                'ui_msgs': []
            }
            message = "Audio Add Mode ON."
            
    try:
        audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
        caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
        yt_dlp_status = "✅ ON" if uid in YT_DLP_MODE else "❌ OFF"
        zip_status = "✅ ON" if uid in ZIP_DOWNLOAD_MODE else "❌ OFF"
        convert_status = "✅ ON" if uid in CONVERT_MODE else "❌ OFF"
        audio_add_status = "✅ ON" if uid in AUDIO_ADD_MODE else "❌ OFF"
        
        waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
        waiting_status_text = f"{waiting_count} file(s) waiting for track order." if waiting_count > 0 else "No files are waiting."

        status_text = (
            "🤖 **Current Mode Status:**\n\n"
            f"1. **Convert Mode:** `{convert_status}`\n"
            f"   - *Task:* Change Quality/Bitrate of Videos/Audio interactively.\n\n"
            f"2. **Audio Add Mode:** `{audio_add_status}`\n"
            f"   - *Task:* Add/merge audio tracks from one video/file to another seamlessly.\n\n"
            f"3. **MKV Audio Change Mode:** `{audio_status}`\n"
            f"   - *Task:* Changes audio track order of forwarded/downloaded MKV/video files. (Stays ON until manually off)\n"
            f"   - *Status:* {waiting_status_text}\n\n"
            f"4. **Edit Caption Mode:** `{caption_status}`\n"
            f"   - *Task:* Adds saved caption without changing rename or thumbnail of forwarded videos.\n\n"
            f"5. **YT-DLP Mode:** `{yt_dlp_status}`\n"
            f"   - *Task:* Processes URLs using YT-DLP engine.\n\n"
            f"6. **ZIP Download Mode:** `{zip_status}`\n"
            f"   - *Task:* Direct ZIP link processing.\n\n"
            "Click the buttons below to toggle modes."
        )
        
        await cb.message.edit_text(status_text, reply_markup=mode_check_keyboard(uid), parse_mode=ParseMode.MARKDOWN)
        await cb.answer(message, show_alert=True)
    except Exception as e:
        logger.error(f"Callback edit error: {e}")
        await cb.answer(message, show_alert=True)

# --- ZIP AUTO EXTRACT & UPLOAD LOGIC ---
async def zip_download_worker(uid, c):
    while uid in ZIP_DL_QUEUES and not ZIP_DL_QUEUES[uid].empty():
        while uid in USER_QUEUE_PAUSED:
            await asyncio.sleep(1)
        
        task_data = await ZIP_DL_QUEUES[uid].get()
        try:
            queue_msg = task_data.get('queue_msg')
            if queue_msg:
                try: await queue_msg.delete()
                except: pass
            await execute_zip_download_and_extract(c, task_data['message'], task_data.get('url'), task_data.get('local_path'))
        except Exception as e:
            logger.error(f"ZIP Worker Error: {e}")
            USER_QUEUE_PAUSED.add(uid)
            markup = InlineKeyboardMarkup([
                [InlineKeyboardButton("Continue ▶️", callback_data="queue_continue"),
                 InlineKeyboardButton("Delete 🗑️", callback_data="queue_delete")]
            ])
            try:
                await c.send_message(task_data['message'].chat.id, f"ZIP Task Failed: {e}\n\nQueue Paused. Select an option:", reply_markup=markup, reply_to_message_id=task_data['message'].id)
            except: pass
        finally:
            ZIP_DL_QUEUES[uid].task_done()
    if uid in ZIP_DL_WORKERS:
        del ZIP_DL_WORKERS[uid]

async def check_and_show_next_zip(c, chat_id, uid):
    if uid not in ZIP_NAV_STATE and ZIP_READY_LIST.get(uid):
        next_zip = ZIP_READY_LIST[uid].pop(0)
        ZIP_NAV_STATE[uid] = {
            'root_dir': next_zip['root_dir'],
            'files_to_upload': next_zip['files_to_upload'],
            'state': 'awaiting_selection',
            'garbage_msgs': []
        }
        
        if uid in AUTO_UPLOAD_ALL:
            files = ZIP_NAV_STATE[uid]['files_to_upload']
            final_order = list(range(1, len(files) + 1))
            msg = await c.send_message(chat_id, "Auto Upload All is ON. Starting upload...")
            async def auto_delete_msg(m_obj):
                await asyncio.sleep(5)
                try: await m_obj.delete()
                except: pass
            asyncio.create_task(auto_delete_msg(msg))
            asyncio.create_task(process_zip_uploads(c, chat_id, uid, final_order))
        else:
            await show_files_for_upload(c, chat_id, uid, next_zip['files_to_upload'])

async def show_files_for_upload(c, chat_id, uid, files, status_msg=None):
    state = ZIP_NAV_STATE[uid]
    text_lines = ["**Files extracted and ready for upload:**\n"]
    for i, f in enumerate(files, 1):
        text_lines.append(f"**{i}.** `{f.name}`")
        
    text_lines.append("\n**Upload Options:**")
    text_lines.append("‣ Send file numbers (e.g., `1,3,5,8-15`) to upload in that exact order.")
    text_lines.append("‣ Send `e <number>` (e.g., `e 1`) to manually extract an archive.")
    text_lines.append("‣ Or click **Upload All 🚀** below to upload all videos serially.")
    
    full_text = "\n".join(text_lines)
    
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("Upload All 🚀", callback_data="zip_upload_all")],
        [InlineKeyboardButton("Cancel / Clear ❌", callback_data="zip_cancel")]
    ])
    
    chunks = [full_text[i:i+4000] for i in range(0, len(full_text), 4000)]
    for idx, chunk in enumerate(chunks):
        reply_markup = markup if idx == len(chunks) - 1 else None
        if status_msg and idx == 0:
            try:
                await status_msg.edit(chunk, reply_markup=reply_markup)
                state['garbage_msgs'].append(status_msg.id)
            except:
                msg = await c.send_message(chat_id, chunk, reply_markup=reply_markup)
                state['garbage_msgs'].append(msg.id)
        else:
            msg = await c.send_message(chat_id, chunk, reply_markup=reply_markup)
            state['garbage_msgs'].append(msg.id)
        await asyncio.sleep(0.3)

async def process_zip_uploads(c, message_or_chat_id, uid, final_order):
    chat_id = message_or_chat_id.chat.id if hasattr(message_or_chat_id, 'chat') else message_or_chat_id
    state = ZIP_NAV_STATE.get(uid)
    if not state:
        return
    state['state'] = 'uploading'
    files = state['files_to_upload']
    root_dir = state['root_dir']
    garbage_msgs = state.get('garbage_msgs', [])
    
    upload_status = await c.send_message(chat_id, f"Starting upload of {len(final_order)} files in specified order...")
    
    for idx in final_order:
        while uid in USER_QUEUE_PAUSED:
             await asyncio.sleep(1)
        if uid not in ZIP_NAV_STATE or ZIP_NAV_STATE[uid].get('state') != 'uploading':
            break # Cancelled or cleared during upload
            
        fpath = files[idx - 1]
        if not fpath.exists(): continue
        original_name = fpath.name
        renamed_file = generate_new_filename(original_name)
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        
        # Creating a fake message object if message_or_chat_id is just an ID (for auto upload)
        class FakeMessage:
            def __init__(self, cid):
                class Chat:
                    id = cid
                self.chat = Chat()
                self.from_user = None
                self.id = 0
        m_obj = message_or_chat_id if hasattr(message_or_chat_id, 'chat') else FakeMessage(chat_id)
        
        try:
            await sequential_upload_task(uid, c, m_obj, fpath, renamed_file, None, cancel_event, default_caption=original_name, original_caption=original_name, original_download_name=original_name)
        except Exception as e:
            logger.error(f"ZIP item upload error: {e}")
            USER_QUEUE_PAUSED.add(uid)
            markup = InlineKeyboardMarkup([
                [InlineKeyboardButton("Continue ▶️", callback_data="queue_continue"),
                 InlineKeyboardButton("Delete 🗑️", callback_data="queue_delete")]
            ])
            await c.send_message(chat_id, f"Upload Failed: {e}\nQueue Paused.", reply_markup=markup)
    
    if root_dir:
        shutil.rmtree(root_dir, ignore_errors=True)
    
    try: await c.delete_messages(chat_id, garbage_msgs)
    except: pass
    
    if uid in ZIP_NAV_STATE and ZIP_NAV_STATE[uid].get('state') == 'uploading':
        ZIP_NAV_STATE.pop(uid, None)
        complete_msg = await c.send_message(chat_id, "All ZIP files queued/uploaded successfully.")
        async def auto_delete(msg_obj):
            await asyncio.sleep(5)
            try: await msg_obj.delete()
            except: pass
        asyncio.ensure_future(auto_delete(complete_msg))
        await check_and_show_next_zip(c, chat_id, uid)

@app.on_callback_query(filters.regex("zip_upload_all"))
async def zip_upload_all_cb(c, cb):
    uid = cb.from_user.id
    if uid not in ZIP_NAV_STATE or ZIP_NAV_STATE[uid]['state'] != 'awaiting_selection':
        await cb.answer("Session expired or invalid.", show_alert=True)
        return
    files = ZIP_NAV_STATE[uid]['files_to_upload']
    final_order = list(range(1, len(files) + 1))
    await cb.answer("Starting upload for all files...", show_alert=False)
    await process_zip_uploads(c, cb.message, uid, final_order)
    
@app.on_callback_query(filters.regex("zip_cancel"))
async def zip_cancel_cb(c, cb):
    uid = cb.from_user.id
    if uid in ZIP_NAV_STATE:
        msgs = ZIP_NAV_STATE[uid].get('garbage_msgs', [])
        try: await c.delete_messages(cb.message.chat.id, msgs)
        except: pass
        ZIP_NAV_STATE.pop(uid, None)
    await cb.message.edit_text("ZIP session cleared. Files are kept and can be accessed via `path`.")
    await check_and_show_next_zip(c, cb.message.chat.id, uid)

def is_archive_file(filepath: Path) -> bool:
    ext = filepath.suffix.lower()
    return ext in ['.zip', '.rar', '.7z', '.tar', '.gz', '.bz2', '.xz']

async def execute_zip_download_and_extract(c, m, url=None, local_path=None):
    uid = m.from_user.id
    status_msg = await c.send_message(m.chat.id, "Downloading Queue Item..." if url else "Processing Local Archive...", reply_markup=progress_keyboard())
    
    safe_name = f"zip_dl_{uid}_{int(time.time())}"
    if url:
        original_name = await get_filename_from_url(url)
        safe_name = re.sub(r"[\\/*?\"<>|:]", "_", original_name)
        if len(safe_name) > 100:
            ext = Path(safe_name).suffix
            safe_name = safe_name[:100 - len(ext)] + ext
    elif local_path:
        safe_name = Path(local_path).name
            
    tmp_in = TMP / f"zip_{uid}_{int(time.time())}_{safe_name}"
    
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    
    try:
        ok, err = False, None
        original_name_pass = url.split("/")[-1] if url else None
        if local_path:
            shutil.copy(local_path, tmp_in)
            original_name_pass = tmp_in.name
            ok = True
        elif url:
            original_name_pass = await get_filename_from_url(url)
            if is_drive_url(url):
                fid = extract_drive_id(url)
                if fid: ok, err = await download_drive_file(fid, tmp_in, status_msg, cancel_event, original_name=original_name_pass)
            else:
                ok, err = await download_url_generic(url, tmp_in, status_msg, cancel_event, original_name=original_name_pass)
        else: # Telegram File
            original_name_pass = m.video.file_name if m.video else (m.document.file_name if m.document else "telegram_file")
            start_t = time.time()
            async def dl_prog(current, total):
                if cancel_event.is_set():
                    c.stop_transmission()
                await progress_callback(current, total, "Downloading...", status_msg, start_t, original_name=original_name_pass)
            await m.download(file_name=str(tmp_in), progress=dl_prog)
            ok = True
            
        if not ok or not tmp_in.exists():
            raise Exception(f"Download Failed: {err}")
            
        if not is_archive_file(tmp_in):
            await status_msg.edit("Non-archive file detected. Queueing for direct upload...", reply_markup=None)
            ZIP_READY_LIST.setdefault(uid, []).append({
                'root_dir': None,
                'files_to_upload': [tmp_in]
            })
            await check_and_show_next_zip(c, m.chat.id, uid)
            return

        await status_msg.edit("Extracting Archive file...", reply_markup=progress_keyboard())
        ext_dir = TMP / f"zip_ext_{uid}_{int(time.time())}"
        ext_dir.mkdir(parents=True, exist_ok=True)
        
        start_t = time.time()
        
        # General extraction logic with extended support and error catch
        try:
            ext = tmp_in.suffix.lower()
            if ext == '.zip':
                with zipfile.ZipFile(tmp_in, 'r') as zip_ref:
                    total_size = sum(info.file_size for info in zip_ref.infolist())
                    extracted_size = 0
                    for info in zip_ref.infolist():
                        if cancel_event.is_set(): break
                        await asyncio.to_thread(zip_ref.extract, info, ext_dir)
                        extracted_size += info.file_size
                        await progress_callback(extracted_size, total_size, "Extracting ZIP...", status_msg, start_t)
            elif ext == '.rar' and 'rarfile' in globals():
                with rarfile.RarFile(tmp_in, 'r') as rar_ref:
                    total_size = sum(info.file_size for info in rar_ref.infolist())
                    extracted_size = 0
                    for info in rar_ref.infolist():
                        if cancel_event.is_set(): break
                        await asyncio.to_thread(rar_ref.extract, info, ext_dir)
                        extracted_size += info.file_size
                        await progress_callback(extracted_size, total_size, "Extracting RAR...", status_msg, start_t)
            elif ext == '.7z' and 'py7zr' in globals():
                with py7zr.SevenZipFile(tmp_in, mode='r') as sz_ref:
                    await asyncio.to_thread(sz_ref.extractall, path=ext_dir)
                    await status_msg.edit("Extracting 7Z... Please wait.", reply_markup=progress_keyboard())
            elif ext in ['.tar', '.gz', '.bz2', '.xz']:
                with tarfile.open(tmp_in, 'r:*') as tar_ref:
                    await asyncio.to_thread(tar_ref.extractall, path=ext_dir)
                    await status_msg.edit("Extracting TAR/GZ... Please wait.", reply_markup=progress_keyboard())
            elif 'Archive' in globals():
                await asyncio.to_thread(Archive(str(tmp_in)).extractall, str(ext_dir))
            elif 'patoolib' in globals():
                await asyncio.to_thread(patoolib.extract_archive, str(tmp_in), outdir=str(ext_dir))
            else:
                cmd = ["7z", "x", str(tmp_in), f"-o{ext_dir}", "-y"]
                process = await asyncio.create_subprocess_exec(*cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                await process.communicate()
        except Exception as e:
            logger.error(f"Archive Mode Error: {e}")
            await status_msg.edit(f"Extraction failed: {e}\nAdding the downloaded archive to list...", reply_markup=None)
            ZIP_READY_LIST.setdefault(uid, []).append({
                'root_dir': None,
                'files_to_upload': [tmp_in]
            })
            await check_and_show_next_zip(c, m.chat.id, uid)
            return
            
        # Recursive archive extraction
        found_zip = True
        while found_zip:
            found_zip = False
            for root, dirs, files in os.walk(ext_dir):
                for file in files:
                    if is_archive_file(Path(file)):
                        nested_zip_path = Path(root) / file
                        try:
                            n_ext = nested_zip_path.suffix.lower()
                            if n_ext == '.zip':
                                with zipfile.ZipFile(nested_zip_path, 'r') as nested_ref:
                                    n_total = sum(n_info.file_size for n_info in nested_ref.infolist())
                                    n_extr = 0
                                    n_start = time.time()
                                    for n_info in nested_ref.infolist():
                                        if cancel_event.is_set(): break
                                        await asyncio.to_thread(nested_ref.extract, n_info, root)
                                        n_extr += n_info.file_size
                                        await progress_callback(n_extr, n_total, f"Extracting Nested Archive: {file[:10]}...", status_msg, n_start)
                            elif n_ext == '.rar' and 'rarfile' in globals():
                                with rarfile.RarFile(nested_zip_path, 'r') as nested_ref:
                                    await asyncio.to_thread(nested_ref.extractall, root)
                            elif n_ext == '.7z' and 'py7zr' in globals():
                                with py7zr.SevenZipFile(nested_zip_path, mode='r') as sz_ref:
                                    await asyncio.to_thread(sz_ref.extractall, path=root)
                            elif n_ext in ['.tar', '.gz', '.bz2', '.xz']:
                                with tarfile.open(nested_zip_path, 'r:*') as tar_ref:
                                    await asyncio.to_thread(tar_ref.extractall, path=root)
                            elif 'Archive' in globals():
                                await asyncio.to_thread(Archive(str(nested_zip_path)).extractall, str(root))
                            elif 'patoolib' in globals():
                                await asyncio.to_thread(patoolib.extract_archive, str(nested_zip_path), outdir=str(root))
                            else:
                                cmd = ["7z", "x", str(nested_zip_path), f"-o{root}", "-y"]
                                process = await asyncio.create_subprocess_exec(*cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                                await process.communicate()
                                
                            nested_zip_path.unlink()
                            found_zip = True
                        except Exception as e:
                            logger.error(f"Nested Archive extraction error: {e}")
        
        tmp_in.unlink(missing_ok=True)
        
        all_files = []
        for root, dirs, files in os.walk(ext_dir):
            for f in files:
                all_files.append(Path(root) / f)
        all_files.sort(key=lambda x: x.name.lower())
        
        if not all_files:
            await status_msg.edit("No files found in the extracted archive.")
            shutil.rmtree(ext_dir, ignore_errors=True)
            return

        try:
            await status_msg.delete()
        except: pass

        ZIP_READY_LIST.setdefault(uid, []).append({
            'root_dir': ext_dir,
            'files_to_upload': all_files
        })
        await check_and_show_next_zip(c, m.chat.id, uid)
        
    except Exception as e:
        logger.error(f"Archive Mode Error: {e}")
        raise e
    finally:
        if cancel_event in TASKS.get(uid, []):
            TASKS[uid].remove(cancel_event)

# -----------------------------

# --- PATH NAVIGATOR FUNCTIONS ---
async def send_path_ui(c, chat_id, uid, msg_id=None):
    current = NAV_PATHS[uid]['current']
    try:
        items = list(current.iterdir())
        items.sort(key=lambda x: (not x.is_dir(), x.name.lower()))
    except Exception as e:
        items = []
    
    NAV_PATHS[uid]['items'] = items
    
    text_lines = [f"**File Manager**\n**Current Path:** `{current}`\n"]
    text_lines.append("**0.** ⬆️ Up")
    
    for i, item in enumerate(items, 1):
        name = item.name
        if item.is_dir():
            text_lines.append(f"**{i}.** 📁 `{name}`")
        else:
            text_lines.append(f"**{i}.** 📄 `{name}`")
            
    text_lines.append("\n**Options:**")
    text_lines.append("‣ Send `0` to go up.")
    text_lines.append("‣ Send a number to open a folder (e.g., `1`).")
    text_lines.append("‣ Send numbers to select files for upload (e.g., `2,3,5-8`).")
    text_lines.append("‣ Send `close` to exit manager.")
    
    full_text = "\n".join(text_lines)
    
    chunks = [full_text[i:i+4000] for i in range(0, len(full_text), 4000)]
    for idx, chunk in enumerate(chunks):
        if msg_id and idx == 0:
            try: await c.edit_message_text(chat_id, msg_id, chunk)
            except: await c.send_message(chat_id, chunk)
        else:
            await c.send_message(chat_id, chunk)

async def process_path_uploads(uid, c, m, files_to_upload):
    for fpath in files_to_upload:
        while uid in USER_QUEUE_PAUSED:
            await asyncio.sleep(1)
        original_name = fpath.name
        renamed_file = generate_new_filename(original_name)
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        try:
            status_msg = await c.send_message(m.chat.id, f"Uploading `{original_name}`...", reply_markup=progress_keyboard())
            USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            await sequential_upload_task(uid, c, m, fpath, renamed_file, status_msg.id, cancel_event, default_caption=original_name, original_caption=original_name, original_download_name=original_name)
        except Exception as e:
            logger.error(f"Path item upload error: {e}")
            USER_QUEUE_PAUSED.add(uid)
            markup = InlineKeyboardMarkup([
                [InlineKeyboardButton("Continue ▶️", callback_data="queue_continue"),
                 InlineKeyboardButton("Delete 🗑️", callback_data="queue_delete")]
            ])
            await c.send_message(m.chat.id, f"Upload Failed: {e}\nQueue Paused.", reply_markup=markup)
    await c.send_message(m.chat.id, "Path selected files queued/uploaded successfully.")

# ----------------------------------------

# --- CONVERT MODE LOGIC ---
async def handle_convert_input(c, m, url=None, file_info=None):
    uid = m.from_user.id
    status_msg = await m.reply_text("📥 Initializing file for conversion...", reply_markup=progress_keyboard())
    
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    
    try:
        original_name = "video.mp4"
        if url:
            original_name = await get_filename_from_url(url)
        elif file_info:
            original_name = file_info.file_name if file_info.file_name else "telegram_video.mp4"
            
        safe_name = re.sub(r"[\\/*?\"<>|:]", "_", original_name)
        tmp_in = TMP / f"cv_{uid}_{int(time.time())}_{safe_name}"
        
        ok = False
        if url:
            if is_drive_url(url):
                fid = extract_drive_id(url)
                if fid: ok, err = await download_drive_file(fid, tmp_in, status_msg, cancel_event, original_name=original_name)
            else:
                ok, err = await download_url_generic(url, tmp_in, status_msg, cancel_event, original_name=original_name)
            if not ok: raise Exception(f"Download Failed: {err}")
        elif file_info:
            start_t = time.time()
            async def dl_prog(current, total):
                if cancel_event.is_set(): c.stop_transmission()
                await progress_callback(current, total, "📥 Downloading to prepare convert...", status_msg, start_t, original_name=original_name)
            await m.download(file_name=str(tmp_in), progress=dl_prog)
            ok = True
            
        if cancel_event.is_set(): raise Exception("Cancelled by user.")
        
        await status_msg.edit("⚙️ Extracting metadata for Convert...", reply_markup=None)
        meta = await asyncio.to_thread(get_detailed_metadata, tmp_in)
        
        if meta['duration'] == 0:
            raise Exception("Could not determine duration/invalid video file.")

        session_id = f"cvs_{uid}_{int(time.time())}"
        ACTIVE_CONVERT_SESSION[uid] = session_id
        
        CONVERT_SESSIONS[session_id] = {
            'uid': uid,
            'path': tmp_in,
            'original_name': original_name,
            'meta': meta,
            'configs': [],
            'curr_res': None, 
            'curr_v_bitrate': meta['v_bitrate'],
            'curr_a_bitrate': 128000 if not meta['audio_streams'] else meta['audio_streams'][0]['bitrate'],
            'upload_original': False,
            'msg_id': status_msg.id,
            'source_message': m
        }
        
        text, markup = build_convert_ui(session_id)
        await status_msg.edit(text, reply_markup=markup, parse_mode=ParseMode.MARKDOWN)

    except Exception as e:
        logger.error(f"Convert Input Error: {e}")
        try: await status_msg.edit(f"Convert preparation failed: {e}")
        except: pass
        if 'tmp_in' in locals() and tmp_in.exists():
            tmp_in.unlink(missing_ok=True)
    finally:
        if cancel_event in TASKS.get(uid, []):
            TASKS[uid].remove(cancel_event)

@app.on_callback_query(filters.regex(r"^cv_(res|vb_minus|vb_plus|ab_minus|ab_plus|orig|next|ok)_"))
async def convert_cb_handler(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    parts = cb.data.split('_')
    
    if parts[1] in ('vb', 'ab'):
        action = f"{parts[1]}_{parts[2]}" 
        session_id = f"{parts[3]}_{parts[4]}_{parts[5]}"
    else:
        action = parts[1]
        session_id = f"{parts[2]}_{parts[3]}_{parts[4]}"
        
    session = CONVERT_SESSIONS.get(session_id)
    if not session or session['uid'] != uid:
        await cb.answer("Session expired or invalid.", show_alert=True)
        return

    if action == "res":
        val = parts[5]
        if val == "Orig":
            session['curr_res'] = None
        else:
            session['curr_res'] = int(val)
    elif action == "vb_minus":
        session['curr_v_bitrate'] = max(100000, session['curr_v_bitrate'] - 100000)
    elif action == "vb_plus":
        session['curr_v_bitrate'] += 100000
    elif action == "ab_minus":
        session['curr_a_bitrate'] = max(32000, session['curr_a_bitrate'] - 32000)
    elif action == "ab_plus":
        session['curr_a_bitrate'] += 32000
    elif action == "orig":
        session['upload_original'] = not session['upload_original']
    elif action == "next":
        # Save config
        session['configs'].append({
            'res': session['curr_res'],
            'v_bitrate': session['curr_v_bitrate'],
            'a_bitrate': session['curr_a_bitrate']
        })
        # Reset current UI state
        session['curr_res'] = None
        session['curr_v_bitrate'] = session['meta']['v_bitrate']
        session['curr_a_bitrate'] = 128000 if not session['meta']['audio_streams'] else session['meta']['audio_streams'][0]['bitrate']
        await cb.answer("Configuration saved! Add another.", show_alert=True)
    elif action == "ok":
        ACTIVE_CONVERT_SESSION.pop(uid, None)
        # Save current config too
        session['configs'].append({
            'res': session['curr_res'],
            'v_bitrate': session['curr_v_bitrate'],
            'a_bitrate': session['curr_a_bitrate']
        })
        await cb.answer("Starting conversions...", show_alert=False)
        asyncio.create_task(execute_conversions(session_id, c))
        return

    text, markup = build_convert_ui(session_id)
    try: await cb.message.edit_text(text, reply_markup=markup, parse_mode=ParseMode.MARKDOWN)
    except: pass

async def execute_conversions(session_id, client):
    session = CONVERT_SESSIONS.pop(session_id, None)
    if not session: return
    
    uid = session['uid']
    in_path = session['path']
    original_name = session['original_name']
    configs = session['configs']
    meta = session['meta']
    msg = session['source_message']
    status_msg_id = session['msg_id']
    
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg_id] = cancel_event

    try:
        for idx, config in enumerate(configs, 1):
            if cancel_event.is_set(): break
            
            res_val = config['res']
            vb = config['v_bitrate']
            ab = config['a_bitrate']
            
            out_ext = in_path.suffix if in_path.suffix else ".mp4"
            res_str = f"{res_val}p" if res_val else "OrigRes"
            out_name = f"[Convert_{res_str}_{vb//1000}k] {original_name}"
            out_path = TMP / f"cv_out_{uid}_{int(time.time())}_{idx}{out_ext}"
            
            try:
                await client.edit_message_text(
                    msg.chat.id, status_msg_id, 
                    f"⚙️ **Converting {idx}/{len(configs)}**\nRes: `{res_str}` | Vid: `{vb//1000}k` | Aud: `{ab//1000}k`\nOriginal: `{original_name}`",
                    reply_markup=progress_keyboard()
                )
            except: pass
            
            cmd = ["ffmpeg", "-y", "-i", str(in_path), "-map", "0:v", "-map", "0:a?", "-map", "0:s?"]
            
            if res_val:
                cmd.extend(["-vf", f"scale=w=-2:h={res_val}"])
                
            orig_v_kbps = meta['v_bitrate']
            
            # Fast convert if target bitrate is higher/equal, else standard convert to preserve quality
            if vb >= orig_v_kbps:
                cmd.extend(["-c:v", "libx264", "-preset", "ultrafast", "-threads", "0", "-b:v", str(vb)])
            else:
                cmd.extend(["-c:v", "libx264", "-b:v", str(vb)])
            
            # Map multiple audios and apply same bitrate to all
            cmd.extend(["-c:a", "aac"])
            for a_idx in range(len(meta['audio_streams'])):
                cmd.extend([f"-b:a:{a_idx}", str(ab)])
                
            cmd.extend(["-c:s", "copy", "-progress", "pipe:1", "-nostats", str(out_path)])
            
            process = await asyncio.create_subprocess_exec(
                *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
            )
            
            start_t = time.time()
            dummy_status = type('obj', (object,), {'chat': type('obj', (object,), {'id': msg.chat.id}), 'id': status_msg_id, 'edit_text': lambda text, reply_markup: client.edit_message_text(msg.chat.id, status_msg_id, text, reply_markup=reply_markup)})
            
            while True:
                if cancel_event.is_set():
                    process.terminate()
                    break
                line = await process.stdout.readline()
                if not line: break
                line = line.decode('utf-8').strip()
                if line.startswith("out_time_us="):
                    us_str = line.split("=")[1]
                    try:
                        if us_str != "N/A":
                            out_time_sec = int(us_str) / 1000000.0
                            action_txt = f"Converting {idx}/{len(configs)} [{res_str}]"
                            await progress_callback(out_time_sec, meta['duration'], action_txt, dummy_status, start_t, is_time_based=True, original_name=out_name)
                    except: pass
            await process.wait()
            
            if cancel_event.is_set(): raise Exception("Cancelled by user")
            
            if out_path.exists() and out_path.stat().st_size > 0:
                await sequential_upload_task(uid, client, msg, out_path, out_name, None, cancel_event, default_caption=out_name, original_caption=None, original_download_name=out_name)
            else:
                logger.error("FFmpeg convert output failed.")
                
        if session['upload_original'] and not cancel_event.is_set():
            out_name = generate_new_filename(original_name)
            await sequential_upload_task(uid, client, msg, in_path, out_name, None, cancel_event, default_caption=original_name, original_caption=None, original_download_name=original_name)
            in_path = None # prevent cleanup in finally block since sequential_upload handles it
            
    except Exception as e:
        logger.error(f"Execution conversions error: {e}")
        try: await client.edit_message_text(msg.chat.id, status_msg_id, f"Conversion Error: {e}")
        except: pass
    finally:
        try:
            if in_path and in_path.exists(): in_path.unlink()
            if cancel_event in TASKS.get(uid, []): TASKS[uid].remove(cancel_event)
            await client.delete_messages(msg.chat.id, status_msg_id)
        except: pass
# ----------------------------------------


# --- AUDIO ADD SYSTEM LOGIC ---
def parse_number_list(s):
    res = []
    parts = s.split(',')
    for p in parts:
        p = p.strip()
        if not p: continue
        if '-' in p:
            try:
                start, end = map(int, p.split('-'))
                if start <= end:
                    res.extend(range(start, end + 1))
                else:
                    res.extend(range(start, end - 1, -1))
            except: pass
        else:
            try: res.append(int(p))
            except: pass
    return res

def parse_custom_mapping(text):
    parts = text.split('=')
    if len(parts) < 2: return {}
    mappings = {}
    current_x_str = parts[0]
    for i in range(1, len(parts)):
        if i == len(parts) - 1:
            current_y_str = parts[i]
            next_x_str = ""
        else:
            match = re.search(r'(.*)[,\s]+([\d\s,\-]+)$', parts[i])
            if match:
                current_y_str = match.group(1)
                next_x_str = match.group(2)
            else:
                current_y_str = parts[i]
                next_x_str = ""
        list_x = parse_number_list(current_x_str)
        list_y = parse_number_list(current_y_str)
        for j in range(min(len(list_x), len(list_y))):
            mappings[list_x[j]] = list_y[j]
        current_x_str = next_x_str
    return mappings

async def execute_audio_add_download_and_extract(c, item):
    uid = item['uid']
    m = item['message']
    url = item.get('url')
    local_path = item.get('local_path')
    phase = item['phase']
    
    status_msg = await c.send_message(m.chat.id, "Downloading Audio Add Item...", reply_markup=progress_keyboard())
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    
    safe_name = f"aa_dl_{uid}_{int(time.time())}"
    tmp_in = TMP / f"aa_tmp_{uid}_{int(time.time())}_{safe_name}"
    
    try:
        ok = False
        original_name_pass = None
        if local_path:
            shutil.copy(local_path, tmp_in)
            original_name_pass = tmp_in.name
            ok = True
        elif url:
            original_name_pass = await get_filename_from_url(url)
            if is_drive_url(url):
                fid = extract_drive_id(url)
                if fid: ok, err = await download_drive_file(fid, tmp_in, status_msg, cancel_event, original_name=original_name_pass)
            else:
                ok, err = await download_url_generic(url, tmp_in, status_msg, cancel_event, original_name=original_name_pass)
        else:
            original_name_pass = m.video.file_name if m.video else (m.document.file_name if m.document else "telegram_file")
            start_t = time.time()
            async def dl_prog(current, total):
                if cancel_event.is_set(): c.stop_transmission()
                await progress_callback(current, total, "Downloading Audio Add file...", status_msg, start_t, original_name=original_name_pass)
            await m.download(file_name=str(tmp_in), progress=dl_prog)
            ok = True
            
        if not ok or not tmp_in.exists(): raise Exception("Download Failed")
        
        # Check if archive
        if is_archive_file(tmp_in):
            await status_msg.edit("Extracting Archive file...", reply_markup=progress_keyboard())
            ext_dir = TMP / f"aa_ext_{uid}_{int(time.time())}"
            ext_dir.mkdir(parents=True, exist_ok=True)
            start_t = time.time()
            
            try:
                ext = tmp_in.suffix.lower()
                if ext == '.zip':
                    with zipfile.ZipFile(tmp_in, 'r') as zip_ref:
                        total_size = sum(info.file_size for info in zip_ref.infolist())
                        extracted_size = 0
                        for info in zip_ref.infolist():
                            if cancel_event.is_set(): break
                            await asyncio.to_thread(zip_ref.extract, info, ext_dir)
                            extracted_size += info.file_size
                            await progress_callback(extracted_size, total_size, "Extracting ZIP...", status_msg, start_t)
                elif ext == '.rar' and 'rarfile' in globals():
                    with rarfile.RarFile(tmp_in, 'r') as rar_ref:
                        total_size = sum(info.file_size for info in rar_ref.infolist())
                        extracted_size = 0
                        for info in rar_ref.infolist():
                            if cancel_event.is_set(): break
                            await asyncio.to_thread(rar_ref.extract, info, ext_dir)
                            extracted_size += info.file_size
                            await progress_callback(extracted_size, total_size, "Extracting RAR...", status_msg, start_t)
                elif ext == '.7z' and 'py7zr' in globals():
                    with py7zr.SevenZipFile(tmp_in, mode='r') as sz_ref:
                        await asyncio.to_thread(sz_ref.extractall, path=ext_dir)
                elif ext in ['.tar', '.gz', '.bz2', '.xz']:
                    with tarfile.open(tmp_in, 'r:*') as tar_ref:
                        await asyncio.to_thread(tar_ref.extractall, path=ext_dir)
                elif 'Archive' in globals():
                    await asyncio.to_thread(Archive(str(tmp_in)).extractall, str(ext_dir))
                elif 'patoolib' in globals():
                    await asyncio.to_thread(patoolib.extract_archive, str(tmp_in), outdir=str(ext_dir))
                else:
                    cmd = ["7z", "x", str(tmp_in), f"-o{ext_dir}", "-y"]
                    process = await asyncio.create_subprocess_exec(*cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    await process.communicate()
            except Exception as e:
                logger.error(f"Archive Mode Error: {e}")
                
            found_zip = True
            while found_zip:
                found_zip = False
                for root, dirs, files in os.walk(ext_dir):
                    for file in files:
                        if is_archive_file(Path(file)):
                            nested_zip_path = Path(root) / file
                            try:
                                n_ext = nested_zip_path.suffix.lower()
                                if n_ext == '.zip':
                                    with zipfile.ZipFile(nested_zip_path, 'r') as nested_ref:
                                        await asyncio.to_thread(nested_ref.extractall, root)
                                elif n_ext == '.rar' and 'rarfile' in globals():
                                    with rarfile.RarFile(nested_zip_path, 'r') as nested_ref:
                                        await asyncio.to_thread(nested_ref.extractall, root)
                                elif n_ext == '.7z' and 'py7zr' in globals():
                                    with py7zr.SevenZipFile(nested_zip_path, mode='r') as sz_ref:
                                        await asyncio.to_thread(sz_ref.extractall, path=root)
                                elif n_ext in ['.tar', '.gz', '.bz2', '.xz']:
                                    with tarfile.open(nested_zip_path, 'r:*') as tar_ref:
                                        await asyncio.to_thread(tar_ref.extractall, path=root)
                                elif 'Archive' in globals():
                                    await asyncio.to_thread(Archive(str(nested_zip_path)).extractall, str(root))
                                elif 'patoolib' in globals():
                                    await asyncio.to_thread(patoolib.extract_archive, str(nested_zip_path), outdir=str(root))
                                else:
                                    cmd = ["7z", "x", str(nested_zip_path), f"-o{root}", "-y"]
                                    process = await asyncio.create_subprocess_exec(*cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                                    await process.communicate()
                                nested_zip_path.unlink()
                                found_zip = True
                            except Exception as e:
                                logger.error(f"Nested Archive extraction error: {e}")

            tmp_in.unlink(missing_ok=True)
            
            video_exts = {".mp4", ".mkv", ".avi", ".mov", ".flv", ".wmv", ".webm"}
            found_vids = []
            for root, dirs, files in os.walk(ext_dir):
                for f in files:
                    if Path(f).suffix.lower() in video_exts:
                        found_vids.append(Path(root) / f)
            found_vids.sort(key=lambda x: x.name.lower())
            
            if phase == 1: AUDIO_ADD_STATE[uid]['list1'].extend(found_vids)
            else: AUDIO_ADD_STATE[uid]['list2'].extend(found_vids)
            
            await status_msg.edit(f"Extracted {len(found_vids)} videos and added to List {phase}.")
        else:
            if phase == 1: AUDIO_ADD_STATE[uid]['list1'].append(tmp_in)
            else: AUDIO_ADD_STATE[uid]['list2'].append(tmp_in)
            await status_msg.edit(f"File added to List {phase}.")
            
    except Exception as e:
        logger.error(f"Audio Add Extract Error: {e}")
        try: await status_msg.edit(f"Error processing item: {e}")
        except: pass
    finally:
        if cancel_event in TASKS.get(uid, []): TASKS[uid].remove(cancel_event)
        async def ad(m_obj):
            await asyncio.sleep(4)
            try: await m_obj.delete()
            except: pass
        asyncio.create_task(ad(status_msg))

async def audio_add_worker(uid, c):
    while uid in AUDIO_ADD_QUEUES and not AUDIO_ADD_QUEUES[uid].empty():
        item = await AUDIO_ADD_QUEUES[uid].get()
        try:
            queue_msg = item.get('queue_msg')
            if queue_msg:
                try: await queue_msg.delete()
                except: pass
            await execute_audio_add_download_and_extract(c, item)
        except Exception as e:
            logger.error(f"Audio Add Worker Error: {e}")
        finally:
            AUDIO_ADD_QUEUES[uid].task_done()
    if uid in AUDIO_ADD_WORKERS: del AUDIO_ADD_WORKERS[uid]

async def show_audio_add_lists(c, chat_id, uid):
    state = AUDIO_ADD_STATE.get(uid)
    if not state: return
    l1 = state['list1']
    l2 = state['list2']
    
    text_lines = ["**List 1 (Target Videos):**"]
    for i, f in enumerate(l1, 1):
        text_lines.append(f"{i}. `{f.name}`")
    
    text_lines.append("\n**List 2 (Source Audios):**")
    for i, f in enumerate(l2, 1):
        text_lines.append(f"{i}. `{f.name}`")
        
    text_lines.append("\n**Options:**")
    text_lines.append("‣ Reply with custom mapping like `1=4, 3=2, 5-10=3,5,7-15`")
    text_lines.append("‣ Or click **Upload All 🚀** to auto map 1:1, 2:2 serially.")
    
    full_text = "\n".join(text_lines)
    
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("Upload All 🚀", callback_data="aa_uploadall")],
        [InlineKeyboardButton("Cancel ❌", callback_data="aa_cancel")]
    ])
    
    chunks = [full_text[i:i+4000] for i in range(0, len(full_text), 4000)]
    for idx, chunk in enumerate(chunks):
        reply_markup = markup if idx == len(chunks) - 1 else None
        msg = await c.send_message(chat_id, chunk, reply_markup=reply_markup)
        state['ui_msgs'].append(msg.id)
        await asyncio.sleep(0.3)

async def show_audio_selection_ui(c, chat_id, uid):
    state = AUDIO_ADD_STATE.get(uid)
    if not state: return
    
    msgs_to_del = state.get('ui_msgs', [])
    try: await c.delete_messages(chat_id, msgs_to_del)
    except: pass
    state['ui_msgs'] = []
    
    mapping = state['mapping']
    list1 = state['list1']
    list2 = state['list2']
    
    status_msg = await c.send_message(chat_id, "Analyzing audio tracks for mapped items... please wait.")
    
    max_tracks_found = 0
    
    for t_idx, s_idx in mapping.items():
        if t_idx - 1 < 0 or t_idx - 1 >= len(list1) or s_idx - 1 < 0 or s_idx - 1 >= len(list2):
            continue
        s_file = list2[s_idx - 1]
        
        tracks = await asyncio.to_thread(get_audio_tracks_ffprobe, s_file)
        state['source_audios'][s_idx] = tracks
        state['selected_audios'][t_idx] = []
        if len(tracks) > max_tracks_found:
            max_tracks_found = len(tracks)
            
    try: await status_msg.delete()
    except: pass
    
    # Send pair messages
    for t_idx, s_idx in mapping.items():
        if t_idx not in state['selected_audios']: continue
        t_file = list1[t_idx - 1]
        s_file = list2[s_idx - 1]
        tracks = state['source_audios'][s_idx]
        sel_list = state['selected_audios'][t_idx]
        
        txt = f"**Video {t_idx}**\n**Target:** `{t_file.name}`\n**Source:** `{s_file.name}`\nSelect Audio Tracks:"
        
        kb = []
        row = []
        for i, trk in enumerate(tracks):
            is_sel = i in sel_list
            mark = "✅" if is_sel else "❌"
            lang = trk['language']
            btn = InlineKeyboardButton(f"Track {i+1}: {lang} {mark}", callback_data=f"aa_sel_{uid}_{t_idx}_{i}")
            row.append(btn)
            if len(row) == 2:
                kb.append(row)
                row = []
        if row: kb.append(row)
        
        msg = await c.send_message(chat_id, txt, reply_markup=InlineKeyboardMarkup(kb))
        state['ui_msgs'].append(msg.id)
        await asyncio.sleep(0.3)
        
    # Send Control Message
    ctrl_txt = "**Global Controls:**\nSelect a track to apply globally to all videos, or click Done to start muxing."
    ctrl_kb = []
    c_row = []
    for i in range(max_tracks_found):
        btn = InlineKeyboardButton(f"Select All Track {i+1}", callback_data=f"aa_selall_{uid}_{i}")
        c_row.append(btn)
        if len(c_row) == 2:
            ctrl_kb.append(c_row)
            c_row = []
    if c_row: ctrl_kb.append(c_row)
    
    ctrl_kb.append([InlineKeyboardButton("Done ✅", callback_data=f"aa_done_{uid}")])
    
    msg = await c.send_message(chat_id, ctrl_txt, reply_markup=InlineKeyboardMarkup(ctrl_kb))
    state['ui_msgs'].append(msg.id)

@app.on_callback_query(filters.regex(r"^aa_(cancel|yes|no|uploadall|sel|selall|done)"))
async def audio_add_cb_handler(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    parts = cb.data.split('_')
    action = parts[1]
    
    state = AUDIO_ADD_STATE.get(uid)
    if not state:
        await cb.answer("Audio Add Session expired or invalid.", show_alert=True)
        return
        
    if action == "cancel":
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("Yes, Clear Data ✅", callback_data="aa_yes")],
            [InlineKeyboardButton("No, Go Back ❌", callback_data="aa_no")]
        ])
        await cb.message.edit_text("Are you sure you want to cancel and clear all data?", reply_markup=kb)
        
    elif action == "yes":
        msgs = state.get('ui_msgs', [])
        try: await c.delete_messages(cb.message.chat.id, msgs)
        except: pass
        AUDIO_ADD_STATE.pop(uid, None)
        AUDIO_ADD_MODE.discard(uid)
        await cb.message.edit_text("Audio Add Session Cleared. Mode Turned OFF.")
        
    elif action == "no":
        await cb.message.delete()
        
    elif action == "uploadall":
        l1 = state['list1']
        l2 = state['list2']
        for i in range(1, min(len(l1), len(l2)) + 1):
            state['mapping'][i] = i
        state['phase'] = 4
        await cb.answer("Auto Mapping 1:1 applied.")
        await show_audio_selection_ui(c, cb.message.chat.id, uid)
        
    elif action == "sel":
        t_idx = int(parts[3])
        track_idx = int(parts[4])
        
        sel_list = state['selected_audios'].get(t_idx, [])
        if track_idx in sel_list:
            sel_list.remove(track_idx)
        else:
            sel_list.append(track_idx)
            
        s_idx = state['mapping'][t_idx]
        tracks = state['source_audios'][s_idx]
        
        kb = []
        row = []
        for i, trk in enumerate(tracks):
            is_sel = i in sel_list
            mark = "✅" if is_sel else "❌"
            lang = trk['language']
            btn = InlineKeyboardButton(f"Track {i+1}: {lang} {mark}", callback_data=f"aa_sel_{uid}_{t_idx}_{i}")
            row.append(btn)
            if len(row) == 2:
                kb.append(row)
                row = []
        if row: kb.append(row)
        
        try: await cb.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup(kb))
        except: pass
        
    elif action == "selall":
        track_idx = int(parts[3])
        for t_idx, s_idx in state['mapping'].items():
            s_tracks = state['source_audios'].get(s_idx, [])
            if track_idx < len(s_tracks):
                if track_idx not in state['selected_audios'][t_idx]:
                    state['selected_audios'][t_idx].append(track_idx)
                    
        await cb.answer(f"Track {track_idx+1} selected for all eligible videos! Click Done.", show_alert=True)
        # Note: we are not refreshing all individual messages to prevent flood wait. The answer alert is enough feedback.
        
    elif action == "done":
        state['phase'] = 5
        await cb.answer("Starting Muxing and Upload Process...", show_alert=False)
        msgs = state.get('ui_msgs', [])
        try: await c.delete_messages(cb.message.chat.id, msgs)
        except: pass
        state['ui_msgs'] = []
        asyncio.create_task(execute_audio_add_muxing(uid, c, cb.message))

async def execute_audio_add_muxing(uid, c, m):
    state = AUDIO_ADD_STATE.get(uid)
    if not state: return
    
    mapping = state.get('mapping', {})
    list1 = state.get('list1', [])
    list2 = state.get('list2', [])
    selected = state.get('selected_audios', {})
    
    status_msg = await m.reply_text("Starting Audio Add Muxing...", reply_markup=progress_keyboard())
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    
    try:
        total_items = len(mapping)
        curr = 0
        for target_idx, source_idx in mapping.items():
            if cancel_event.is_set(): break
            curr += 1
            
            t_idx_0 = target_idx - 1
            s_idx_0 = source_idx - 1
            if t_idx_0 < 0 or t_idx_0 >= len(list1) or s_idx_0 < 0 or s_idx_0 >= len(list2):
                continue
            
            t_file = list1[t_idx_0]
            s_file = list2[s_idx_0]
            
            if not t_file.exists() or not s_file.exists(): continue
            
            sel_tracks = selected.get(target_idx, [])
            if not sel_tracks:
                continue 
                
            target_name = t_file.name
            out_name = generate_new_filename(target_name)
            if not out_name.lower().endswith(".mkv"):
                out_name = Path(out_name).stem + ".mkv"
            
            out_path = TMP / f"aa_{uid}_{int(time.time())}_{out_name}"
            
            t_meta = await asyncio.to_thread(get_detailed_metadata, t_file)
            num_t_audios = len(t_meta.get('audio_streams', []))
            
            cmd = ["ffmpeg", "-y", "-i", str(t_file), "-i", str(s_file)]
            cmd.extend(["-map", "0:v", "-map", "0:a?", "-map", "0:s?"])
            
            s_audio_metadata = state['source_audios'].get(source_idx, [])
            
            for rel_idx in sel_tracks:
                if rel_idx < len(s_audio_metadata):
                    abs_stream_idx = s_audio_metadata[rel_idx]['stream_index']
                    cmd.extend(["-map", f"1:{abs_stream_idx}"])
            
            cmd.extend(["-c", "copy"])
            
            cmd.extend(["-disposition:a:0", "default"])
            
            for i in range(len(sel_tracks)):
                cmd.extend([f"-disposition:a:{num_t_audios + i}", "none"])
                
            cmd.extend(["-progress", "pipe:1", "-nostats", str(out_path)])
            
            try: await status_msg.edit(f"Muxing {curr}/{total_items}...\nTarget: `{target_name}`", reply_markup=progress_keyboard())
            except: pass
            
            process = await asyncio.create_subprocess_exec(
                *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
            )
            
            start_t = time.time()
            while True:
                if cancel_event.is_set():
                    process.terminate()
                    break
                line = await process.stdout.readline()
                if not line: break
                line = line.decode('utf-8').strip()
                if line.startswith("out_time_us="):
                    us_str = line.split("=")[1]
                    try:
                        if us_str != "N/A":
                            out_time_sec = int(us_str) / 1000000.0
                            await progress_callback(out_time_sec, t_meta['duration'], f"Muxing {curr}/{total_items}...", status_msg, start_t, is_time_based=True, original_name=target_name)
                    except: pass
            await process.wait()
            
            if cancel_event.is_set(): raise Exception("Cancelled by user")
            
            if process.returncode == 0 and out_path.exists() and out_path.stat().st_size > 0:
                await sequential_upload_task(uid, c, m, out_path, out_name, None, cancel_event, default_caption=target_name, original_caption=None, original_download_name=target_name)
            else:
                logger.error("Audio Add Muxing failed.")
                
    except Exception as e:
        logger.error(f"Audio Add Execution Error: {e}")
        try: await status_msg.edit(f"Error: {e}")
        except: pass
    finally:
        if cancel_event in TASKS.get(uid, []): TASKS[uid].remove(cancel_event)
        try: await status_msg.delete()
        except: pass
        AUDIO_ADD_MODE.discard(uid)
        AUDIO_ADD_STATE.pop(uid, None)
# ----------------------------------------


@app.on_message(filters.text & filters.private)
async def text_handler(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    text = m.text.strip()
    
    if text.isdigit() and uid in ACTIVE_CONVERT_SESSION:
        session_id = ACTIVE_CONVERT_SESSION[uid]
        session = CONVERT_SESSIONS.get(session_id)
        if session:
            kbps = int(text)
            if kbps > 0:
                session['curr_v_bitrate'] = kbps * 1000
                try:
                    t_ui, markup = build_convert_ui(session_id)
                    await c.edit_message_text(m.chat.id, session['msg_id'], t_ui, reply_markup=markup, parse_mode=ParseMode.MARKDOWN)
                except: pass
            try: await m.delete()
            except: pass
            return

    text_lower = text.lower()
    
    if text_lower == "next" and uid in AUDIO_ADD_MODE:
        state = AUDIO_ADD_STATE.get(uid)
        if not state: return
        
        if uid in AUDIO_ADD_QUEUES and not AUDIO_ADD_QUEUES[uid].empty():
            await m.reply_text("⏳ Please wait for the current downloads/extractions to finish...")
            return
            
        if state['phase'] == 1:
            state['phase'] = 2
            await m.reply_text("✅ Phase 1 Complete (Target Videos).\nNow send/forward the SOURCE videos/links/zips (the files containing the audio you want to add).\nOnce done, type `next` again.")
        elif state['phase'] == 2:
            state['phase'] = 3
            await show_audio_add_lists(c, m.chat.id, uid)
        return

    if text_lower != "next" and uid in AUDIO_ADD_MODE and AUDIO_ADD_STATE.get(uid, {}).get('phase') == 3:
        if "=" in text:
            mapping = parse_custom_mapping(text)
            if mapping:
                AUDIO_ADD_STATE[uid]['mapping'] = mapping
                AUDIO_ADD_STATE[uid]['phase'] = 4
                await show_audio_selection_ui(c, m.chat.id, uid)
                return
            else:
                await m.reply_text("Invalid mapping format. Example: `1=4, 3=2, 5-10=3,5,7-15`")
                return

    if text_lower == "path":
        NAV_PATHS[uid] = {"current": TMP, "items": []}
        await send_path_ui(c, m.chat.id, uid)
        return

    # Handle all for zip
    if uid in ZIP_DOWNLOAD_MODE:
        if text_lower == "all":
            AUTO_UPLOAD_ALL.add(uid)
            await m.reply_text("Auto Upload All is now **ON**.")
            # Trigger if one is waiting
            if uid in ZIP_NAV_STATE and ZIP_NAV_STATE[uid]['state'] == 'awaiting_selection':
                files = ZIP_NAV_STATE[uid]['files_to_upload']
                final_order = list(range(1, len(files) + 1))
                await process_zip_uploads(c, m, uid, final_order)
            return
        elif text_lower in ["all f", "all off"]:
            AUTO_UPLOAD_ALL.discard(uid)
            await m.reply_text("Auto Upload All is now **OFF**.")
            return

    if text_lower == "clear":
        cleared = False
        ZIP_READY_LIST.pop(uid, None)
        if uid in ZIP_DL_QUEUES:
            while not ZIP_DL_QUEUES[uid].empty():
                try: 
                    item = ZIP_DL_QUEUES[uid].get_nowait()
                    if 'queue_msg' in item and item['queue_msg']:
                        try: await item['queue_msg'].delete()
                        except: pass
                    ZIP_DL_QUEUES[uid].task_done()
                except: pass
            cleared = True
        if uid in ZIP_NAV_STATE:
            ZIP_NAV_STATE.pop(uid)
            cleared = True
        if cleared:
            await m.reply_text("ZIP Download session and queue cleared. You can send a new link.")
        else:
            await m.reply_text("No active ZIP session to clear.")
        return

    if uid in ZIP_NAV_STATE:
        state = ZIP_NAV_STATE[uid]
        if state['state'] == 'awaiting_selection':
            state.setdefault('garbage_msgs', []).append(m.id)
            if text_lower.startswith('e '):
                try:
                    num = int(text_lower.split()[1])
                    files = state['files_to_upload']
                    if 1 <= num <= len(files):
                        file_to_extract = files[num-1]
                        if uid not in ZIP_DL_QUEUES:
                            ZIP_DL_QUEUES[uid] = asyncio.Queue()
                        queue_msg = await m.reply_text(f"Queued for manual extraction. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
                        await ZIP_DL_QUEUES[uid].put({'local_path': str(file_to_extract), 'message': m, 'queue_msg': queue_msg})
                        if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
                            ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
                        return
                except Exception as e:
                    err_msg = await m.reply_text("Invalid format for manual extract. Use `e 1`.")
                    state['garbage_msgs'].append(err_msg.id)
                    return
            
            files = state['files_to_upload']
            selected_indices = []
            try:
                parts = text.split(',')
                for p in parts:
                    p = p.strip()
                    if not p: continue
                    if '-' in p:
                        start, end = map(int, p.split('-'))
                        for i in range(start, end + 1):
                            if i not in selected_indices: selected_indices.append(i)
                    else:
                        num = int(p)
                        if num not in selected_indices: selected_indices.append(num)
            except Exception:
                err_msg = await m.reply_text("Invalid format. Use numbers, ranges like 1,3,5,8-15, or `e 1` for manual extract.")
                state['garbage_msgs'].append(err_msg.id)
                return
            
            valid_selected = [i for i in selected_indices if 1 <= i <= len(files)]
            all_indices = list(range(1, len(files) + 1))
            unselected = [i for i in all_indices if i not in valid_selected]
            final_order = valid_selected + unselected
            
            await process_zip_uploads(c, m, uid, final_order)
            return
    
    if uid in NAV_PATHS:
        if text_lower == 'close':
            NAV_PATHS.pop(uid)
            await m.reply_text("File Manager closed.")
            return
        if text_lower == '0':
            current = NAV_PATHS[uid]['current']
            if current != TMP:
                NAV_PATHS[uid]['current'] = current.parent
            await send_path_ui(c, m.chat.id, uid)
            return
            
        selected_indices = []
        try:
            parts = text.split(',')
            for p in parts:
                p = p.strip()
                if not p: continue
                if '-' in p:
                    start, end = map(int, p.split('-'))
                    for i in range(start, end + 1):
                        if i not in selected_indices: selected_indices.append(i)
                else:
                    num = int(p)
                    if num not in selected_indices: selected_indices.append(num)
        except Exception:
            pass
            
        if selected_indices:
            items = NAV_PATHS[uid].get('items', [])
            if len(selected_indices) == 1 and 1 <= selected_indices[0] <= len(items):
                idx = selected_indices[0] - 1
                selected_item = items[idx]
                if selected_item.is_dir():
                    NAV_PATHS[uid]['current'] = selected_item
                    await send_path_ui(c, m.chat.id, uid)
                    return
                    
            files_to_upload = []
            for i in selected_indices:
                if 1 <= i <= len(items):
                    item = items[i-1]
                    if item.is_file():
                        files_to_upload.append(item)
            
            if files_to_upload:
                await m.reply_text(f"Starting upload for {len(files_to_upload)} selected files from path...")
                asyncio.create_task(process_path_uploads(uid, c, m, files_to_upload))
                return

    is_batch_cmd = False
    if text_lower in ["on", "off", "no", "d", "cap"]:
        is_batch_cmd = True
    elif text_lower.startswith("ok"):
        is_batch_cmd = True

    if is_batch_cmd:
        if uid in EDIT_CAPTION_MODE:
            if text_lower == "cap":
                if uid not in MULTI_GROUP_BATCH_MODE:
                    return
                if uid in USE_ORIGINAL_CAPTION_IN_MULTI_GROUP:
                    USE_ORIGINAL_CAPTION_IN_MULTI_GROUP.discard(uid)
                    await m.reply_text("Original Caption Mode OFF. Now saved caption will be used.")
                else:
                    USE_ORIGINAL_CAPTION_IN_MULTI_GROUP.add(uid)
                    await m.reply_text("Original Caption Mode ON. Original video caption will be used without modification.")
            elif text_lower == "on":
                BATCH_CAPTION_MODE.add(uid)
                BATCH_DATA[uid] = []
                USE_ORIGINAL_CAPTION_IN_MULTI_GROUP.discard(uid)
                if uid in MULTI_GROUP_BATCH_MODE:
                    MULTI_GROUP_BATCH_MODE.discard(uid)
                await m.reply_text("Batch Caption Mode ON. Forward videos to save file IDs.")
            elif text_lower == "no":
                MULTI_GROUP_BATCH_MODE.add(uid)
                MULTI_GROUP_DATA[uid] = [[]]
                if uid in BATCH_CAPTION_MODE:
                    BATCH_CAPTION_MODE.discard(uid)
                await m.reply_text("Multi-group Batch Mode ON. Forward/send videos for the 1st group.")
            elif text_lower == "d":
                if uid in MULTI_GROUP_BATCH_MODE:
                    if uid not in MULTI_GROUP_DATA:
                        MULTI_GROUP_DATA[uid] = [[]]
                    MULTI_GROUP_DATA[uid].append([])
                    group_num = len(MULTI_GROUP_DATA[uid])
                    await m.reply_text(f"New group created (Group {group_num}). Forward/send videos for this group.")
            elif text_lower == "off":
                BATCH_CAPTION_MODE.discard(uid)
                BATCH_DATA.pop(uid, None)
                MULTI_GROUP_BATCH_MODE.discard(uid)
                MULTI_GROUP_DATA.pop(uid, None)
                BATCH_STATUS_MSG.pop(uid, None)
                MULTI_GROUP_DONE_MSG.pop(uid, None)
                USE_ORIGINAL_CAPTION_IN_MULTI_GROUP.discard(uid)
                await m.reply_text("Batch Caption Mode & Multi-group Mode OFF. Forwarded videos will have caption changed directly.")
            elif text_lower.startswith("ok"):
                if uid in MULTI_GROUP_BATCH_MODE and uid in MULTI_GROUP_DATA and MULTI_GROUP_DATA[uid]:
                    parts = text_lower.split()
                    group_weights = {}
                    if len(parts) > 1:
                        for p in parts[1:]:
                            if '=' in p:
                                try:
                                    g, w = map(int, p.split('='))
                                    group_weights[g] = w
                                except ValueError:
                                    pass

                    groups = MULTI_GROUP_DATA[uid]
                    total_items = sum(len(g) for g in groups)
                    await m.reply_text(f"Multi-group processing started for {len(groups)} groups ({total_items} items total)...")
                    
                    queues = [list(g) for g in groups]
                    
                    while any(queues):
                        for idx, q in enumerate(queues):
                            group_num = idx + 1
                            weight = group_weights.get(group_num, 1)
                            
                            for _ in range(weight):
                                if not q:
                                    break
                                item = q.pop(0)
                                await handle_caption_only_upload_with_file(c, item['message'], item['file_info'])
                                await asyncio.sleep(0.5)
                    
                    MULTI_GROUP_DATA[uid] = [[]]
                    if uid in BATCH_STATUS_MSG:
                        try:
                            await c.delete_messages(m.chat.id, BATCH_STATUS_MSG[uid])
                        except: pass
                        BATCH_STATUS_MSG.pop(uid, None)
                    if uid in MULTI_GROUP_DONE_MSG:
                        try: await c.delete_messages(m.chat.id, MULTI_GROUP_DONE_MSG[uid])
                        except: pass
                        MULTI_GROUP_DONE_MSG.pop(uid, None)
                    
                    complete_msg = await m.reply_text("Multi-group batch processing complete.")
                    async def auto_delete():
                        await asyncio.sleep(5) 
                        try: await complete_msg.delete()
                        except: pass
                    asyncio.ensure_future(auto_delete())
                elif uid in BATCH_CAPTION_MODE and uid in BATCH_DATA and BATCH_DATA[uid]:
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
            elif text_lower.startswith("ok"):
                if uid in BATCH_UPLOAD_MODE and uid in BATCH_DATA and BATCH_DATA[uid]:
                    items = BATCH_DATA[uid]
                    await m.reply_text(f"Batch processing started for {len(items)} items...")
                    
                    for item in items:
                        if item.get('is_url'):
                            await add_to_queue(uid, c, item['message'], item['original_name'], is_url=True, url=item['url'])
                        else:
                            await add_to_queue(uid, c, item['message'], item['original_name'], is_url=False, original_caption=item['message'].caption)
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

    if uid in SET_CAPTION_REQUEST:
        SET_CAPTION_REQUEST.discard(uid)
        USER_CAPTIONS[uid] = text
        USER_COUNTERS.pop(uid, None) 
        await m.reply_text("Your caption has been saved. Uploaded videos will use this caption.")
        return

    if m.reply_to_message and m.reply_to_message.id in PENDING_AUDIO_ORDERS:
        prompt_message_id = m.reply_to_message.id
        file_data = PENDING_AUDIO_ORDERS.get(prompt_message_id)
        
        if file_data['uid'] != uid:
             await m.reply_text("You cannot provide orders for this file.")
             return

        tracks = file_data['tracks']
        try:
            new_order_str = [x.strip() for x in text.split(',') if x.strip()]
            num_tracks_in_file = len(tracks)
            
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

            asyncio.create_task(
                handle_audio_remux(
                    c, m, file_data['path'], 
                    file_data['original_name'], 
                    new_stream_map, 
                    messages_to_delete=[prompt_message_id, m.id],
                    default_caption=file_data.get('default_caption')
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

    if text.startswith("http://") or text.startswith("https://"):
        url = text
        if uid in CONVERT_MODE:
            await handle_convert_input(c, m, url=url)
            return
            
        if uid in AUDIO_ADD_MODE:
            phase = AUDIO_ADD_STATE[uid]['phase']
            if phase in (1, 2):
                if uid not in AUDIO_ADD_QUEUES: AUDIO_ADD_QUEUES[uid] = asyncio.Queue()
                queue_msg = await m.reply_text(f"Queue item added to Audio Add List {phase}. Position: {AUDIO_ADD_QUEUES[uid].qsize() + 1}")
                await AUDIO_ADD_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg, 'phase': phase, 'uid': uid})
                if uid not in AUDIO_ADD_WORKERS or AUDIO_ADD_WORKERS[uid].done():
                    AUDIO_ADD_WORKERS[uid] = asyncio.create_task(audio_add_worker(uid, c))
                return
            
        if uid in ZIP_DOWNLOAD_MODE:
            if uid not in ZIP_DL_QUEUES:
                ZIP_DL_QUEUES[uid] = asyncio.Queue()
            queue_msg = await m.reply_text(f"Queue item added. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
            await ZIP_DL_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg})
            if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
                ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
            return
            
        if uid in YT_DLP_MODE or is_youtube_url(url):
            await fetch_youtube_formats(c, m, url)
            return

        original_name = await get_filename_from_url(url)
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
            status_text = f"{count} items saved for batch upload.\nLast: `{original_name}`"
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
    uid = m.from_user.id
    
    if uid in CONVERT_MODE:
        await handle_convert_input(c, m, url=url)
        return
        
    if uid in AUDIO_ADD_MODE:
        phase = AUDIO_ADD_STATE[uid]['phase']
        if phase in (1, 2):
            if uid not in AUDIO_ADD_QUEUES: AUDIO_ADD_QUEUES[uid] = asyncio.Queue()
            queue_msg = await m.reply_text(f"Queue item added to Audio Add List {phase}. Position: {AUDIO_ADD_QUEUES[uid].qsize() + 1}")
            await AUDIO_ADD_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg, 'phase': phase, 'uid': uid})
            if uid not in AUDIO_ADD_WORKERS or AUDIO_ADD_WORKERS[uid].done():
                AUDIO_ADD_WORKERS[uid] = asyncio.create_task(audio_add_worker(uid, c))
            return
    
    if uid in ZIP_DOWNLOAD_MODE:
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Queue item added. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
        await ZIP_DL_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg})
        if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
            ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
        return
        
    if uid in YT_DLP_MODE or is_youtube_url(url):
        await fetch_youtube_formats(c, m, url)
        return

    original_name = await get_filename_from_url(url)
    
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
        status_text = f"{count} items saved for batch upload.\nLast: `{original_name}`"
        await update_batch_status(c, m, uid, status_text)
    else:
        await add_to_queue(uid, c, m, original_name, is_url=True, url=url)

async def download_and_process_generic(c, m, url, status_msg, cancel_event_passed=None):
    uid = m.from_user.id
    cancel_event = cancel_event_passed or asyncio.Event()
    if not cancel_event_passed:
        TASKS.setdefault(uid, []).append(cancel_event)
    
    if status_msg:
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
        
    try:
        fname = await get_filename_from_url(url)
        safe_name = re.sub(r"[\\/*?\"<>|:]", "_", fname)

        if len(safe_name) > 100:
            ext = Path(safe_name).suffix
            safe_name = safe_name[:100 - len(ext)] + ext

        video_exts = {".mp4", ".mkv", ".avi", ".mov", ".flv", ".wmv", ".webm"}
        if not any(safe_name.lower().endswith(ext) for ext in video_exts):
            safe_name += ".mp4"

        tmp_in = TMP / f"dl_{uid}_{int(datetime.now().timestamp())}_{safe_name}"
        ok, err = False, None
        
        if is_drive_url(url):
            fid = extract_drive_id(url)
            if not fid:
                await status_msg.edit("Google Drive ID not found.")
                if cancel_event in TASKS.get(uid, []): TASKS[uid].remove(cancel_event)
                return
            ok, err = await download_drive_file(fid, tmp_in, status_msg, cancel_event=cancel_event, original_name=fname)
        else:
            ok, err = await download_url_generic(url, tmp_in, status_msg, cancel_event=cancel_event, original_name=fname)

        if not ok:
            raise Exception(f"Download Failed: {err}")

        await status_msg.edit("Download complete. Uploading...", reply_markup=None)
        renamed_file = generate_new_filename(safe_name)
        
        if uid in MKV_AUDIO_CHANGE_MODE:
            try:
                await status_msg.edit("Checking file for audio track analysis...", reply_markup=progress_keyboard())
                audio_tracks = await asyncio.to_thread(get_audio_tracks_ffprobe, tmp_in)
                
                if not audio_tracks:
                    await status_msg.edit("No audio tracks found in this video or FFprobe failed. Uploading directly...")
                    asyncio.create_task(
                        sequential_upload_task(uid, c, m, tmp_in, renamed_file, status_msg.id, cancel_event, default_caption=safe_name, original_caption=fname, original_download_name=fname)
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
                    'tracks': audio_tracks,
                    'default_caption': safe_name
                }
                return 
            except Exception as e:
                logger.error(f"URL Audio track analysis error: {e}")
                await status_msg.edit(f"Error analyzing audio tracks: {e}. Uploading directly...")
                asyncio.create_task(
                    sequential_upload_task(uid, c, m, tmp_in, renamed_file, status_msg.id, cancel_event, default_caption=safe_name, original_caption=fname, original_download_name=fname)
                )
                return

        asyncio.create_task(
            sequential_upload_task(uid, c, m, tmp_in, renamed_file, status_msg.id, cancel_event, default_caption=safe_name, original_caption=fname, original_download_name=fname)
        )
    except Exception as e:
        raise e
    finally:
        pass 

async def handle_caption_only_upload(c: Client, m: Message):
    file_info = m.video or m.document
    await handle_caption_only_upload_with_file(c, m, file_info)

async def handle_caption_only_upload_with_file(c: Client, m: Message, file_info):
    uid = m.from_user.id
    
    use_orig_cap = False
    final_caption_template = USER_CAPTIONS.get(uid)
    
    if not final_caption_template or uid in USE_ORIGINAL_CAPTION_IN_MULTI_GROUP:
        use_orig_cap = True
    
    if use_orig_cap:
        caption_to_use = m.caption or (file_info.file_name if file_info and file_info.file_name else "Video")
        caption_entities_to_use = m.caption_entities
    else:
        caption_to_use = final_caption_template
        caption_entities_to_use = None

    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    
    try:
        status_msg = await m.reply_text("Editing caption...", reply_markup=progress_keyboard())
    except Exception:
        status_msg = await m.reply_text("Editing caption...", reply_markup=progress_keyboard())
        
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    
    try:
        source_message = m
        
        if not file_info:
            try:
                await status_msg.edit("This is not a video or document file.")
            except Exception:
                await m.reply_text("This is not a video or document file.")
            return
        
        if use_orig_cap:
            final_caption = make_bold(caption_to_use)
            final_entities = caption_entities_to_use
        else:
            final_caption = make_bold(process_dynamic_caption(uid, caption_to_use))
            final_entities = None
        
        if file_info.file_id:
            try:
                parse_mode_arg = ParseMode.MARKDOWN

                if source_message.video or (file_info and getattr(file_info, 'duration', 0) > 0): 
                    await c.send_video(
                        chat_id=m.chat.id,
                        video=file_info.file_id,
                        caption=final_caption,
                        caption_entities=final_entities,
                        thumb=file_info.thumbs[0].file_id if file_info.thumbs else None,
                        duration=file_info.duration,
                        width=file_info.width,       
                        height=file_info.height,     
                        supports_streaming=True,
                        parse_mode=parse_mode_arg
                    )
                else:
                    await c.send_document(
                        chat_id=m.chat.id,
                        document=file_info.file_id,
                        file_name=file_info.file_name,
                        caption=final_caption,
                        caption_entities=final_entities,
                        thumb=file_info.thumbs[0].file_id if file_info.thumbs else None,
                        parse_mode=parse_mode_arg
                    )
                try:
                    await status_msg.delete() 
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
        
    file_info = m.video or m.document
    original_name = file_info.file_name if file_info and file_info.file_name else f"file_{file_info.file_unique_id}"

    if uid in CONVERT_MODE:
        await handle_convert_input(c, m, file_info=file_info)
        return
        
    if uid in AUDIO_ADD_MODE:
        phase = AUDIO_ADD_STATE[uid]['phase']
        if phase in (1, 2):
            if uid not in AUDIO_ADD_QUEUES: AUDIO_ADD_QUEUES[uid] = asyncio.Queue()
            queue_msg = await m.reply_text(f"Queue item added to Audio Add List {phase}. Position: {AUDIO_ADD_QUEUES[uid].qsize() + 1}")
            await AUDIO_ADD_QUEUES[uid].put({'message': m, 'queue_msg': queue_msg, 'phase': phase, 'uid': uid, 'is_telegram_file': True})
            if uid not in AUDIO_ADD_WORKERS or AUDIO_ADD_WORKERS[uid].done():
                AUDIO_ADD_WORKERS[uid] = asyncio.create_task(audio_add_worker(uid, c))
            return

    if uid in ZIP_DOWNLOAD_MODE:
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Queue item added. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
        await ZIP_DL_QUEUES[uid].put({'message': m, 'queue_msg': queue_msg, 'is_telegram_file': True})
        if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
            ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
        return

    if uid in MKV_AUDIO_CHANGE_MODE:
        await handle_audio_change_file(c, m)
        return

    if uid in EDIT_CAPTION_MODE: 
        if uid in MULTI_GROUP_BATCH_MODE:
            if not file_info: 
                return
            
            if uid not in MULTI_GROUP_DATA or not MULTI_GROUP_DATA[uid]: 
                MULTI_GROUP_DATA[uid] = [[]]
            
            MULTI_GROUP_DATA[uid][-1].append({
                'message': m,
                'file_info': file_info
            })
            
            group_idx = len(MULTI_GROUP_DATA[uid])
            count_in_group = len(MULTI_GROUP_DATA[uid][-1])
            status_text = f"Group {group_idx}: {count_in_group} video file IDs saved.\nLast: `{original_name}`"
            markup = InlineKeyboardMarkup([[InlineKeyboardButton("Done ✅", callback_data="multi_group_done")]])
            
            if uid in MULTI_GROUP_DONE_MSG:
                try:
                    await c.delete_messages(m.chat.id, MULTI_GROUP_DONE_MSG[uid])
                except Exception:
                    pass
                    
            done_msg = await m.reply_text(status_text, reply_markup=markup)
            MULTI_GROUP_DONE_MSG[uid] = done_msg.id
            return
            
        if uid in BATCH_CAPTION_MODE:
            if not file_info: 
                return
            
            if uid not in BATCH_DATA: 
                BATCH_DATA[uid] = []
            
            BATCH_DATA[uid].append({
                'message': m,
                'file_info': file_info
            })
            
            count = len(BATCH_DATA[uid])
            status_text = f"{count} video file IDs saved.\nLast: `{original_name}`"
            await update_batch_status(c, m, uid, status_text)
            return

        await handle_caption_only_upload(c, m)
        return

    if uid in BATCH_UPLOAD_MODE:
        if uid not in BATCH_DATA: 
            BATCH_DATA[uid] = []
        BATCH_DATA[uid].append({
            'message': m,
            'original_name': original_name,
            'is_url': False
        })
        count = len(BATCH_DATA[uid])
        status_text = f"{count} files saved for batch upload.\nLast: `{original_name}`"
        await update_batch_status(c, m, uid, status_text)
        return

    await add_to_queue(uid, c, m, original_name, is_url=False, original_caption=m.caption)

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
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
        
        start_t = time.time()
        async def dl_prog(current, total):
            if cancel_event.is_set():
                c.stop_transmission()
            if status_msg:
                await progress_callback(current, total, "Downloading...", status_msg, start_t, original_name=original_name)
                
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
            'tracks': audio_tracks,
            'default_caption': original_name
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

async def handle_audio_remux(c: Client, m: Message, in_path: Path, original_name: str, new_stream_map: list, messages_to_delete: list = None, default_caption: str = None):
    uid = m.from_user.id
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    
    out_name = generate_new_filename(original_name)
    if not out_name.lower().endswith(".mkv"):
        out_name = Path(out_name).stem + ".mkv"
    
    asyncio.create_task(
        sequential_remux_upload_task(uid, c, m, in_path, out_name, new_stream_map, messages_to_delete, cancel_event, default_caption, original_download_name=original_name)
    )

async def sequential_remux_upload_task(uid, c, m, in_path, out_name, new_stream_map, messages_to_delete, cancel_event, default_caption=None, original_download_name=None):
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
            "-metadata", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:v", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:v", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:a", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:a", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:s", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:s", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-c", "copy",
            str(out_path)
        ]

        status_msg = None
        if messages_to_delete:
             pass

        try:
            status_msg = await m.reply_text("Changing audio track order (Remuxing)...", reply_markup=progress_keyboard())
            USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            
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

            await process_file_and_upload(c, m, out_path, target_name=out_name, original_download_name=original_download_name, messages_to_delete=all_messages_to_delete, cancel_event_passed=cancel_event, passed_uid=uid, default_caption=default_caption, original_caption_passed=default_caption) 

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
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    except Exception:
        status_msg = await m.reply_text("Downloading file for renaming...", reply_markup=progress_keyboard())
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    tmp_out = TMP / f"rename_{uid}_{int(datetime.now().timestamp())}_{new_name}"
    try:
        start_t = time.time()
        async def dl_prog(current, total):
            if cancel_event.is_set():
                c.stop_transmission()
            if status_msg:
                await progress_callback(current, total, "Downloading...", status_msg, start_t, original_name=new_name)
                
        await m.reply_to_message.download(file_name=str(tmp_out), progress=dl_prog)
        
        try:
            await status_msg.edit("Download complete, uploading with new name...", reply_markup=None)
        except Exception:
            await m.reply_text("Download complete, uploading with new name...", reply_markup=None)
        
        asyncio.create_task(
            sequential_upload_task(uid, c, m, tmp_out, new_name, status_msg.id, cancel_event, default_caption=new_name, original_caption=new_name, original_download_name=new_name)
        )
    except Exception as e:
        await m.reply_text(f"Rename error: {e}")
    finally:
        pass

@app.on_callback_query(filters.regex("cancel_single"))
async def cancel_single_cb(c, cb):
    uid = cb.from_user.id
    msg_id = cb.message.id
    
    ACTIVE_CONVERT_SESSION.pop(uid, None)
    
    if msg_id in PENDING_AUDIO_ORDERS:
        file_data = PENDING_AUDIO_ORDERS.pop(msg_id)
        if file_data['uid'] == uid:
            try: Path(file_data['path']).unlink(missing_ok=True)
            except Exception: pass
            
            if uid in USER_TASK_EVENTS and msg_id in USER_TASK_EVENTS[uid]:
                USER_TASK_EVENTS[uid][msg_id].set()
                
            await cb.answer("Audio change process cancelled.", show_alert=True)
            try: await cb.message.delete()
            except: pass
            return

    if uid in USER_TASK_EVENTS and msg_id in USER_TASK_EVENTS[uid]:
        USER_TASK_EVENTS[uid][msg_id].set()
        await cb.answer("Task cancelled.", show_alert=True)
        try: await cb.message.delete()
        except: pass
    else:
        await cb.answer("Task not found or already completed.", show_alert=True)

@app.on_callback_query(filters.regex("cancel_all"))
async def cancel_all_cb(c, cb):
    uid = cb.from_user.id
    count = 0
    
    ACTIVE_CONVERT_SESSION.pop(uid, None)
    
    if uid in ZIP_DL_QUEUES:
        while not ZIP_DL_QUEUES[uid].empty():
            try: 
                item = ZIP_DL_QUEUES[uid].get_nowait()
