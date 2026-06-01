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
from flask import Flask, render_template_string, Response, request, stream_with_context, send_file
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
import uuid

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
SET_FILENAME_REQUEST = set() # New for filename
USER_CAPTIONS = {}
USER_FILENAMES = {} # New for filename
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
CONVERT_LOCKS = {} # To prevent CPU overload
CONVERT_BATCH_LIST = {} # For multiple videos batch conversion
# ----------------------------------

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

# --- NEW STATE FOR PATH NAVIGATOR & FLASK SERVER ---
NAV_PATHS = {} # uid -> {"current": Path, "items": list, "selected_file": Path}
DIRECT_LINKS = {} # uuid -> local file path
TG_FILE_STREAMS = {} # uuid -> {file_id, size, mime}
DOWNLOAD_ONLY_MODE = set()
# ------------------------------------------------

# --- YT-DLP STATE & MODES ---
YT_SESSIONS = {}
YT_DLP_MODE = set()
SAVED_YT_QUALITIES = {}
# --------------------

# --- NEW STATE FOR BATCH AUDIO ADD MODE ---
BATCH_AUDIO_MODE = set()
BATCH_AUDIO_STATE = {} # uid -> 'list1', 'list2', 'mapping', 'ui'
BATCH_AUDIO_LIST1 = {} # uid -> list of dicts: {'path': str, 'name': str}
BATCH_AUDIO_LIST2 = {} # uid -> list of dicts: {'path': str, 'name': str}
BATCH_AUDIO_MAPPING = {} # uid -> dict mapping pairs
BATCH_AUDIO_CURRENT_PAIR_IDX = {}
BATCH_AUDIO_TRACK_CONFIGS = {}
BATCH_AUDIO_UI_MSG = {}
BATCH_AUDIO_DOWNLOAD_TASKS = {}
BATCH_AUDIO_QUEUES = {}
BATCH_AUDIO_WORKERS = {}
# ------------------------------------------

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

def get_unique_filename(directory: Path, filename: str) -> Path:
    """Ensures no file collision by appending numbers if the file exists."""
    base = Path(filename).stem
    ext = Path(filename).suffix
    counter = 1
    new_path = directory / filename
    while new_path.exists():
        new_path = directory / f"{base} {counter:02d}{ext}"
        counter += 1
    return new_path

def advance_dynamic_counters(uid):
    if uid not in USER_COUNTERS:
        USER_COUNTERS[uid] = {'uploads': 0, 'episode_numbers': {}, 'dynamic_counters': {}, 're_options_count': 0}
        
    USER_COUNTERS[uid]['uploads'] += 1

    if USER_COUNTERS[uid]['re_options_count'] > 0:
        if (USER_COUNTERS[uid]['uploads'] - 1) % USER_COUNTERS[uid]['re_options_count'] == 0 and USER_COUNTERS[uid]['uploads'] > 1:
            for key in USER_COUNTERS[uid]['dynamic_counters']:
                USER_COUNTERS[uid]['dynamic_counters'][key]['value'] += 1
    elif USER_COUNTERS[uid]['uploads'] > 1:
        for key in USER_COUNTERS[uid].get('dynamic_counters', {}):
             USER_COUNTERS[uid]['dynamic_counters'][key]['value'] += 1

def process_dynamic_caption(uid, caption_template, is_first_setup=False):
    if uid not in USER_COUNTERS:
        USER_COUNTERS[uid] = {'uploads': 0, 'episode_numbers': {}, 'dynamic_counters': {}, 're_options_count': 0}
        
    counter_matches = re.findall(r"\[\s*(\(?\d+\)?)\s*\]", caption_template)
    if USER_COUNTERS[uid]['uploads'] <= 1 or is_first_setup:
        for match in counter_matches:
            if match not in USER_COUNTERS[uid]['dynamic_counters']:
                has_paren = match.startswith('(') and match.endswith(')')
                clean_match = re.sub(r'[()]', '', match)
                USER_COUNTERS[uid]['dynamic_counters'][match] = {'value': int(clean_match), 'has_paren': has_paren}

    quality_match = re.search(r"\[re\s*\((.*?)\)\]", caption_template)
    if quality_match:
        options_str = quality_match.group(1)
        options = [opt.strip() for opt in options_str.split(',')]
        
        if not USER_COUNTERS[uid]['re_options_count']:
            USER_COUNTERS[uid]['re_options_count'] = len(options)
        
        current_index = max(0, (USER_COUNTERS[uid]['uploads'] - 1)) % len(options)
        current_quality = options[current_index]
        caption_template = caption_template.replace(quality_match.group(0), current_quality)

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

    return caption_template

def process_dynamic_text_no_increment(uid, caption_template):
    if uid not in USER_COUNTERS:
        return caption_template
    
    uploads = USER_COUNTERS[uid].get('uploads', 1)
    
    quality_match = re.search(r"\[re\s*\((.*?)\)\]", caption_template)
    if quality_match:
        options_str = quality_match.group(1)
        options = [opt.strip() for opt in options_str.split(',')]
        re_count = USER_COUNTERS[uid].get('re_options_count', len(options))
        current_index = (uploads - 1) % len(options) if uploads > 0 else 0
        current_quality = options[current_index]
        caption_template = caption_template.replace(quality_match.group(0), current_quality)

    for match, data in USER_COUNTERS[uid].get('dynamic_counters', {}).items():
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

    return caption_template


def generate_new_filename(original_name: str, uid: int = None) -> str:
    """Generates the new standardized filename while preserving the original extension."""
    file_path = Path(original_name)
    file_ext = file_path.suffix.lower()
    
    file_ext = "." + file_ext.lstrip('.') if file_ext and file_ext != '.' else ".mp4"
    
    if uid and uid in USER_FILENAMES:
        base_name = process_dynamic_caption(uid, USER_FILENAMES[uid], is_first_setup=True)
    else:
        base_name = "[@TA_HD_Anime] Telegram Channel"
        
    return base_name + file_ext

def get_dynamic_filename(uid, original_name):
    file_path = Path(original_name)
    file_ext = file_path.suffix.lower()
    file_ext = "." + file_ext.lstrip('.') if file_ext and file_ext != '.' else ".mp4"
    
    if uid in USER_FILENAMES:
        base_name = process_dynamic_text_no_increment(uid, USER_FILENAMES[uid])
    else:
        base_name = "[@TA_HD_Anime] Telegram Channel"
    return base_name + file_ext

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
    if orig_h > 0 or True: 
        res_buttons.append(InlineKeyboardButton(f"✅ Orig" if res is None else "Orig", callback_data=f"cv_res_{session_id}_Orig"))
        for r in [2160, 1440, 1080, 720, 480, 360, 240, 144]:
            res_buttons.append(InlineKeyboardButton(f"✅ {r}p" if res == r else f"{r}p", callback_data=f"cv_res_{session_id}_{r}"))
    
    keyboard = []
    for i in range(0, len(res_buttons), 4):
        keyboard.append(res_buttons[i:i+4])
        
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
    batch_audio_status = "✅ ON" if uid in BATCH_AUDIO_MODE else "❌ OFF"
    dl_only_status = "✅ ON" if uid in DOWNLOAD_ONLY_MODE else "❌ OFF"
    
    waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
    waiting_status = f" ({waiting_count} orders pending)" if waiting_count > 0 else ""
    
    keyboard = [
        [InlineKeyboardButton(f"Convert Mode {convert_status}", callback_data="toggle_convert_mode")],
        [InlineKeyboardButton(f"MKV Audio Change Mode {audio_status}{waiting_status}", callback_data="toggle_audio_mode")],
        [InlineKeyboardButton(f"Batch Audio Add Mode {batch_audio_status}", callback_data="toggle_batch_audio_mode")],
        [InlineKeyboardButton(f"Edit Caption Mode {caption_status}", callback_data="toggle_caption_mode")],
        [InlineKeyboardButton(f"YT-DLP Mode {yt_dlp_status}", callback_data="toggle_ytdlp_mode")],
        [InlineKeyboardButton(f"ZIP Download Mode {zip_status}", callback_data="toggle_zip_mode")],
        [InlineKeyboardButton(f"Download Only Mode {dl_only_status}", callback_data="toggle_dl_only_mode")]
    ]
    return InlineKeyboardMarkup(keyboard)

def get_audio_tracks_ffprobe(file_path: Path) -> list:
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
    if not text: return text
    text_str = str(text).strip()
    if not text_str.startswith("**"):
        text_str = f"**{text_str}"
    if not text_str.endswith("**"):
        text_str = f"{text_str}**"
    return text_str

PROGRESS_CACHE = {}

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
            status_msg = await m.reply_text(f"Queue item added for `{title}` ({res}p)...")
        else:
            status_msg = await m.reply_text(f"Queue item added for `{original_name}`...", reply_markup=progress_keyboard())
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
    try:
        connector = aiohttp.TCPConnector(limit=0, family=socket.AF_INET, use_dns_cache=True, ttl_dns_cache=300)
        async with aiohttp.ClientSession(connector=connector) as sess:
            async with sess.head(url, allow_redirects=True, timeout=10) as resp:
                cd = resp.headers.get('Content-Disposition')
                if cd:
                    fname_match = re.findall(r'filename\*?=(?:UTF-8\'\')?["\']?([^"\';\n]+)', cd, re.IGNORECASE)
                    if fname_match:
                        extracted_name = urllib.parse.unquote(fname_match[0])
                        if len(extracted_name) > 200:
                            ext = Path(extracted_name).suffix
                            extracted_name = extracted_name[:200 - len(ext)] + ext
                        return extracted_name
    except Exception:
        pass
        
    fname = url.split("/")[-1].split("?")[0]
    fname = urllib.parse.unquote(fname)
    
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
        BotCommand("file_name_save", "Save dynamic file name (admin only)"),
        BotCommand("view_filename", "View saved file name format (admin only)"),
        BotCommand("del_filename", "Delete saved file name format (admin only)"),
        BotCommand("rename", "Rename replied video (admin only)"),
        BotCommand("batch_audio_add", "Batch MKV audio change mode (admin only)"),
        BotCommand("mkv_video_audio_change", "Single MKV audio track change mode (admin only)"),
        BotCommand("yt_dlp", "Toggle YT-DLP mode for all URLs (admin only)"),
        BotCommand("convert", "Convert Video/Audio quality, bitrate & format (admin only)"),
        BotCommand("create_post", "Create new post (admin only)"), 
        BotCommand("download_only", "Download to temporary folder & generate direct links (admin only)"),
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
    if uid not in USER_UPLOAD_LOCKS:
        USER_UPLOAD_LOCKS[uid] = asyncio.Lock()
    
    async with USER_UPLOAD_LOCKS[uid]:
        if cancel_event.is_set():
            if tmp_path.exists(): tmp_path.unlink()
            return
        await process_file_and_upload(client, message, tmp_path, target_name=renamed_file, original_download_name=original_download_name, messages_to_delete=[status_msg_id] if status_msg_id else [], cancel_event_passed=cancel_event, passed_uid=uid, default_caption=default_caption, original_caption_passed=original_caption)

async def process_queue_handler(uid, client):
    queue = USER_QUEUES[uid]
    while not queue.empty():
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
                
                out_tmpl = str(get_unique_filename(TMP, f"yt_{uid}_{int(datetime.now().timestamp())}_{res}p_{safe_title}.%(ext)s"))
                
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
                    renamed_file = get_dynamic_filename(uid, original_name)
                    
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
                file_info = m.video or m.document
                tmp_path = get_unique_filename(TMP, original_name)
                
                try:
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

                    renamed_file = get_dynamic_filename(uid, original_name)
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
    
    if uid in USER_WORKERS: del USER_WORKERS[uid]
    if uid in USER_QUEUES: del USER_QUEUES[uid]


@app.on_callback_query(filters.regex("refresh_btn"))
async def refresh_btn_cb(c, cb):
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
            
    if uid in USER_WORKERS:
        USER_WORKERS[uid].cancel()
        del USER_WORKERS[uid]
        
    if uid in BATCH_AUDIO_QUEUES:
        while not BATCH_AUDIO_QUEUES[uid].empty():
            try: BATCH_AUDIO_QUEUES[uid].get_nowait(); BATCH_AUDIO_QUEUES[uid].task_done()
            except: pass
    if uid in BATCH_AUDIO_WORKERS:
        BATCH_AUDIO_WORKERS[uid].cancel()
        del BATCH_AUDIO_WORKERS[uid]

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
        status_msg = await m.reply_text(f"Queue item added for `{title}` ({res}p)...")
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
        "/file_name_save - Save custom file name format (admin only)\n"
        "/view_filename - View saved file name format (admin only)\n"
        "/del_filename - Delete saved file name format (admin only)\n"
        "/rename <newname.ext> - Rename replied video (admin only)\n"
        "/batch_audio_add - Batch MKV audio change mode (admin only)\n"
        "/mkv_video_audio_change - Single MKV audio track change mode (admin only)\n"
        "/yt_dlp - Toggle YT-DLP mode for all URLs (admin only)\n"
        "/convert - Convert Video/Audio quality, bitrate & format (admin only)\n"
        "/create_post - Create new post (admin only)\n" 
        "/download_only - Download to temporary folder & generate direct links (admin only)\n"
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
    SET_FILENAME_REQUEST.clear()
    USER_FILENAMES.clear()
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
    CONVERT_ZIP_MODE.clear()
    ACTIVE_CONVERT_SESSION.clear()
    for s_id in list(CONVERT_SESSIONS.keys()):
        try:
            CONVERT_SESSIONS[s_id]['path'].unlink(missing_ok=True)
        except: pass
    CONVERT_SESSIONS.clear()
    CONVERT_BATCH_LIST.clear()
    BATCH_AUDIO_MODE.clear()
    BATCH_AUDIO_STATE.clear()
    BATCH_AUDIO_LIST1.clear()
    BATCH_AUDIO_LIST2.clear()
    CREATE_POST_MODE.clear()
    POST_CREATION_STATE.clear()
    BATCH_CAPTION_MODE.clear()
    BATCH_UPLOAD_MODE.clear()
    BATCH_DATA.clear()
    BATCH_STATUS_MSG.clear()
    DOWNLOAD_ONLY_MODE.clear()
    
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
    
    if uid in BATCH_AUDIO_QUEUES:
        while not BATCH_AUDIO_QUEUES[uid].empty():
            try: BATCH_AUDIO_QUEUES[uid].get_nowait(); BATCH_AUDIO_QUEUES[uid].task_done()
            except: pass
    for worker in BATCH_AUDIO_WORKERS.values():
        worker.cancel()
    BATCH_AUDIO_WORKERS.clear()
    
    NAV_PATHS.clear()
    YT_SESSIONS.clear()
    YT_DLP_MODE.clear()
    SAVED_YT_QUALITIES.clear()
    DIRECT_LINKS.clear()
    TG_FILE_STREAMS.clear()
    
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

@app.on_message(filters.command("download_only") & filters.private)
async def download_only_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    if uid in DOWNLOAD_ONLY_MODE:
        DOWNLOAD_ONLY_MODE.discard(uid)
        await m.reply_text("Download Only Mode **OFF**.")
    else:
        DOWNLOAD_ONLY_MODE.add(uid)
        out_dir = TMP / f"download_only_{uid}"
        out_dir.mkdir(parents=True, exist_ok=True)
        await m.reply_text("Download Only Mode **ON**.\nFiles, Links, ZIPs will only be downloaded and extracted here.\nSend `link` to get direct download links.\nSend `t` to generate instant streaming link for a Telegram file without downloading.")

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
        ACTIVE_CONVERT_SESSION.pop(uid, None)
        CONVERT_BATCH_LIST.pop(uid, None)
        await m.reply_text("Convert Mode **OFF**.")
    else:
        CONVERT_MODE.add(uid)
        CONVERT_BATCH_LIST[uid] = []
        await m.reply_text("Convert Mode **ON**.\nSend/Forward video, audio, link, or zip.\nSend multiple items, type `next` when done, just like Batch Audio Mode.")

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
        
        out = get_unique_filename(TMP, f"post_img_{uid}.jpg")
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
        out = get_unique_filename(TMP, f"thumb_{uid}.jpg")
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

# File name save handlers
@app.on_message(filters.command("file_name_save") & filters.private)
async def set_filename_prompt(c, m: Message):
    if not is_admin(m.from_user.id):
        await m.reply_text("You are not authorized to use this command.")
        return
    SET_FILENAME_REQUEST.add(m.from_user.id)
    await m.reply_text(
        "Provide a file name format. You can use these codes:\n"
        "1. **Number Increment:** `[01]`, `[(01)]`\n"
        "2. **Quality Cycle:** `[re (480p, 720p)]`\n"
        "3. **Conditional Text:** `[TEXT (XX)]`"
    )

@app.on_message(filters.command("view_filename") & filters.private)
async def view_filename_cmd(c, m: Message):
    if not is_admin(m.from_user.id): return
    uid = m.from_user.id
    filename = USER_FILENAMES.get(uid)
    if filename:
        await m.reply_text(f"Your saved file name:\n\n`{filename}`", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("Delete File Name 🗑️", callback_data="delete_filename")]]))
    else:
        await m.reply_text("You don't have any saved file name. Use /file_name_save to set one.")

@app.on_callback_query(filters.regex("delete_filename"))
async def delete_filename_cb(c, cb):
    uid = cb.from_user.id
    if not is_admin(uid): return
    if uid in USER_FILENAMES:
        USER_FILENAMES.pop(uid)
        await cb.message.edit_text("Your file name format has been deleted.")
    else:
        await cb.answer("You don't have any saved file name.", show_alert=True)

# Handler to toggle edit caption mode
@app.on_message(filters.command("edit_caption_mode") & filters.private)
async def toggle_edit_caption_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return

    if uid in EDIT_CAPTION_MODE:
        EDIT_CAPTION_MODE.discard(uid)
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

# --- HANDLER: /batch_audio_add ---
@app.on_message(filters.command("batch_audio_add") & filters.private)
async def batch_audio_add_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return

    if uid in BATCH_AUDIO_MODE:
        BATCH_AUDIO_MODE.discard(uid)
        BATCH_AUDIO_STATE.pop(uid, None)
        for item in BATCH_AUDIO_LIST1.get(uid, []):
            try: Path(item['path']).unlink(missing_ok=True)
            except: pass
        for item in BATCH_AUDIO_LIST2.get(uid, []):
            try: Path(item['path']).unlink(missing_ok=True)
            except: pass
        BATCH_AUDIO_LIST1.pop(uid, None)
        BATCH_AUDIO_LIST2.pop(uid, None)
        if uid in BATCH_AUDIO_QUEUES:
            while not BATCH_AUDIO_QUEUES[uid].empty():
                try: BATCH_AUDIO_QUEUES[uid].get_nowait(); BATCH_AUDIO_QUEUES[uid].task_done()
                except: pass
        await m.reply_text("Batch Audio Add Mode **OFF**.")
    else:
        BATCH_AUDIO_MODE.add(uid)
        BATCH_AUDIO_STATE[uid] = 'list1'
        BATCH_AUDIO_LIST1[uid] = []
        BATCH_AUDIO_LIST2[uid] = []
        await m.reply_text("Batch Audio Add Mode **ON**.\nSend Base Videos / Links / ZIP files (List 1).\n*(Type next when done, or type list to view/delete)*")

# --- HANDLER: /mkv_video_audio_change ---
@app.on_message(filters.command("mkv_video_audio_change") & filters.private)
async def toggle_audio_change_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return

    if uid in MKV_AUDIO_CHANGE_MODE:
        MKV_AUDIO_CHANGE_MODE.discard(uid)
        for msg_id in list(PENDING_AUDIO_ORDERS.keys()):
            if PENDING_AUDIO_ORDERS[msg_id]['uid'] == uid:
                file_data = PENDING_AUDIO_ORDERS.pop(msg_id)
                try: Path(file_data['path']).unlink(missing_ok=True)
                except: pass
        await m.reply_text("MKV audio change mode has been **TURNED OFF**.")
    else:
        MKV_AUDIO_CHANGE_MODE.add(uid)
        await m.reply_text("MKV audio change mode has been **TURNED ON**. Now send a **SINGLE MKV file** or video.\nFor multiple files mapping, use /batch_audio_add")

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
    batch_audio_status = "✅ ON" if uid in BATCH_AUDIO_MODE else "❌ OFF"
    dl_only_status = "✅ ON" if uid in DOWNLOAD_ONLY_MODE else "❌ OFF"
    
    waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
    waiting_status_text = f"{waiting_count} file(s) waiting for track order." if waiting_count > 0 else "No files are waiting."
    
    status_text = (
        "🤖 **Current Mode Status:**\n\n"
        f"1. **Convert Mode:** `{convert_status}`\n"
        f"   - *Task:* Change Quality/Bitrate of Videos/Audio interactively.\n\n"
        f"2. **MKV Audio Change Mode:** `{audio_status}`\n"
        f"   - *Task:* Single file track change.\n"
        f"   - *Status:* {waiting_status_text}\n\n"
        f"3. **Batch Audio Add Mode:** `{batch_audio_status}`\n"
        f"   - *Task:* Add audios to multiple base files via Lists.\n\n"
        f"4. **Edit Caption Mode:** `{caption_status}`\n"
        f"   - *Task:* Adds saved caption without changing rename or thumbnail of forwarded videos.\n\n"
        f"5. **YT-DLP Mode:** `{yt_dlp_status}`\n"
        f"6. **ZIP Download Mode:** `{zip_status}`\n"
        f"7. **Download Only Mode:** `{dl_only_status}`\n"
        "Click the buttons below to toggle modes."
    )
    
    await m.reply_text(status_text, reply_markup=mode_check_keyboard(uid), parse_mode=ParseMode.MARKDOWN)

# --- CALLBACK: Mode Toggle Buttons ---
@app.on_callback_query(filters.regex("toggle_(audio|caption|ytdlp|zip|convert|batch_audio|dl_only)_mode"))
async def mode_toggle_callback(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("You are not authorized.", show_alert=True)
        return

    action = cb.data
    
    if action == "toggle_audio_mode":
        if uid in MKV_AUDIO_CHANGE_MODE:
            MKV_AUDIO_CHANGE_MODE.discard(uid)
            for msg_id in list(PENDING_AUDIO_ORDERS.keys()):
                if PENDING_AUDIO_ORDERS[msg_id]['uid'] == uid:
                    file_data = PENDING_AUDIO_ORDERS.pop(msg_id)
                    try: Path(file_data['path']).unlink(missing_ok=True)
                    except: pass
            message = "MKV Audio Change Mode OFF."
        else:
            MKV_AUDIO_CHANGE_MODE.add(uid)
            message = "MKV Audio Change Mode ON."
            
    elif action == "toggle_caption_mode":
        if uid in EDIT_CAPTION_MODE:
            EDIT_CAPTION_MODE.discard(uid)
            BATCH_CAPTION_MODE.discard(uid)
            BATCH_DATA.pop(uid, None)
            MULTI_GROUP_BATCH_MODE.discard(uid)
            MULTI_GROUP_DATA.pop(uid, None)
            BATCH_STATUS_MSG.pop(uid, None)
            MULTI_GROUP_DONE_MSG.pop(uid, None)
            USE_ORIGINAL_CAPTION_IN_MULTI_GROUP.discard(uid)
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
            ZIP_READY_LIST.pop(uid, None)
            ZIP_NAV_STATE.pop(uid, None)
            AUTO_UPLOAD_ALL.discard(uid)
            if uid in ZIP_DL_QUEUES:
                while not ZIP_DL_QUEUES[uid].empty():
                    try: ZIP_DL_QUEUES[uid].get_nowait(); ZIP_DL_QUEUES[uid].task_done()
                    except: pass
            message = "ZIP Download Mode OFF."
        else:
            ZIP_DOWNLOAD_MODE.add(uid)
            message = "ZIP Download Mode ON."
            
    elif action == "toggle_dl_only_mode":
        if uid in DOWNLOAD_ONLY_MODE:
            DOWNLOAD_ONLY_MODE.discard(uid)
            message = "Download Only Mode OFF."
        else:
            DOWNLOAD_ONLY_MODE.add(uid)
            out_dir = TMP / f"download_only_{uid}"
            out_dir.mkdir(parents=True, exist_ok=True)
            message = "Download Only Mode ON."
            
    elif action == "toggle_convert_mode":
        if uid in CONVERT_MODE:
            CONVERT_MODE.discard(uid)
            CONVERT_ZIP_MODE.discard(uid)
            ACTIVE_CONVERT_SESSION.pop(uid, None)
            CONVERT_BATCH_LIST.pop(uid, None)
            message = "Convert Mode OFF."
        else:
            CONVERT_MODE.add(uid)
            CONVERT_BATCH_LIST[uid] = []
            message = "Convert Mode ON."
            
    elif action == "toggle_batch_audio_mode":
        if uid in BATCH_AUDIO_MODE:
            BATCH_AUDIO_MODE.discard(uid)
            BATCH_AUDIO_STATE.pop(uid, None)
            for item in BATCH_AUDIO_LIST1.get(uid, []):
                try: Path(item['path']).unlink(missing_ok=True)
                except: pass
            for item in BATCH_AUDIO_LIST2.get(uid, []):
                try: Path(item['path']).unlink(missing_ok=True)
                except: pass
            BATCH_AUDIO_LIST1.pop(uid, None)
            BATCH_AUDIO_LIST2.pop(uid, None)
            if uid in BATCH_AUDIO_QUEUES:
                while not BATCH_AUDIO_QUEUES[uid].empty():
                    try: BATCH_AUDIO_QUEUES[uid].get_nowait(); BATCH_AUDIO_QUEUES[uid].task_done()
                    except: pass
            message = "Batch Audio Add Mode OFF."
        else:
            BATCH_AUDIO_MODE.add(uid)
            BATCH_AUDIO_STATE[uid] = 'list1'
            BATCH_AUDIO_LIST1[uid] = []
            BATCH_AUDIO_LIST2[uid] = []
            message = "Batch Audio Add Mode ON."
            
    try:
        audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
        caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
        yt_dlp_status = "✅ ON" if uid in YT_DLP_MODE else "❌ OFF"
        zip_status = "✅ ON" if uid in ZIP_DOWNLOAD_MODE else "❌ OFF"
        convert_status = "✅ ON" if uid in CONVERT_MODE else "❌ OFF"
        batch_audio_status = "✅ ON" if uid in BATCH_AUDIO_MODE else "❌ OFF"
        dl_only_status = "✅ ON" if uid in DOWNLOAD_ONLY_MODE else "❌ OFF"
        
        waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
        waiting_status_text = f"{waiting_count} file(s) waiting for track order." if waiting_count > 0 else "No files are waiting."

        status_text = (
            "🤖 **Current Mode Status:**\n\n"
            f"1. **Convert Mode:** `{convert_status}`\n"
            f"   - *Task:* Change Quality/Bitrate of Videos/Audio interactively.\n\n"
            f"2. **MKV Audio Change Mode:** `{audio_status}`\n"
            f"   - *Task:* Single file track change.\n"
            f"   - *Status:* {waiting_status_text}\n\n"
            f"3. **Batch Audio Add Mode:** `{batch_audio_status}`\n"
            f"   - *Task:* Add audios to multiple base files via Lists.\n\n"
            f"4. **Edit Caption Mode:** `{caption_status}`\n"
            f"   - *Task:* Adds saved caption without changing rename or thumbnail of forwarded videos.\n\n"
            f"5. **YT-DLP Mode:** `{yt_dlp_status}`\n"
            f"6. **ZIP Download Mode:** `{zip_status}`\n"
            f"7. **Download Only Mode:** `{dl_only_status}`\n"
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
            await execute_zip_download_and_extract(c, task_data['message'], task_data.get('url'), task_data.get('local_path'), task_data.get('target_list'))
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
    
    chunks = [full_text[i:i+3500] for i in range(0, len(full_text), 3500)]
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
            break 
            
        fpath = files[idx - 1]
        if not fpath.exists(): continue
        original_name = fpath.name
        renamed_file = get_dynamic_filename(uid, original_name)
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        
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
    if ext in ['.zip', '.rar', '.7z', '.tar', '.gz', '.bz2', '.xz']:
        return True
    try:
        with open(filepath, 'rb') as f:
            header = f.read(4)
            if header.startswith(b'PK\x03\x04') or header.startswith(b'Rar!') or header.startswith(b'7z\xbc\xaf'):
                return True
    except: pass
    return False

async def execute_zip_download_and_extract(c, m, url=None, local_path=None, target_list=None):
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
            
    tmp_in = get_unique_filename(TMP, safe_name)
    
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    
    try:
        ok, err = False, None
        original_name_pass = safe_name
        if local_path:
            shutil.copy(local_path, tmp_in)
            original_name_pass = Path(local_path).name
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
                if cancel_event.is_set():
                    c.stop_transmission()
                await progress_callback(current, total, "Downloading...", status_msg, start_t, original_name=original_name_pass)
            await m.download(file_name=str(tmp_in), progress=dl_prog)
            ok = True
            
        if not ok or not tmp_in.exists():
            raise Exception(f"Download Failed: {err}")
            
        if not is_archive_file(tmp_in):
            await status_msg.edit("Non-archive file detected. Handling as direct video...", reply_markup=None)
            if target_list is not None:
                new_path = get_unique_filename(tmp_in.parent, original_name_pass)
                shutil.move(tmp_in, new_path)
                
                # Check target format
                if target_list is CONVERT_BATCH_LIST.get(uid):
                    target_list.append(new_path)
                    await status_msg.edit(f"File added to Convert list. Send `next` to configure.")
                else:
                    target_list.append({'path': str(new_path), 'name': original_name_pass})
                    await status_msg.edit(f"File added to list. Total: {len(target_list)}")
                return
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
        
        try:
            ext = tmp_in.suffix.lower()
            if ext == '.zip' or zipfile.is_zipfile(tmp_in):
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
            await status_msg.edit(f"Extraction failed: {e}\nAdding the downloaded file to list...", reply_markup=None)
            if target_list is not None:
                new_path = get_unique_filename(tmp_in.parent, original_name_pass)
                shutil.move(tmp_in, new_path)
                if target_list is CONVERT_BATCH_LIST.get(uid):
                    target_list.append(new_path)
                else:
                    target_list.append({'path': str(new_path), 'name': original_name_pass})
                return
            ZIP_READY_LIST.setdefault(uid, []).append({
                'root_dir': None,
                'files_to_upload': [tmp_in]
            })
            await check_and_show_next_zip(c, m.chat.id, uid)
            return
            
        found_zip = True
        while found_zip:
            found_zip = False
            for root, dirs, files in os.walk(ext_dir):
                for file in files:
                    nested_zip_path = Path(root) / file
                    if is_archive_file(nested_zip_path):
                        try:
                            n_ext = nested_zip_path.suffix.lower()
                            if n_ext == '.zip' or zipfile.is_zipfile(nested_zip_path):
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
        video_exts = {".mp4", ".mkv", ".avi", ".mov", ".flv", ".wmv", ".webm"}
        for root, dirs, files in os.walk(ext_dir):
            for f in files:
                p = Path(root) / f
                if target_list is not None and p.suffix.lower() not in video_exts:
                    continue
                all_files.append(p)
        all_files.sort(key=lambda x: x.name.lower())
        
        if not all_files:
            await status_msg.edit("No suitable files found in the extracted archive.")
            shutil.rmtree(ext_dir, ignore_errors=True)
            return

        if target_list is not None:
            if target_list is CONVERT_BATCH_LIST.get(uid):
                target_list.extend(all_files)
                await status_msg.edit(f"Extracted {len(all_files)} files for Conversion. Send `next` to configure.")
            else:
                for f in all_files:
                    target_list.append({'path': str(f), 'name': f.name})
                await status_msg.edit(f"Extracted {len(all_files)} files to list. Total: {len(target_list)}")
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

# --- BATCH AUDIO LIST UI & PAGINATION ---
async def send_batch_audio_list_page(c, chat_id, uid, list_id, page=0, msg_id=None):
    target_list = BATCH_AUDIO_LIST1.get(uid, []) if list_id == 'list1' else BATCH_AUDIO_LIST2.get(uid, [])
    per_page = 10
    total_items = len(target_list)
    total_pages = max(1, math.ceil(total_items / per_page))
    
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    
    start_idx = page * per_page
    end_idx = min(start_idx + per_page, total_items)
    
    list_name = "List 1 (Base Videos)" if list_id == 'list1' else "List 2 (Audio Sources)"
    text = f"**{list_name} - Page {page + 1}/{total_pages}**\n\n"
    
    keyboard = []
    
    if total_items == 0:
        text += "List is empty."
    else:
        for i in range(start_idx, end_idx):
            f_name = target_list[i]['name']
            text += f"**{i+1}.** `{f_name}`\n"
            keyboard.append([
                InlineKeyboardButton(f"{i+1}. {f_name[:20]}...", callback_data="ignore"),
                InlineKeyboardButton("Delete 🗑️", callback_data=f"baud_list_del_{list_id}_{i}_{page}")
            ])
            
    nav_buttons = []
    if page > 0:
        nav_buttons.append(InlineKeyboardButton("⬅️ Previous", callback_data=f"baud_list_page_{list_id}_{page-1}"))
    if page < total_pages - 1:
        nav_buttons.append(InlineKeyboardButton("Next ➡️", callback_data=f"baud_list_page_{list_id}_{page+1}"))
        
    if nav_buttons:
        keyboard.append(nav_buttons)
        
    keyboard.append([InlineKeyboardButton("Close ❌", callback_data="baud_list_close")])
    
    markup = InlineKeyboardMarkup(keyboard)
    
    if msg_id:
        try: await c.edit_message_text(chat_id, msg_id, text, reply_markup=markup)
        except Exception: pass
    else:
        await c.send_message(chat_id, text, reply_markup=markup)
# ----------------------------------------


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
        icon = "📁" if item.is_dir() else "📄"
        text_lines.append(f"**{i}.** {icon} `{name}`")
            
    text_lines.append("\n**Options:**")
    text_lines.append("‣ `0`: Go up | `<num>`: Open folder/Select file")
    text_lines.append("‣ `e 1-2`: Extract ZIP | `d 1-3`: Delete files")
    text_lines.append("‣ `l 1-5` or `l all`: Generate Direct DL Link")
    text_lines.append("‣ `r 1-5`: Rename metadata | `close`: Exit")
    
    full_text = "\n".join(text_lines)
    
    chunks = [full_text[i:i+3500] for i in range(0, len(full_text), 3500)]
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
        renamed_file = get_dynamic_filename(uid, original_name)
        
        if uid not in USER_QUEUES:
            USER_QUEUES[uid] = asyncio.Queue()
        
        status_msg = await c.send_message(m.chat.id, f"Queue: Upload added for `{original_name}`...", reply_markup=progress_keyboard())
        
        await USER_QUEUES[uid].put({
            'message': m,
            'original_name': original_name,
            'status_msg': status_msg,
            'is_url': False,
            'path_file': fpath,
            'original_caption': original_name
        })
        
        if uid not in USER_WORKERS or USER_WORKERS[uid].done():
            USER_WORKERS[uid] = asyncio.create_task(process_queue_handler(uid, c))
    await c.send_message(m.chat.id, "Path selected files queued successfully.")

# ----------------------------------------

# --- CONVERT MODE LOGIC ---
async def process_convert_queue_worker(uid, client):
    if uid not in CONVERT_LOCKS:
        CONVERT_LOCKS[uid] = asyncio.Lock()
    pass

async def handle_convert_input(c, m, url=None, file_info=None, override_path=None):
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
        elif override_path:
            original_name = Path(override_path).name
            
        safe_name = re.sub(r"[\\/*?\"<>|:]", "_", original_name)
        tmp_in = get_unique_filename(TMP, f"cv_{uid}_{int(time.time())}_{safe_name}")
        
        ok = False
        if override_path:
            tmp_in = Path(override_path)
            ok = True
        elif url:
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
        if 'tmp_in' in locals() and tmp_in.exists() and not override_path:
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
        await cb.answer("Queued for conversions...", show_alert=False)
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
    
    if uid not in CONVERT_LOCKS:
        CONVERT_LOCKS[uid] = asyncio.Lock()
        
    async with CONVERT_LOCKS[uid]: # Limit to one convert task at a time to save CPU
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg_id] = cancel_event
    
        try:
            for idx, config in enumerate(configs, 1):
                if cancel_event.is_set(): break
                
                res_val = config['res']
                vb = config['v_bitrate']
                ab = config['a_bitrate']
                orig_vb = meta['v_bitrate']
                
                out_ext = in_path.suffix if in_path.suffix else ".mp4"
                res_str = f"{res_val}p" if res_val else "OrigRes"
                out_name = f"[Convert_{res_str}_{vb//1000}k] {original_name}"
                out_path = get_unique_filename(TMP, f"cv_out_{uid}_{int(time.time())}_{idx}{out_ext}")
                
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
                
                if vb > orig_vb and orig_vb > 0:
                    cmd.extend(["-c:v", "libx264", "-pix_fmt", "yuv420p", "-profile:v", "high", "-preset", "ultrafast", "-threads", "0", 
                                "-b:v", str(vb), "-minrate", str(vb), "-maxrate", str(vb), "-bufsize", str(vb*2)])
                else:
                    cmd.extend(["-c:v", "libx264", "-pix_fmt", "yuv420p", "-profile:v", "high", "-preset", "medium", "-threads", "0", "-b:v", str(vb)])
                
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
                out_name = get_dynamic_filename(uid, original_name)
                await sequential_upload_task(uid, client, msg, in_path, out_name, None, cancel_event, default_caption=original_name, original_caption=None, original_download_name=original_name)
                in_path = None
                
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
            
        # Process next file in batch
        batch_list = CONVERT_BATCH_LIST.get(uid, [])
        if batch_list:
            next_file = batch_list.pop(0)
            await handle_convert_input(client, msg, override_path=next_file)
            
# ----------------------------------------


@app.on_message(filters.text & filters.private)
async def text_handler(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    text = m.text.strip()
    text_lower = text.lower()
    
    if uid in SET_FILENAME_REQUEST:
        SET_FILENAME_REQUEST.discard(uid)
        USER_FILENAMES[uid] = text
        await m.reply_text("Your file name format has been saved. Uploaded/renamed videos will use this format.")
        return
    
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

    # t command for TG file direct link
    if text_lower == "t" and uid in DOWNLOAD_ONLY_MODE:
        if m.reply_to_message and (m.reply_to_message.video or m.reply_to_message.document):
            file_info = m.reply_to_message.video or m.reply_to_message.document
            file_uuid = str(uuid.uuid4())
            TG_FILE_STREAMS[file_uuid] = file_info.file_id
            host = RENDER_EXTERNAL_HOSTNAME or f"localhost:{PORT}"
            link = f"http://{host}/stream/{file_uuid}"
            await m.reply_text(f"**Direct Telegram Stream Link:**\n`{link}`\n*(Link works as long as bot is running)*")
        else:
            await m.reply_text("Reply to a Telegram Video or Document with `t` to generate a stream link.")
        return

    # link command for download_only mode
    if text_lower == "link" and uid in DOWNLOAD_ONLY_MODE:
        out_dir = TMP / f"download_only_{uid}"
        if out_dir.exists():
            items = list(out_dir.iterdir())
            if not items:
                await m.reply_text("No files downloaded yet.")
                return
            links = []
            for item in items:
                if item.is_file():
                    file_uuid = str(uuid.uuid4())
                    DIRECT_LINKS[file_uuid] = str(item)
                    host = RENDER_EXTERNAL_HOSTNAME or f"localhost:{PORT}"
                    links.append(f"📄 `{item.name}`\n🔗 `http://{host}/dl/{file_uuid}`")
            if links:
                await m.reply_text("**Direct Download Links:**\n\n" + "\n\n".join(links))
            else:
                await m.reply_text("No files downloaded yet.")
        else:
            await m.reply_text("No files downloaded yet.")
        return

    # UI Delete List support
    if text_lower == "list" and uid in BATCH_AUDIO_MODE:
        state = BATCH_AUDIO_STATE.get(uid)
        if state in ['list1', 'list2']:
            await send_batch_audio_list_page(c, m.chat.id, uid, state, 0)
        else:
            await m.reply_text("List viewing is only available while adding links/videos to lists.")
        return

    if text_lower == "path":
        NAV_PATHS[uid] = {"current": TMP, "items": []}
        await send_path_ui(c, m.chat.id, uid)
        return

    # Handle zip convert mode is removed, extracting zip automatically
    if uid in CONVERT_MODE:
        if text_lower == "next":
            batch_list = CONVERT_BATCH_LIST.get(uid, [])
            if not batch_list:
                await m.reply_text("List is empty. Send videos/links/zips first.")
                return
            await m.reply_text("Starting Batch Conversion configuration...")
            first_file = batch_list.pop(0)
            await handle_convert_input(c, m, override_path=first_file)
            return

    # Handle all for zip
    if uid in ZIP_DOWNLOAD_MODE:
        if text_lower == "all":
            AUTO_UPLOAD_ALL.add(uid)
            await m.reply_text("Auto Upload All is now **ON**.")
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
            
            def parse_indices(s, max_len):
                idxs = set()
                for part in s.split(','):
                    part = part.strip()
                    if not part: continue
                    if '-' in part:
                        try:
                            st, en = map(int, part.split('-'))
                            for i in range(st, en + 1):
                                if 1 <= i <= max_len: idxs.add(i)
                        except: pass
                    else:
                        try:
                            num = int(part)
                            if 1 <= num <= max_len: idxs.add(num)
                        except: pass
                return sorted(list(idxs))
                
            if text_lower.startswith('e '):
                target = text_lower[2:].strip()
                files = state['files_to_upload']
                idxs = parse_indices(target, len(files))
                if not idxs:
                    err_msg = await m.reply_text("Invalid format for manual extract. Use `e 1` or `e 1-3`.")
                    state['garbage_msgs'].append(err_msg.id)
                    return
                for num in idxs:
                    file_to_extract = files[num-1]
                    if uid not in ZIP_DL_QUEUES:
                        ZIP_DL_QUEUES[uid] = asyncio.Queue()
                    queue_msg = await m.reply_text(f"Queued for manual extraction. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
                    await ZIP_DL_QUEUES[uid].put({'local_path': str(file_to_extract), 'message': m, 'queue_msg': queue_msg})
                    if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
                        ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
                return
            
            files = state['files_to_upload']
            valid_selected = parse_indices(text_lower, len(files))
            if not valid_selected:
                err_msg = await m.reply_text("Invalid format. Use numbers, ranges like 1,3,5,8-15, or `e 1` for manual extract.")
                state['garbage_msgs'].append(err_msg.id)
                return
                
            all_indices = list(range(1, len(files) + 1))
            unselected = [i for i in all_indices if i not in valid_selected]
            final_order = valid_selected + unselected
            
            await process_zip_uploads(c, m, uid, final_order)
            return
    
    if uid in NAV_PATHS:
        state = NAV_PATHS[uid]
        current = state['current']
        items = state.get('items', [])
        
        if text_lower == 'close':
            NAV_PATHS.pop(uid)
            await m.reply_text("File Manager closed.")
            return
        elif text_lower == 'b':
            if current != TMP:
                NAV_PATHS[uid]['current'] = current.parent
                await send_path_ui(c, m.chat.id, uid)
            else:
                await m.reply_text("Already at root directory.")
            return
            
        def parse_indices(s, max_len):
            idxs = set()
            for part in s.split(','):
                part = part.strip()
                if not part: continue
                if '-' in part:
                    try:
                        st, en = map(int, part.split('-'))
                        for i in range(st, en + 1):
                            if 1 <= i <= max_len: idxs.add(i)
                    except: pass
                else:
                    try:
                        num = int(part)
                        if 1 <= num <= max_len: idxs.add(num)
                    except: pass
            return sorted(list(idxs))

        if text_lower.startswith("d "):
            target = text_lower[2:].strip()
            if target == "all":
                idxs = list(range(1, len(items) + 1))
            else:
                idxs = parse_indices(target, len(items))
            for i in idxs:
                item = items[i-1]
                if item.is_dir(): shutil.rmtree(item, ignore_errors=True)
                else: item.unlink(missing_ok=True)
            await m.reply_text(f"Deleted {len(idxs)} items.")
            await send_path_ui(c, m.chat.id, uid)
            return

        if text_lower.startswith("e "):
            target = text_lower[2:].strip()
            idxs = parse_indices(target, len(items))
            for i in idxs:
                item = items[i-1]
                if item.is_file() and is_archive_file(item):
                    ext_dir = get_unique_filename(current, f"ext_{int(time.time())}")
                    ext_dir.mkdir(exist_ok=True)
                    try:
                        ext = item.suffix.lower()
                        if ext == '.zip' or zipfile.is_zipfile(item):
                            with zipfile.ZipFile(item, 'r') as zip_ref: zip_ref.extractall(ext_dir)
                        elif ext == '.rar' and 'rarfile' in globals():
                            with rarfile.RarFile(item, 'r') as rar_ref: rar_ref.extractall(ext_dir)
                        elif ext == '.7z' and 'py7zr' in globals():
                            with py7zr.SevenZipFile(item, 'r') as sz_ref: sz_ref.extractall(ext_dir)
                        item.unlink()
                    except Exception as e:
                        await m.reply_text(f"Extract error on {item.name}: {e}")
            await m.reply_text(f"Extracted selected archives.")
            await send_path_ui(c, m.chat.id, uid)
            return

        if text_lower.startswith("l "):
            target = text_lower[2:].strip()
            if target == "all":
                idxs = list(range(1, len(items) + 1))
            else:
                idxs = parse_indices(target, len(items))
            links = []
            for i in idxs:
                item = items[i-1]
                if item.is_file():
                    file_uuid = str(uuid.uuid4())
                    DIRECT_LINKS[file_uuid] = str(item)
                    host = RENDER_EXTERNAL_HOSTNAME or f"localhost:{PORT}"
                    links.append(f"📄 `{item.name}`\n🔗 `http://{host}/dl/{file_uuid}`")
            if links:
                await m.reply_text("**Direct Links:**\n\n" + "\n\n".join(links))
            else:
                await m.reply_text("No files selected for links.")
            return

        if text_lower.startswith("r "):
            target = text_lower[2:].strip()
            if target == "all":
                idxs = list(range(1, len(items) + 1))
            else:
                idxs = parse_indices(target, len(items))
            for i in idxs:
                item = items[i-1]
                if item.is_file():
                    new_name = get_dynamic_filename(uid, item.name)
                    tmp_out = get_unique_filename(current, f"ren_{int(time.time())}_{new_name}")
                    cmd = [
                        "ffmpeg", "-y", "-i", str(item),
                        "-map", "0", "-c", "copy",
                        "-metadata", f"title=[@TA_HD_Anime] Telegram Channel",
                        "-metadata:s:v", "title=[@TA_HD_Anime] Telegram Channel",
                        "-metadata:s:a", "title=[@TA_HD_Anime] Telegram Channel",
                        str(tmp_out)
                    ]
                    try:
                        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                        if tmp_out.exists() and tmp_out.stat().st_size > 0:
                            item.unlink()
                            new_path = get_unique_filename(current, new_name)
                            tmp_out.rename(new_path)
                    except: pass
            await m.reply_text(f"Renamed selected files.")
            await send_path_ui(c, m.chat.id, uid)
            return
            
        try:
            idxs = parse_indices(text_lower, len(items))
            if len(idxs) == 1:
                item = items[idxs[0]-1]
                if item.is_dir():
                    NAV_PATHS[uid]['current'] = item
                    await send_path_ui(c, m.chat.id, uid)
                    return
            files_to_upload = [items[i-1] for i in idxs if items[i-1].is_file()]
            if files_to_upload:
                await m.reply_text(f"Queued {len(files_to_upload)} files for upload.")
                asyncio.create_task(process_path_uploads(uid, c, m, files_to_upload))
            return
        except:
            pass

    # Handle Batch Audio Add Commands
    if uid in BATCH_AUDIO_MODE:
        if text_lower == "next":
            state = BATCH_AUDIO_STATE.get(uid, 'list1')
            if state == 'list1':
                if not BATCH_AUDIO_LIST1.get(uid):
                    await m.reply_text("List 1 is empty. Please send Base Videos first.")
                    return
                BATCH_AUDIO_STATE[uid] = 'list2'
                keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton("Use List 1 Audio 🎵", callback_data="baud_use_list1")]
                ])
                await m.reply_text(f"List 1 complete with {len(BATCH_AUDIO_LIST1[uid])} items.\nNow send Audio Source Videos / ZIP files (List 2).\n*(Type next when done, or click the button below to use List 1 internally)*", reply_markup=keyboard)
            elif state == 'list2':
                if not BATCH_AUDIO_LIST2.get(uid):
                    await m.reply_text("List 2 is empty. Please send Audio Sources first.")
                    return
                BATCH_AUDIO_STATE[uid] = 'mapping'
                
                def chunk_and_send(lst, title):
                    chunks = []
                    curr = f"**{title}:**\n"
                    for i, p in enumerate(lst):
                        line = f"{i+1}. {p['name']}\n"
                        if len(curr) + len(line) > 3500:
                            chunks.append(curr)
                            curr = f"**{title} (Cont):**\n"
                        curr += line
                    if curr: chunks.append(curr)
                    return chunks

                list1_chunks = chunk_and_send(BATCH_AUDIO_LIST1[uid], "List 1 (Base Videos)")
                list2_chunks = chunk_and_send(BATCH_AUDIO_LIST2[uid], "List 2 (Audio Sources)")

                for c_msg in list1_chunks: await m.reply_text(c_msg)
                for c_msg in list2_chunks: await m.reply_text(c_msg)
                
                keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton("Upload All 🚀", callback_data="baud_list_ok")],
                    [InlineKeyboardButton("Cancel ❌", callback_data="baud_list_cancel")]
                ])
                
                await m.reply_text(
                    "**Mapping Rules:**\n"
                    "‣ Default matches 1 to 1, 2 to 2.\n"
                    "‣ Custom mapping: send `1-13=1-13, 14=16, 15=14`\n"
                    "‣ Click Upload All or send custom string.",
                    reply_markup=keyboard
                )
            return
        elif text_lower == "off":
            BATCH_AUDIO_MODE.discard(uid)
            BATCH_AUDIO_STATE.pop(uid, None)
            for item in BATCH_AUDIO_LIST1.get(uid, []):
                try: Path(item['path']).unlink(missing_ok=True)
                except: pass
            for item in BATCH_AUDIO_LIST2.get(uid, []):
                try: Path(item['path']).unlink(missing_ok=True)
                except: pass
            BATCH_AUDIO_LIST1.pop(uid, None)
            BATCH_AUDIO_LIST2.pop(uid, None)
            if uid in BATCH_AUDIO_QUEUES:
                while not BATCH_AUDIO_QUEUES[uid].empty():
                    try: BATCH_AUDIO_QUEUES[uid].get_nowait(); BATCH_AUDIO_QUEUES[uid].task_done()
                    except: pass
            await m.reply_text("Batch Audio Add Mode **OFF**.")
            return
        elif BATCH_AUDIO_STATE.get(uid) == 'mapping':
            pairs = []
            if text_lower == 'ok':
                count = min(len(BATCH_AUDIO_LIST1[uid]), len(BATCH_AUDIO_LIST2[uid]))
                pairs = [(i, i) for i in range(count)]
            else:
                try:
                    mapping_str = text_lower.replace(' ', '')
                    parts = mapping_str.split(',')
                    for part in parts:
                        if not part: continue
                        if '=' in part:
                            l_str, r_str = part.split('=')
                        else:
                            l_str, r_str = part, part
                        
                        def parse_indices(s):
                            res = []
                            if '-' in s:
                                st, en = map(int, s.split('-'))
                                res.extend(list(range(st-1, en)))
                            else:
                                res.append(int(s)-1)
                            return res
                            
                        l_idx = parse_indices(l_str)
                        r_idx = parse_indices(r_str)
                        
                        if len(r_idx) == 1 and len(l_idx) > 1:
                            r_idx = r_idx * len(l_idx)
                            
                        for l, r in zip(l_idx, r_idx):
                            if 0 <= l < len(BATCH_AUDIO_LIST1[uid]) and 0 <= r < len(BATCH_AUDIO_LIST2[uid]):
                                pairs.append((l, r))
                except Exception as e:
                    await m.reply_text(f"Invalid mapping format: {e}. Please try again or type `ok` for default. \nExample: `1-5=1-5, 6=8, 7=9`")
                    return
            
            if not pairs:
                await m.reply_text("No valid mappings found. Try again.")
                return
                
            BATCH_AUDIO_MAPPING[uid] = pairs
            BATCH_AUDIO_STATE[uid] = 'ui'
            BATCH_AUDIO_CURRENT_PAIR_IDX[uid] = 0
            BATCH_AUDIO_TRACK_CONFIGS[uid] = {}
            
            await show_batch_audio_ui(c, m.chat.id, uid)
            return

    is_batch_cmd = text_lower in ["on", "off", "no", "d", "cap"] or text_lower.startswith("ok")

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
        if uid in DOWNLOAD_ONLY_MODE:
            original_name = await get_filename_from_url(url)
            safe_name = re.sub(r"[\\/*?\"<>|:]", "_", original_name)
            out_dir = TMP / f"download_only_{uid}"
            out_dir.mkdir(parents=True, exist_ok=True)
            
            if uid not in ZIP_DL_QUEUES:
                ZIP_DL_QUEUES[uid] = asyncio.Queue()
            queue_msg = await m.reply_text(f"Queue: Added `{original_name}` for download only. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
            
            target_list = []
            await ZIP_DL_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg, 'target_list': target_list, 'local_path': None})
            
            if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
                async def custom_download_worker(uid_arg, c_arg):
                    while uid_arg in ZIP_DL_QUEUES and not ZIP_DL_QUEUES[uid_arg].empty():
                        t_data = await ZIP_DL_QUEUES[uid_arg].get()
                        try:
                            if t_data.get('queue_msg'):
                                try: await t_data['queue_msg'].delete()
                                except: pass
                            # Just download to out_dir
                            s_msg = await c_arg.send_message(m.chat.id, f"Downloading `{await get_filename_from_url(t_data['url'])}`...", reply_markup=progress_keyboard())
                            t_out = get_unique_filename(out_dir, await get_filename_from_url(t_data['url']))
                            ok, err = await download_url_generic(t_data['url'], t_out, s_msg)
                            if ok and is_archive_file(t_out):
                                await s_msg.edit("Extracting archive...", reply_markup=None)
                                try:
                                    ext = t_out.suffix.lower()
                                    if ext == '.zip' or zipfile.is_zipfile(t_out):
                                        with zipfile.ZipFile(t_out, 'r') as zip_ref: zip_ref.extractall(out_dir)
                                    elif ext == '.rar' and 'rarfile' in globals():
                                        with rarfile.RarFile(t_out, 'r') as rar_ref: rar_ref.extractall(out_dir)
                                    elif ext == '.7z' and 'py7zr' in globals():
                                        with py7zr.SevenZipFile(t_out, 'r') as sz_ref: sz_ref.extractall(out_dir)
                                    t_out.unlink()
                                    await s_msg.edit("Download & Extract complete. Send `link` to get links.")
                                except Exception as e:
                                    await s_msg.edit(f"Downloaded but extraction failed: {e}")
                            elif ok:
                                await s_msg.edit("Download complete. Send `link` to get links.")
                            else:
                                await s_msg.edit(f"Download failed: {err}")
                        except Exception as e:
                            logger.error(f"DL Only Error: {e}")
                        finally:
                            ZIP_DL_QUEUES[uid_arg].task_done()
                    if uid_arg in ZIP_DL_WORKERS: del ZIP_DL_WORKERS[uid_arg]
                
                ZIP_DL_WORKERS[uid] = asyncio.create_task(custom_download_worker(uid, c))
            return

        if uid in CONVERT_MODE:
            asyncio.create_task(execute_zip_download_and_extract(c, m, url=url, target_list=CONVERT_BATCH_LIST.get(uid)))
            return

        if uid in BATCH_AUDIO_MODE:
            state = BATCH_AUDIO_STATE.get(uid)
            target_list = BATCH_AUDIO_LIST1[uid] if state == 'list1' else BATCH_AUDIO_LIST2[uid]
            if uid not in BATCH_AUDIO_QUEUES:
                BATCH_AUDIO_QUEUES[uid] = asyncio.Queue()
            
            original_name = await get_filename_from_url(url)
            queue_msg = await m.reply_text(f"Queue item added for `{original_name}`. Position: {BATCH_AUDIO_QUEUES[uid].qsize() + 1}")
            
            await BATCH_AUDIO_QUEUES[uid].put({'url': url, 'message': m, 'target_list': target_list, 'queue_msg': queue_msg})
            if uid not in BATCH_AUDIO_WORKERS or BATCH_AUDIO_WORKERS[uid].done():
                BATCH_AUDIO_WORKERS[uid] = asyncio.create_task(batch_audio_worker(uid, c))
            return
            
        if uid in ZIP_DOWNLOAD_MODE:
            if uid not in ZIP_DL_QUEUES:
                ZIP_DL_QUEUES[uid] = asyncio.Queue()
            original_name = await get_filename_from_url(url)
            queue_msg = await m.reply_text(f"Queue item added for `{original_name}`. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
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

async def batch_audio_worker(uid, c):
    while uid in BATCH_AUDIO_QUEUES and not BATCH_AUDIO_QUEUES[uid].empty():
        task_data = await BATCH_AUDIO_QUEUES[uid].get()
        try:
            queue_msg = task_data.get('queue_msg')
            if queue_msg:
                try: await queue_msg.delete()
                except: pass
            await process_batch_audio_input(uid, c, task_data['message'], url=task_data.get('url'), file_info=task_data.get('file_info'), target_list=task_data.get('target_list'))
        except Exception as e:
            logger.error(f"Batch Audio Worker Error: {e}")
        finally:
            BATCH_AUDIO_QUEUES[uid].task_done()
    if uid in BATCH_AUDIO_WORKERS:
        del BATCH_AUDIO_WORKERS[uid]

async def process_batch_audio_input(uid, c, m, url=None, file_info=None, target_list=None):
    list_num = "1" if target_list is BATCH_AUDIO_LIST1.get(uid) else "2"
    
    if url or file_info:
        status_msg = None
        try:
            original_name = "video.mp4"
            if url: original_name = await get_filename_from_url(url)
            elif file_info: original_name = file_info.file_name or "video.mp4"
            
            status_msg = await m.reply_text(f"Downloading `{original_name}` to build list...")
            
            safe_name = re.sub(r"[\\/*?\"<>|:]", "_", original_name)
            tmp_in = get_unique_filename(TMP, safe_name)
            
            if url:
                if is_drive_url(url):
                    fid = extract_drive_id(url)
                    if fid: await download_drive_file(fid, tmp_in, status_msg, original_name=original_name)
                else:
                    await download_url_generic(url, tmp_in, status_msg, original_name=original_name)
            elif file_info:
                start_t = time.time()
                async def dl_prog(current, total):
                    if status_msg:
                        await progress_callback(current, total, "Downloading List Item...", status_msg, start_t, original_name=original_name)
                await m.download(file_name=str(tmp_in), progress=dl_prog)
                
            if tmp_in.exists():
                if is_archive_file(tmp_in):
                    await status_msg.delete()
                    await execute_zip_download_and_extract(c, m, url=None, local_path=str(tmp_in), target_list=target_list)
                    tmp_in.unlink(missing_ok=True)
                else:
                    target_list.append({'path': str(tmp_in), 'name': original_name})
                    await status_msg.edit(f"URL/File added to List {list_num}. Total: {len(target_list)}")
            else:
                await status_msg.edit("Failed to download file.")
        except Exception as e:
            logger.error(f"Batch Audio DL error: {e}")
            if status_msg:
                try: await status_msg.edit(f"Failed to download file: {e}")
                except: pass

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
    
    if uid in DOWNLOAD_ONLY_MODE:
        original_name = await get_filename_from_url(url)
        out_dir = TMP / f"download_only_{uid}"
        out_dir.mkdir(parents=True, exist_ok=True)
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Queue: Added `{original_name}` for download only. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
        
        target_list = []
        await ZIP_DL_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg, 'target_list': target_list, 'local_path': None})
        
        if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
            async def custom_download_worker(uid_arg, c_arg):
                while uid_arg in ZIP_DL_QUEUES and not ZIP_DL_QUEUES[uid_arg].empty():
                    t_data = await ZIP_DL_QUEUES[uid_arg].get()
                    try:
                        if t_data.get('queue_msg'):
                            try: await t_data['queue_msg'].delete()
                            except: pass
                        s_msg = await c_arg.send_message(m.chat.id, f"Downloading `{await get_filename_from_url(t_data['url'])}`...", reply_markup=progress_keyboard())
                        t_out = get_unique_filename(out_dir, await get_filename_from_url(t_data['url']))
                        ok, err = await download_url_generic(t_data['url'], t_out, s_msg)
                        if ok and is_archive_file(t_out):
                            await s_msg.edit("Extracting archive...", reply_markup=None)
                            try:
                                ext = t_out.suffix.lower()
                                if ext == '.zip' or zipfile.is_zipfile(t_out):
                                    with zipfile.ZipFile(t_out, 'r') as zip_ref: zip_ref.extractall(out_dir)
                                elif ext == '.rar' and 'rarfile' in globals():
                                    with rarfile.RarFile(t_out, 'r') as rar_ref: rar_ref.extractall(out_dir)
                                elif ext == '.7z' and 'py7zr' in globals():
                                    with py7zr.SevenZipFile(t_out, 'r') as sz_ref: sz_ref.extractall(out_dir)
                                t_out.unlink()
                                await s_msg.edit("Download & Extract complete. Send `link` to get links.")
                            except Exception as e:
                                await s_msg.edit(f"Downloaded but extraction failed: {e}")
                        elif ok:
                            await s_msg.edit("Download complete. Send `link` to get links.")
                        else:
                            await s_msg.edit(f"Download failed: {err}")
                    except Exception as e:
                        logger.error(f"DL Only Error: {e}")
                    finally:
                        ZIP_DL_QUEUES[uid_arg].task_done()
                if uid_arg in ZIP_DL_WORKERS: del ZIP_DL_WORKERS[uid_arg]
            
            ZIP_DL_WORKERS[uid] = asyncio.create_task(custom_download_worker(uid, c))
        return

    if uid in CONVERT_MODE:
        asyncio.create_task(execute_zip_download_and_extract(c, m, url=url, target_list=CONVERT_BATCH_LIST.get(uid)))
        return

    if uid in BATCH_AUDIO_MODE:
        state = BATCH_AUDIO_STATE.get(uid)
        target_list = BATCH_AUDIO_LIST1[uid] if state == 'list1' else BATCH_AUDIO_LIST2[uid]
        if uid not in BATCH_AUDIO_QUEUES:
            BATCH_AUDIO_QUEUES[uid] = asyncio.Queue()
            
        original_name = await get_filename_from_url(url)
        queue_msg = await m.reply_text(f"Queue item added for `{original_name}`. Position: {BATCH_AUDIO_QUEUES[uid].qsize() + 1}")
        
        await BATCH_AUDIO_QUEUES[uid].put({'url': url, 'message': m, 'target_list': target_list, 'queue_msg': queue_msg})
        if uid not in BATCH_AUDIO_WORKERS or BATCH_AUDIO_WORKERS[uid].done():
            BATCH_AUDIO_WORKERS[uid] = asyncio.create_task(batch_audio_worker(uid, c))
        return
    
    if uid in ZIP_DOWNLOAD_MODE:
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        original_name = await get_filename_from_url(url)
        queue_msg = await m.reply_text(f"Queue item added for `{original_name}`. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
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

        tmp_in = get_unique_filename(TMP, safe_name)
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
        renamed_file = get_dynamic_filename(uid, safe_name)
        
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

    if uid in DOWNLOAD_ONLY_MODE:
        out_dir = TMP / f"download_only_{uid}"
        out_dir.mkdir(parents=True, exist_ok=True)
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Queue: Added `{original_name}` for download only. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
        
        target_list = []
        await ZIP_DL_QUEUES[uid].put({'message': m, 'queue_msg': queue_msg, 'target_list': target_list, 'local_path': None})
        
        if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
            async def custom_download_worker(uid_arg, c_arg):
                while uid_arg in ZIP_DL_QUEUES and not ZIP_DL_QUEUES[uid_arg].empty():
                    t_data = await ZIP_DL_QUEUES[uid_arg].get()
                    try:
                        if t_data.get('queue_msg'):
                            try: await t_data['queue_msg'].delete()
                            except: pass
                        m_obj = t_data['message']
                        f_info = m_obj.video or m_obj.document
                        orig = f_info.file_name or f"file_{f_info.file_unique_id}"
                        s_msg = await c_arg.send_message(m_obj.chat.id, f"Downloading `{orig}`...", reply_markup=progress_keyboard())
                        t_out = get_unique_filename(out_dir, orig)
                        
                        start_t = time.time()
                        async def dl_prog(current, total):
                            await progress_callback(current, total, "Downloading...", s_msg, start_t, original_name=orig)
                        await m_obj.download(file_name=str(t_out), progress=dl_prog)
                        
                        if is_archive_file(t_out):
                            await s_msg.edit("Extracting archive...", reply_markup=None)
                            try:
                                ext = t_out.suffix.lower()
                                if ext == '.zip' or zipfile.is_zipfile(t_out):
                                    with zipfile.ZipFile(t_out, 'r') as zip_ref: zip_ref.extractall(out_dir)
                                elif ext == '.rar' and 'rarfile' in globals():
                                    with rarfile.RarFile(t_out, 'r') as rar_ref: rar_ref.extractall(out_dir)
                                elif ext == '.7z' and 'py7zr' in globals():
                                    with py7zr.SevenZipFile(t_out, 'r') as sz_ref: sz_ref.extractall(out_dir)
                                t_out.unlink()
                                await s_msg.edit("Download & Extract complete. Send `link` to get links.")
                            except Exception as e:
                                await s_msg.edit(f"Downloaded but extraction failed: {e}")
                        else:
                            await s_msg.edit("Download complete. Send `link` to get links.")
                    except Exception as e:
                        logger.error(f"DL Only Error: {e}")
                    finally:
                        ZIP_DL_QUEUES[uid_arg].task_done()
                if uid_arg in ZIP_DL_WORKERS: del ZIP_DL_WORKERS[uid_arg]
            ZIP_DL_WORKERS[uid] = asyncio.create_task(custom_download_worker(uid, c))
        return

    if uid in CONVERT_MODE:
        asyncio.create_task(execute_zip_download_and_extract(c, m, url=None, target_list=CONVERT_BATCH_LIST.get(uid)))
        return
        
    if uid in BATCH_AUDIO_MODE:
        state = BATCH_AUDIO_STATE.get(uid)
        target_list = BATCH_AUDIO_LIST1[uid] if state == 'list1' else BATCH_AUDIO_LIST2[uid]
        if uid not in BATCH_AUDIO_QUEUES:
            BATCH_AUDIO_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Queue item added for `{original_name}`. Position: {BATCH_AUDIO_QUEUES[uid].qsize() + 1}")
        await BATCH_AUDIO_QUEUES[uid].put({'file_info': file_info, 'message': m, 'target_list': target_list, 'queue_msg': queue_msg})
        if uid not in BATCH_AUDIO_WORKERS or BATCH_AUDIO_WORKERS[uid].done():
            BATCH_AUDIO_WORKERS[uid] = asyncio.create_task(batch_audio_worker(uid, c))
        return

    if uid in ZIP_DOWNLOAD_MODE:
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Queue item added for `{original_name}`. Position: {ZIP_DL_QUEUES[uid].qsize() + 1}")
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

# --- FLASK STREAMING AND DIRECT LINKS ---
import queue

@flask_app.route('/stream/<uuid>')
def stream_tg_file(uuid):
    file_id = TG_FILE_STREAMS.get(uuid)
    if not file_id: return "Invalid Link", 404
    
    q = queue.Queue(maxsize=10)
    
    async def fetch_data():
        try:
            async for chunk in app.stream_media(file_id, limit=0):
                q.put(chunk)
        except Exception as e:
            print(e)
        finally:
            q.put(None)
            
    asyncio.run_coroutine_threadsafe(fetch_data(), app.loop)
    
    def generate():
        while True:
            chunk = q.get()
            if chunk is None:
                break
            yield chunk
            
    return Response(stream_with_context(generate()), mimetype="video/mp4")

@flask_app.route('/dl/<uuid>')
def download_direct(uuid):
    filepath = DIRECT_LINKS.get(uuid)
    if not filepath or not os.path.exists(filepath):
        return "File not found", 404
    return send_file(filepath, as_attachment=True)

@flask_app.route('/')
def home():
    html_content = """
    <!DOCTYPE html>
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
