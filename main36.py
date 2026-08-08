[file name]: main35.py
[file content begin]
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
from flask import Flask, render_template_string, send_from_directory, Response, request, redirect
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
import email.message
import mimetypes
try:
    from google.oauth2 import service_account
    from googleapiclient.discovery import build
    from googleapiclient.http import MediaFileUpload
except ImportError:
    pass
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
PORT = int(os.getenv("PORT", "10000"))
RENDER_EXTERNAL_HOSTNAME = os.getenv("RENDER_EXTERNAL_HOSTNAME")
if not RENDER_EXTERNAL_HOSTNAME:
    try:
        import urllib.request
        _public_ip = urllib.request.urlopen('https://api.ipify.org', timeout=3).read().decode('utf8')
        RENDER_EXTERNAL_HOSTNAME = f"{_public_ip}:{PORT}"
    except Exception:
        try:
            _s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            _s.connect(("8.8.8.8", 80))
            _local_ip = _s.getsockname()[0]
            _s.close()
            RENDER_EXTERNAL_HOSTNAME = f"{_local_ip}:{PORT}"
        except Exception:
            RENDER_EXTERNAL_HOSTNAME = f"localhost:{PORT}"
PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL")
if not PUBLIC_BASE_URL:
    PUBLIC_BASE_URL = f"http://{RENDER_EXTERNAL_HOSTNAME}"
else:
    if not PUBLIC_BASE_URL.startswith(('http://', 'https://')):
        PUBLIC_BASE_URL = f"http://{PUBLIC_BASE_URL}"
API_ID = int(os.getenv("API_ID"))
API_HASH = os.getenv("API_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
GDRIVE_SERVICE_KEY = os.getenv("GDRIVE_SERVICE_KEY")
GDRIVE_FOLDER_ID = os.getenv("GDRIVE_FOLDER_ID")
RAW_COOKIES = os.getenv("COOKIES_TXT")
if RAW_COOKIES:
    if os.path.exists(RAW_COOKIES):
        COOKIES_TXT = RAW_COOKIES
    else:
        with open("cookies.txt", "w") as f:
            f.write(RAW_COOKIES)
        COOKIES_TXT = "cookies.txt"
else:
    COOKIES_TXT = None
TMP = Path("tmp")
TMP.mkdir(parents=True, exist_ok=True)
USER_THUMBS = {}
TASKS = {}
USER_TASK_EVENTS = {} 
DOWNLOAD_TASKS = {}   
UPLOAD_TASKS = {}     
SET_THUMB_REQUEST = set()
SET_CAPTION_REQUEST = set()
SET_FILENAME_REQUEST = set() 
USER_CAPTIONS = {}
USER_FILENAMES = {} 
USER_COUNTERS = {}
EDIT_CAPTION_MODE = set()
USER_THUMB_TIME = {}
HIDE_PROGRESS_BAR = set()
USER_PROGRESS_INTERVAL = {} 
USER_QUEUE_PAUSED = set()
AUTO_UPLOAD_ALL = set()
MKV_AUDIO_CHANGE_MODE = set()
PENDING_AUDIO_ORDERS = {}
CONVERT_MODE = set()
CONVERT_SESSIONS = {}
ACTIVE_CONVERT_SESSION = {} 
CONVERT_LOCKS = {} 
CONVERT_ZIP_MODE = set()
CONVERT_BATCH_LIST = {} 
CONVERT_BATCH_UI_MSG = {}
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
USER_DOWNLOAD_QUEUES = {}
USER_UPLOAD_QUEUES = {}
DOWNLOAD_WORKERS = {}
UPLOAD_WORKERS = {}
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
BATCH_AUDIO_MODE = set()
BATCH_AUDIO_STATE = {} 
BATCH_AUDIO_LIST1 = {} 
BATCH_AUDIO_LIST2 = {} 
BATCH_AUDIO_MAPPING = {} 
BATCH_AUDIO_CURRENT_PAIR_IDX = {}
BATCH_AUDIO_TRACK_CONFIGS = {}
BATCH_AUDIO_UI_MSG = {}
BATCH_AUDIO_DOWNLOAD_TASKS = {}
BATCH_AUDIO_QUEUES = {}
BATCH_AUDIO_WORKERS = {}
DOWNLOAD_ONLY_MODE = set()
DOWNLOAD_LINK_MODE = set()
DOWNLOAD_T_MODE = set()
UPLOAD_DRIVE_MODE = set()
MISSING_EXT_QUEUE = {} 
PATH_MODE_SELECTION = {}          
PATH_CONVERT_LIST = {}            
PATH_BATCH_AUDIO_LIST1 = {}       
PATH_BATCH_AUDIO_LIST2 = {}       
PATH_BATCH_AUDIO_STAGE = {}       
PATH_ZIP_LISTS = {}               
PATH_ZIP_CURRENT_LIST = {}        
EXTENSION_WAIT = {}  
ADMIN_ID = int(os.getenv("ADMIN_ID", ""))
MAX_SIZE = 1000 * 1024 * 1024 * 1024 

# ===== CONCURRENCY CONTROL SETTINGS =====
MAX_CONCURRENT_DOWNLOADS = 5
MAX_CONCURRENT_UPLOADS = 5
MAX_CONCURRENT_CONVERTS = 5

# ===== SEMAPHORES FOR CONCURRENCY =====
DOWNLOAD_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_DOWNLOADS)
UPLOAD_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_UPLOADS)
CONVERT_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_CONVERTS)

# ===== ORDERED OUTPUT QUEUES =====
USER_OUTPUT_QUEUES = {}
USER_OUTPUT_WORKERS = {}
USER_OUTPUT_ORDER = {}
USER_OUTPUT_LOCK = {}

# ===== ORDERED CONVERT QUEUES =====
CONVERT_OUTPUT_QUEUES = {}
CONVERT_OUTPUT_WORKERS = {}
CONVERT_OUTPUT_ORDER = {}
CONVERT_OUTPUT_LOCK = {}

app = Client("mybot", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN, workers=1000, sleep_threshold=86400)
flask_app = Flask(__name__)
MAIN_LOOP = None 

def get_gdrive_service():
    if not GDRIVE_SERVICE_KEY:
        return None
    try:
        creds_dict = json.loads(GDRIVE_SERVICE_KEY)
        creds = service_account.Credentials.from_service_account_info(
            creds_dict, scopes=['https://www.googleapis.com/auth/drive']
        )
        service = build('drive', 'v3', credentials=creds)
        return service
    except Exception as e:
        logger.error(f"GDrive Auth Error: {e}")
        return None

async def upload_to_gdrive(file_path: Path, file_name: str, message: Message):
    service = get_gdrive_service()
    if not service:
        return False, "Google Drive API is not configured."
    try:
        status_msg = await message.reply_text(f"Uploading `{file_name}` to Google Drive...", reply_markup=progress_keyboard(task_type='upload'))
        def gdrive_upload_thread():
            file_metadata = {'name': file_name}
            if GDRIVE_FOLDER_ID:
                file_metadata['parents'] = [GDRIVE_FOLDER_ID]
            media = MediaFileUpload(str(file_path), resumable=True)
            request = service.files().create(body=file_metadata, media_body=media, fields='id, webViewLink')
            response = None
            while response is None:
                status, response = request.next_chunk()
            return response
        response = await asyncio.to_thread(gdrive_upload_thread)
        link = response.get('webViewLink')
        await status_msg.edit(f"✅ **Successfully Uploaded to Google Drive:**\n\n🔗 **Link:** {link}")
        return True, link
    except Exception as e:
        logger.error(f"GDrive Upload Error: {e}")
        try:
            await status_msg.edit(f"❌ **Google Drive Upload Failed:**\n\n`{e}`")
        except:
            pass
        return False, str(e)

async def send_mode_tutorial(c, chat_id, mode_name):
    tutorials = {
        "upload_drive": (
            "🚀 **Google Drive Upload Mode - Tutorial**\n\n"
            "এই মোডটি চালু থাকলে আপনি টেলিগ্রামে যেই ভিডিও/ফাইল দিবেন বা লিঙ্কের মাধ্যমে ডাউনলোড করবেন, তা সরাসরি আপনার Google Drive এ আপলোড হবে।\n\n"
            "**কীভাবে ব্যবহার করবেন:**\n"
            "‣ যেকোনো ফাইল/ভিডিও ফরোয়ার্ড করুন বা সরাসরি পাঠান।\n"
            "‣ /upload_url দিয়ে লিঙ্ক দিলে সেটিও ড্রাইভে আপলোড হবে।\n"
            "‣ Google Drive এর লিঙ্ক দিলে Service Account ব্যবহার করে ডাউনলোড হবে (Private File-ও কাজ করবে)।\n"
            "‣ ব্যাচ মোড (`on`/`off`) দিয়ে অনেকগুলো ফাইল একসাথে Queue তে দিতে পারবেন।"
        ),
        "zip_file_download": (
            "📦 **ZIP File Download Mode - Tutorial**\n\n"
            "যেকোনো ZIP/RAR/7Z আর্কাইভ এক্সট্রাক্ট এবং আপলোড করার জন্য এটি ব্যবহৃত হয়।\n\n"
            "**কীভাবে ব্যবহার করবেন:**\n"
            "‣ আর্কাইভ লিঙ্ক বা টেলিগ্রাম ফাইল পাঠান।\n"
            "‣ ডাউনলোড ও এক্সট্রাক্ট হওয়ার পর ফাইলের তালিকা আসবে।\n"
            "‣ সিরিয়াল অনুযায়ী আপলোড করতে `1,3,5` বা `1-5` লিখুন।\n"
            "‣ অটোমেটিক সব আপলোড করতে `all` লিখুন।\n"
            "‣ ক্লিয়ার করতে `clear` লিখুন।"
        ),
        "convert": (
            "⚙️ **Convert Mode - Tutorial**\n\n"
            "ভিডিও/অডিও এর কোয়ালিটি, রেজুলেশন এবং বিটরেট পরিবর্তন করার জন্য।\n\n"
            "**কীভাবে ব্যবহার করবেন:**\n"
            "‣ যেকোনো ভিডিও বা লিঙ্ক পাঠান।\n"
            "‣ `list` লিখে জমা করা ফাইলগুলো দেখুন।\n"
            "‣ `next` লিখে পরবর্তী ফাইলের কাজ শুরু করুন।\n"
            "‣ সরাসরি বিটরেট কাস্টমাইজ করতে সংখ্যা (যেমন: `200`) লিখে রিপ্লাই দিন।"
        ),
        "download_only": (
            "📥 **Download Only Mode - Tutorial**\n\n"
            "ফাইল শুধু সার্ভারে ডাউনলোড হবে, টেলিগ্রামে আপলোড হবে না।\n\n"
            "**কীভাবে ব্যবহার করবেন:**\n"
            "‣ `link` পাঠালে ডাউনলোডের পর ডাইরেক্ট ডাউনলোড লিঙ্ক দেবে।\n"
            "‣ `t` পাঠালে ডাউনলোড না করেই সরাসরি Stream/Direct Link দেবে (দুটি লিঙ্ক থাকবে: ডাউনলোড এবং প্লে করার জন্য)।\n"
            "‣ `off` লিখে নরমাল ডাউনলোড মোডে ফিরে যান।"
        ),
        "batch_audio_add": (
            "🎵 **Batch Audio Add Mode - Tutorial**\n\n"
            "অনেকগুলো ভিডিওর সাথে একসাথে অডিও ট্র্যাক যোগ করার জন্য।\n\n"
            "**কীভাবে ব্যবহার করবেন:**\n"
            "‣ প্রথমে ভিডিওগুলো (List 1) পাঠান। তারপর `next` লিখুন।\n"
            "‣ এরপর অডিও সোর্স (List 2) পাঠান। আবার `next` লিখুন।\n"
            "‣ কাস্টম ম্যাপিংয়ের জন্য `1-5=1-5, 6=8` ফরম্যাটে লিখুন বা ডিফল্ট সিলেক্ট করুন।"
        )
    }
    if mode_name in tutorials:
        await c.send_message(chat_id, tutorials[mode_name])

def get_unique_path(base_dir: Path, filename: str) -> Path:
    target = base_dir / filename
    if not target.exists():
        return target
    stem = target.stem
    ext = target.suffix
    counter = 2
    while target.exists():
        target = base_dir / f"{stem} {counter:02d}{ext}"
        counter += 1
    return target

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

def process_dynamic_caption(uid, caption_template, is_first_setup=False):
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
    return caption_template

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

def generate_new_filename(original_name: str, uid: int = None) -> str:
    file_path = Path(original_name)
    file_ext = file_path.suffix.lower()
    file_ext = "." + file_ext.lstrip('.') if file_ext else ".mp4"
    if not file_ext or file_ext == '.':
        file_ext = ".mp4"
    if uid and uid in USER_FILENAMES:
        base_name = process_dynamic_text_no_increment(uid, USER_FILENAMES[uid])
    else:
        base_name = "[@TA_HD_Anime] Telegram Channel"
    return base_name + file_ext

def get_video_metadata(file_path: Path) -> dict:
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
    current = session['current_config']
    v_kbps = current['v_bitrate'] // 1000
    a_kbps = current['a_bitrate'] // 1000
    res = current['res']
    est_size = calculate_estimated_size(meta['duration'], v_kbps, a_kbps, len(meta['audio_streams']))
    orig_v_kbps = meta['v_bitrate'] // 1000
    saved_count = len(configs)
    text = (
        f"**🎥 Video Convert Options**\n\n"
        f"**File:** `{session['original_name']}`\n"
        f"**Original Size:** `{format_size(meta['filesize'])}`\n"
        f"**Original Video:** `{meta['width']}x{meta['height']} @ {orig_v_kbps} kbps`\n"
        f"**Audio Tracks:** `{len(meta['audio_streams'])}`\n\n"
        f"**--- Current Configuration ---**\n"
        f"**Target Quality:** `{res if res else 'Original'}p`\n"
        f"**Target Video Bitrate:** `{v_kbps} kbps`\n"
        f"**Target Audio Bitrate (All):** `{a_kbps} kbps`\n"
        f"**Estimated Size:** `{format_size(est_size)}`\n"
        f"**Saved Configs:** `{saved_count}`\n\n"
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
        InlineKeyboardButton("Add Quality ➕", callback_data=f"cv_add_{session_id}"),
        InlineKeyboardButton("Next Video ⏩", callback_data=f"cv_next_{session_id}")
    ])
    keyboard.append([
        InlineKeyboardButton("Select All & Convert 🚀", callback_data=f"cv_selectall_{session_id}"),
        InlineKeyboardButton("Cancel ❌", callback_data="cancel_single")
    ])
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

def progress_keyboard(task_type='download'):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("Cancel ❌", callback_data="cancel_single"),
         InlineKeyboardButton(f"All Cancel ❌", callback_data=f"cancel_all_{task_type}")]
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
    drive_status = "✅ ON" if uid in UPLOAD_DRIVE_MODE else "❌ OFF"
    waiting_count = sum(1 for data in PENDING_AUDIO_ORDERS.values() if data['uid'] == uid)
    waiting_status = f" ({waiting_count} orders pending)" if waiting_count > 0 else ""
    keyboard = [
        [InlineKeyboardButton(f"Convert Mode {convert_status}", callback_data="toggle_convert_mode")],
        [InlineKeyboardButton(f"MKV Audio Change Mode {audio_status}{waiting_status}", callback_data="toggle_audio_mode")],
        [InlineKeyboardButton(f"Batch Audio Add Mode {batch_audio_status}", callback_data="toggle_batch_audio_mode")],
        [InlineKeyboardButton(f"Edit Caption Mode {caption_status}", callback_data="toggle_caption_mode")],
        [InlineKeyboardButton(f"YT-DLP Mode {yt_dlp_status}", callback_data="toggle_ytdlp_mode")],
        [InlineKeyboardButton(f"ZIP Download Mode {zip_status}", callback_data="toggle_zip_mode")],
        [InlineKeyboardButton(f"Download Only Mode {dl_only_status}", callback_data="toggle_dl_only_mode")],
        [InlineKeyboardButton(f"Google Drive Mode {drive_status}", callback_data="toggle_drive_mode")]
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
        await message.edit_text(text, reply_markup=progress_keyboard(task_type='download' if 'Download' in action else 'upload'))
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

# ===== ORDERED OUTPUT HELPER FUNCTIONS =====

async def add_to_output_queue(uid, output_data):
    """Add an output item to the user's ordered output queue."""
    if uid not in USER_OUTPUT_QUEUES:
        USER_OUTPUT_QUEUES[uid] = asyncio.Queue()
        USER_OUTPUT_ORDER[uid] = 0
        USER_OUTPUT_LOCK[uid] = asyncio.Lock()
    await USER_OUTPUT_QUEUES[uid].put({
        'order': USER_OUTPUT_ORDER[uid],
        'data': output_data
    })
    USER_OUTPUT_ORDER[uid] += 1
    if uid not in USER_OUTPUT_WORKERS or USER_OUTPUT_WORKERS[uid].done():
        USER_OUTPUT_WORKERS[uid] = asyncio.create_task(process_output_queue(uid))

async def process_output_queue(uid):
    """Process the ordered output queue, sending items in the correct order."""
    if uid not in USER_OUTPUT_LOCK:
        USER_OUTPUT_LOCK[uid] = asyncio.Lock()
    async with USER_OUTPUT_LOCK[uid]:
        queue = USER_OUTPUT_QUEUES.get(uid)
        if not queue:
            return
        pending_items = {}
        next_order = 0
        while True:
            try:
                item = await queue.get()
                pending_items[item['order']] = item['data']
                while next_order in pending_items:
                    data = pending_items.pop(next_order)
                    try:
                        await data['send_func'](data['message'], data['file_path'], data['file_name'])
                    except Exception as e:
                        logger.error(f"Error sending output item {next_order}: {e}")
                    next_order += 1
                queue.task_done()
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.error(f"Output queue processing error: {e}")
                await asyncio.sleep(1)

async def add_to_convert_output_queue(uid, output_data):
    """Add a converted file to the user's ordered convert output queue."""
    if uid not in CONVERT_OUTPUT_QUEUES:
        CONVERT_OUTPUT_QUEUES[uid] = asyncio.Queue()
        CONVERT_OUTPUT_ORDER[uid] = 0
        CONVERT_OUTPUT_LOCK[uid] = asyncio.Lock()
    await CONVERT_OUTPUT_QUEUES[uid].put({
        'order': CONVERT_OUTPUT_ORDER[uid],
        'data': output_data
    })
    CONVERT_OUTPUT_ORDER[uid] += 1
    if uid not in CONVERT_OUTPUT_WORKERS or CONVERT_OUTPUT_WORKERS[uid].done():
        CONVERT_OUTPUT_WORKERS[uid] = asyncio.create_task(process_convert_output_queue(uid))

async def process_convert_output_queue(uid):
    """Process the ordered convert output queue, sending items in the correct order."""
    if uid not in CONVERT_OUTPUT_LOCK:
        CONVERT_OUTPUT_LOCK[uid] = asyncio.Lock()
    async with CONVERT_OUTPUT_LOCK[uid]:
        queue = CONVERT_OUTPUT_QUEUES.get(uid)
        if not queue:
            return
        pending_items = {}
        next_order = 0
        while True:
            try:
                item = await queue.get()
                pending_items[item['order']] = item['data']
                while next_order in pending_items:
                    data = pending_items.pop(next_order)
                    try:
                        await data['send_func'](data['message'], data['file_path'], data['file_name'])
                    except Exception as e:
                        logger.error(f"Error sending convert output item {next_order}: {e}")
                    next_order += 1
                queue.task_done()
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.error(f"Convert output queue processing error: {e}")
                await asyncio.sleep(1)

# ===== QUEUE SYSTEM WITH CONCURRENCY =====

async def add_to_queue(uid, c, m, original_name, is_url=False, url=None, is_yt_dlp=False, fmt=None, title=None, res=None, original_caption=None, task_type='upload'):
    """Add item to the appropriate queue (download or upload) with concurrency support."""
    if task_type == 'download':
        if uid not in USER_DOWNLOAD_QUEUES:
            USER_DOWNLOAD_QUEUES[uid] = asyncio.Queue()
        queue = USER_DOWNLOAD_QUEUES[uid]
        worker_dict = DOWNLOAD_WORKERS
        status_prefix = "Download"
    else:
        if uid not in USER_UPLOAD_QUEUES:
            USER_UPLOAD_QUEUES[uid] = asyncio.Queue()
        queue = USER_UPLOAD_QUEUES[uid]
        worker_dict = UPLOAD_WORKERS
        status_prefix = "Upload"
    
    try:
        if is_yt_dlp:
            status_msg = await m.reply_text(f"Queue item added for `{title}` ({res}p)...")
        else:
            status_msg = await m.reply_text(f"Queue item added for `{original_name}`...", reply_markup=progress_keyboard(task_type=task_type))
    except:
        status_msg = None
    
    await queue.put({
        'message': m,
        'original_name': original_name,
        'status_msg': status_msg,
        'is_url': is_url,
        'url': url,
        'is_yt_dlp': is_yt_dlp,
        'fmt': fmt,
        'title': title,
        'res': res,
        'original_caption': original_caption,
        'task_type': task_type,
        'order': USER_OUTPUT_ORDER.get(uid, 0)  # Capture order when added
    })
    
    # Start worker if not already running
    if uid not in worker_dict or worker_dict[uid].done():
        if task_type == 'download':
            worker_dict[uid] = asyncio.create_task(process_download_queue_handler(uid, c))
        else:
            worker_dict[uid] = asyncio.create_task(process_upload_queue_handler(uid, c))

async def process_download_queue_handler(uid, client):
    """Process download queue with concurrent downloads (max 5)."""
    queue = USER_DOWNLOAD_QUEUES.get(uid)
    if not queue:
        return
    
    # Process items concurrently using semaphore
    tasks = []
    while not queue.empty():
        while uid in USER_QUEUE_PAUSED:
            await asyncio.sleep(1)
        while uid in MISSING_EXT_QUEUE and len(MISSING_EXT_QUEUE[uid]) > 0:
            await asyncio.sleep(1)
        
        task_data = await queue.get()
        # Start a download task with semaphore
        task = asyncio.create_task(
            process_single_download_with_semaphore(uid, client, task_data)
        )
        tasks.append(task)
        queue.task_done()
    
    # Wait for all download tasks to complete
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)
    
    if uid in DOWNLOAD_WORKERS:
        del DOWNLOAD_WORKERS[uid]
    if uid in USER_DOWNLOAD_QUEUES:
        del USER_DOWNLOAD_QUEUES[uid]

async def process_single_download_with_semaphore(uid, client, task_data):
    """Process a single download with semaphore for concurrency control."""
    async with DOWNLOAD_SEMAPHORE:
        try:
            m = task_data.get('message')
            original_name = task_data.get('original_name')
            status_msg = task_data.get('status_msg')
            is_url = task_data.get('is_url', False)
            is_yt_dlp = task_data.get('is_yt_dlp', False)
            original_caption = task_data.get('original_caption')
            order = task_data.get('order', 0)
            
            cancel_event = asyncio.Event()
            TASKS.setdefault(uid, []).append(cancel_event)
            DOWNLOAD_TASKS.setdefault(uid, []).append(cancel_event)
            if status_msg:
                USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            
            if is_yt_dlp:
                url = task_data.get('url')
                fmt = task_data.get('fmt')
                title = task_data.get('title')
                res = task_data.get('res', 'Unknown')
                safe_title = re.sub(r"[\\/*?\"<>|:]", "_", title)
                if len(safe_title) > 100: safe_title = safe_title[:100]
                out_tmpl = str(TMP / f"{safe_title}.%(ext)s")
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
                        await status_msg.edit(f"Starting YT-DLP Download for {res}p...", reply_markup=progress_keyboard(task_type='download'))
                    downloaded_file = await asyncio.to_thread(run_dl)
                    actual_path = Path(downloaded_file)
                    if cancel_event.is_set() or not actual_path.exists():
                        raise Exception("Cancelled or download failed.")
                    if status_msg:
                        await status_msg.edit_text(f"Download complete ({res}p), adding to upload queue...", reply_markup=None)
                    original_name = actual_path.name
                    renamed_file = get_dynamic_filename(uid, original_name)
                    yt_caption = f"{title} - {res}p" if title else original_name
                    # Add to upload queue
                    await add_to_queue(uid, client, m, original_name, is_url=False, original_caption=yt_caption, task_type='upload')
                except Exception as e:
                    logger.error(f"YT-DLP Download Error: {e}")
                    raise e
            elif is_url:
                url = task_data.get('url')
                ext = Path(original_name).suffix
                if not ext:
                    keyboard = InlineKeyboardMarkup([
                        [InlineKeyboardButton(".zip", callback_data=f"extsel_{uid}_.zip"),
                         InlineKeyboardButton(".mkv", callback_data=f"extsel_{uid}_.mkv")],
                        [InlineKeyboardButton(".mp4", callback_data=f"extsel_{uid}_.mp4"),
                         InlineKeyboardButton(".rar", callback_data=f"extsel_{uid}_.rar")]
                    ])
                    if uid not in MISSING_EXT_QUEUE:
                        MISSING_EXT_QUEUE[uid] = []
                    if status_msg:
                        await status_msg.edit("No format found in URL. Please select format:", reply_markup=keyboard)
                    else:
                        status_msg = await m.reply_text("No format found in URL. Please select format:", reply_markup=keyboard)
                    task_data['status_msg'] = status_msg
                    MISSING_EXT_QUEUE[uid].append(task_data)
                    return
                else:
                    await download_and_process_generic(client, m, url, status_msg, cancel_event)
            else:
                # Telegram file download
                file_info = m.video or m.document
                tmp_path = get_unique_path(TMP, original_name)
                try:
                    if status_msg:
                        try:
                            await status_msg.edit("Downloading...", reply_markup=progress_keyboard(task_type='download'))
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
                        return
                    try:
                        if status_msg:
                            await status_msg.edit("Download complete, adding to upload queue...", reply_markup=None)
                    except Exception:
                        pass
                    renamed_file = get_dynamic_filename(uid, tmp_path.name)
                    await add_to_queue(uid, client, m, original_name, is_url=False, original_caption=original_caption, task_type='upload')
                except Exception as e:
                    if tmp_path.exists():
                        tmp_path.unlink()
                    raise e
        except Exception as e:
            logger.error(f"Download Error: {e}")
            USER_QUEUE_PAUSED.add(uid)
            markup = InlineKeyboardMarkup([
                [InlineKeyboardButton("Continue ▶️", callback_data="queue_continue"),
                 InlineKeyboardButton("Delete 🗑️", callback_data="queue_delete")]
            ])
            err_msg = f"Download Task Failed for `{original_name}`: {e}\n\n⚠️ **Queue is Paused.** Please select an option to resume or cancel remaining queue."
            try:
                if status_msg:
                    await status_msg.reply_text(err_msg, reply_markup=markup, quote=True)
                else:
                    await m.reply_text(err_msg, reply_markup=markup, quote=True)
            except:
                pass

async def process_upload_queue_handler(uid, client):
    """Process upload queue with concurrent uploads (max 5)."""
    queue = USER_UPLOAD_QUEUES.get(uid)
    if not queue:
        return
    
    # Process items concurrently using semaphore
    tasks = []
    while not queue.empty():
        while uid in USER_QUEUE_PAUSED:
            await asyncio.sleep(1)
        while uid in MISSING_EXT_QUEUE and len(MISSING_EXT_QUEUE[uid]) > 0:
            await asyncio.sleep(1)
        
        task_data = await queue.get()
        # Start an upload task with semaphore
        task = asyncio.create_task(
            process_single_upload_with_semaphore(uid, client, task_data)
        )
        tasks.append(task)
        queue.task_done()
    
    # Wait for all upload tasks to complete
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)
    
    if uid in UPLOAD_WORKERS:
        del UPLOAD_WORKERS[uid]
    if uid in USER_UPLOAD_QUEUES:
        del USER_UPLOAD_QUEUES[uid]

async def process_single_upload_with_semaphore(uid, client, task_data):
    """Process a single upload with semaphore for concurrency control."""
    async with UPLOAD_SEMAPHORE:
        try:
            m = task_data.get('message')
            original_name = task_data.get('original_name')
            status_msg = task_data.get('status_msg')
            original_caption = task_data.get('original_caption')
            order = task_data.get('order', 0)
            
            cancel_event = asyncio.Event()
            TASKS.setdefault(uid, []).append(cancel_event)
            UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
            if status_msg:
                USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            
            # Find the downloaded file in tmp directory
            downloaded_files = list(TMP.glob(f"*{original_name}*")) if original_name else []
            if not downloaded_files:
                # Try to find by name pattern
                name_pattern = re.sub(r'[^\w\s.-]', '_', original_name)
                downloaded_files = list(TMP.glob(f"*{name_pattern}*"))
            
            if not downloaded_files:
                # If file not found, maybe it's already processed or direct upload
                logger.warning(f"No downloaded file found for: {original_name}")
                return
            
            tmp_path = downloaded_files[0]
            renamed_file = get_dynamic_filename(uid, original_name)
            
            # Upload the file
            if uid in UPLOAD_DRIVE_MODE:
                ok, link = await upload_to_gdrive(tmp_path, renamed_file, m)
                if status_msg:
                    try: await client.delete_messages(m.chat.id, [status_msg.id])
                    except: pass
                if tmp_path.exists():
                    tmp_path.unlink()
            else:
                # Add to ordered output queue instead of direct upload
                output_data = {
                    'message': m,
                    'file_path': tmp_path,
                    'file_name': renamed_file,
                    'send_func': send_uploaded_file
                }
                await add_to_output_queue(uid, output_data)
                
                # Notify status
                if status_msg:
                    try:
                        await status_msg.edit(f"✅ Upload queued for: `{renamed_file}`")
                    except:
                        pass
                
        except Exception as e:
            logger.error(f"Upload Error: {e}")
            USER_QUEUE_PAUSED.add(uid)
            markup = InlineKeyboardMarkup([
                [InlineKeyboardButton("Continue ▶️", callback_data="queue_continue"),
                 InlineKeyboardButton("Delete 🗑️", callback_data="queue_delete")]
            ])
            err_msg = f"Upload Task Failed for `{original_name}`: {e}\n\n⚠️ **Queue is Paused.** Please select an option to resume or cancel remaining queue."
            try:
                if status_msg:
                    await status_msg.reply_text(err_msg, reply_markup=markup, quote=True)
                else:
                    await m.reply_text(err_msg, reply_markup=markup, quote=True)
            except:
                pass

async def send_uploaded_file(message, file_path, file_name):
    """Send an uploaded file to the user with proper processing."""
    uid = message.from_user.id
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    try:
        await process_file_and_upload(client, message, file_path, target_name=file_name, 
                                     original_download_name=file_name, 
                                     messages_to_delete=[], 
                                     cancel_event_passed=cancel_event, 
                                     passed_uid=uid, 
                                     default_caption=file_name, 
                                     original_caption_passed=file_name)
    except Exception as e:
        logger.error(f"Error sending uploaded file: {e}")

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
    for attempt in range(1, 6):
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
                        if attempt < 5:
                            await asyncio.sleep(2)
                            continue
                        return False, f"HTTP {resp.status}"
                    if resp.status in (200, 206):
                        ok, err = await download_stream(resp, out_path, message, cancel_event=cancel_event, original_name=original_name)
                        if ok: return True, None
                        else:
                            if attempt < 5: await asyncio.sleep(2); continue
                            return False, err
        except (aiohttp.ClientError, asyncio.TimeoutError, ssl.SSLError) as e:
            logger.warning(f"aiohttp attempt {attempt} failed: {e}")
            if attempt < 5:
                await asyncio.sleep(2)
                continue
            logger.info("Falling back to wget for download")
            return await download_with_wget(url, out_path, message, cancel_event, original_name)
        except Exception as e:
            logger.error(f"aiohttp unexpected error: {e}")
            if attempt < 5:
                await asyncio.sleep(2)
                continue
            return False, str(e)
    return await download_with_wget(url, out_path, message, cancel_event, original_name)

async def download_with_wget(url: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    cmd = ["wget", "-O", str(out_path), "--no-check-certificate", "--timeout=30", "--tries=3", url]
    if cancel_event:
        pass
    try:
        process = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
        if message:
            await message.edit_text("Downloading using wget (fallback)...", reply_markup=progress_keyboard(task_type='download'))
        await process.wait()
        if process.returncode == 0 and out_path.exists() and out_path.stat().st_size > 0:
            return True, None
        else:
            stderr = (await process.stderr.read()).decode()
            return False, f"wget failed: {stderr}"
    except Exception as e:
        return False, str(e)

async def download_drive_file(file_id: str, out_path: Path, message: Message = None, cancel_event: asyncio.Event = None, original_name=None):
    service = get_gdrive_service()
    if service:
        try:
            request = service.files().get_media(fileId=file_id)
            total = 0
            if out_path.exists():
                total = out_path.stat().st_size
            mode = "ab" if total > 0 else "wb"
            start_t = time.time()
            from googleapiclient.http import MediaIoBaseDownload
            import io
            def gdrive_download():
                with out_path.open(mode) as fh:
                    downloader = MediaIoBaseDownload(fh, request)
                    done = False
                    while done is False:
                        if cancel_event and cancel_event.is_set():
                            raise Exception("Cancelled")
                        status, done = downloader.next_chunk()
                        if status and message:
                            asyncio.run_coroutine_threadsafe(
                                progress_callback(status.resumable_progress, status.total_size, "Downloading from GDrive (API)...", message, start_t, original_name=original_name),
                                asyncio.get_event_loop()
                            )
            await asyncio.to_thread(gdrive_download)
            return True, None
        except Exception as e:
            logger.warning(f"GDrive API Download failed, falling back to public link: {e}")
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

def process_dynamic_text_no_increment(uid, caption_template):
    if uid not in USER_COUNTERS:
        USER_COUNTERS[uid] = {'uploads': 0, 'episode_numbers': {}, 'dynamic_counters': {}, 're_options_count': 0}
    counter_matches = re.findall(r"\[\s*(\(?\d+\)?)\s*\]", caption_template)
    for match in counter_matches:
        if match not in USER_COUNTERS[uid].get('dynamic_counters', {}):
            has_paren = match.startswith('(') and match.endswith(')')
            clean_match = re.sub(r'[()]', '', match)
            if 'dynamic_counters' not in USER_COUNTERS[uid]:
                USER_COUNTERS[uid]['dynamic_counters'] = {}
            USER_COUNTERS[uid]['dynamic_counters'][match] = {'value': int(clean_match), 'has_paren': has_paren}
    uploads = USER_COUNTERS[uid].get('uploads', 1)
    quality_match = re.search(r"\[re\s*\((.*?)\)\]", caption_template)
    if quality_match:
        options_str = quality_match.group(1)
        options = [opt.strip() for opt in options_str.split(',')]
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

def get_dynamic_filename(uid, original_name):
    file_path = Path(original_name)
    file_ext = file_path.suffix.lower()
    file_ext = "." + file_ext.lstrip('.') if file_ext and file_ext != '.' else ".mp4"
    if uid in USER_FILENAMES:
        base_name = process_dynamic_text_no_increment(uid, USER_FILENAMES[uid])
    else:
        base_name = "[@TA_HD_Anime] Telegram Channel"
    return base_name + file_ext

async def set_bot_commands():
    cmds = [
        BotCommand("start", "Start bot / Help"),
        BotCommand("upload_url", "Download & Upload file from URL (admin only)"),
        BotCommand("upload_drive", "Toggle Google Drive Upload Mode (admin only)"),
        BotCommand("download_only", "Download files to storage only (admin only)"),
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
        BotCommand("mode_check", "Check current mode status (admin only)"),
        BotCommand("progress_bar", "Toggle progress bar ON/OFF or Custom Interval (admin only)"),
        BotCommand("continue", "Resume paused queue / Restore buttons"),
        BotCommand("restart", "Show Storage info and Clear Data"),
        BotCommand("check", "Check ping status and connectivity"),
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
        if uid in UPLOAD_DRIVE_MODE:
            ok, link = await upload_to_gdrive(tmp_path, renamed_file, message)
            if status_msg_id:
                try: await client.delete_messages(message.chat.id, [status_msg_id])
                except: pass
            if tmp_path.exists():
                tmp_path.unlink()
            return
        await process_file_and_upload(client, message, tmp_path, target_name=renamed_file, original_download_name=original_download_name, messages_to_delete=[status_msg_id] if status_msg_id else [], cancel_event_passed=cancel_event, passed_uid=uid, default_caption=default_caption, original_caption_passed=original_caption)

async def process_queue_handler(uid, client):
    queue = USER_QUEUES[uid]
    while not queue.empty():
        while uid in USER_QUEUE_PAUSED:
            await asyncio.sleep(1)
        while uid in MISSING_EXT_QUEUE and len(MISSING_EXT_QUEUE[uid]) > 0:
            await asyncio.sleep(1)
        task_data = await queue.get()
        try:
            m = task_data.get('message')
            original_name = task_data.get('original_name')
            status_msg = task_data.get('status_msg')
            is_url = task_data.get('is_url', False)
            is_yt_dlp = task_data.get('is_yt_dlp', False)
            original_caption = task_data.get('original_caption')
            task_type = task_data.get('task_type', 'upload')
            cancel_event = asyncio.Event()
            TASKS.setdefault(uid, []).append(cancel_event)
            if task_type == 'download':
                DOWNLOAD_TASKS.setdefault(uid, []).append(cancel_event)
            else:
                UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
            if status_msg:
                USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            if is_yt_dlp:
                url = task_data.get('url')
                fmt = task_data.get('fmt')
                title = task_data.get('title')
                res = task_data.get('res', 'Unknown')
                safe_title = re.sub(r"[\\/*?\"<>|:]", "_", title)
                if len(safe_title) > 100: safe_title = safe_title[:100]
                out_tmpl = str(TMP / f"{safe_title}.%(ext)s")
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
                        await status_msg.edit(f"Starting YT-DLP Download for {res}p...", reply_markup=progress_keyboard(task_type='download'))
                    downloaded_file = await asyncio.to_thread(run_dl)
                    actual_path = Path(downloaded_file)
                    if cancel_event.is_set() or not actual_path.exists():
                         raise Exception("Cancelled or download failed.")
                    if status_msg:
                        await status_msg.edit_text(f"Download complete ({res}p), uploading...", reply_markup=None)
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
                ext = Path(original_name).suffix
                if not ext:
                    keyboard = InlineKeyboardMarkup([
                        [InlineKeyboardButton(".zip", callback_data=f"extsel_{uid}_.zip"),
                         InlineKeyboardButton(".mkv", callback_data=f"extsel_{uid}_.mkv")],
                        [InlineKeyboardButton(".mp4", callback_data=f"extsel_{uid}_.mp4"),
                         InlineKeyboardButton(".rar", callback_data=f"extsel_{uid}_.rar")]
                    ])
                    if uid not in MISSING_EXT_QUEUE:
                        MISSING_EXT_QUEUE[uid] = []
                    if status_msg:
                        await status_msg.edit("No format found in URL. Please select format:", reply_markup=keyboard)
                    else:
                        status_msg = await m.reply_text("No format found in URL. Please select format:", reply_markup=keyboard)
                    task_data['status_msg'] = status_msg
                    MISSING_EXT_QUEUE[uid].append(task_data)
                    continue
                else:
                    await download_and_process_generic(client, m, url, status_msg, cancel_event)
            else:
                file_info = m.video or m.document
                tmp_path = get_unique_path(TMP, original_name)
                try:
                    if status_msg:
                        try:
                            await status_msg.edit("Downloading...", reply_markup=progress_keyboard(task_type='download'))
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
                            await status_msg.edit("Download complete, uploading...", reply_markup=None)
                    except Exception:
                        pass
                    renamed_file = get_dynamic_filename(uid, tmp_path.name)
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

@app.on_callback_query(filters.regex(r"^extsel_"))
async def ext_select_cb(c, cb):
    uid = cb.from_user.id
    parts = cb.data.split('_')
    if str(uid) != parts[1]:
        await cb.answer("Not your prompt.", show_alert=True)
        return
    ext = parts[2]
    if uid in MISSING_EXT_QUEUE and len(MISSING_EXT_QUEUE[uid]) > 0:
        task_data = MISSING_EXT_QUEUE[uid].pop(0)
        task_data['original_name'] += ext
        await USER_QUEUES[uid].put(task_data)
        if task_data['status_msg']:
            await task_data['status_msg'].edit(f"Format selected: {ext}. Resuming download...")
        await cb.answer(f"Added {ext}", show_alert=False)
        if uid not in USER_WORKERS or USER_WORKERS[uid].done():
             USER_WORKERS[uid] = asyncio.create_task(process_queue_handler(uid, c))
    else:
        await cb.answer("Task not found.", show_alert=True)
        try: await cb.message.delete()
        except: pass

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
        'res': res,
        'task_type': 'download'  
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

@app.on_message(filters.command("start") & filters.private)
async def start_handler(c, m: Message):
    await set_bot_commands()
    text = (
        "Hi! I am URL uploader bot.\n\n"
        "Note: Many commands can only be used by the Admin (owner).\n\n"
        "Commands:\n"
        "/upload_url <url> - Download & Upload file from URL (admin only)\n"
        "/upload_drive - Toggle Google Drive Upload Mode (admin only)\n"
        "/download_only - Download files to storage only without upload (admin only)\n"
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
        "/mode_check - Check current mode status (admin only)\n"
        "/progress_bar - Toggle progress bar ON/OFF or Custom Interval (admin only)\n"
        "/continue - Resume paused queue / Restore buttons\n"
        "/restart - Show Storage info and Clear Data\n"
        "/check - Check ping status and connectivity\n"
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
    USER_THUMBS.clear()
    TASKS.clear()
    USER_TASK_EVENTS.clear()
    DOWNLOAD_TASKS.clear()
    UPLOAD_TASKS.clear()
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
    CONVERT_BATCH_LIST.clear()
    CONVERT_BATCH_UI_MSG.clear()
    ACTIVE_CONVERT_SESSION.clear()
    for s_id in list(CONVERT_SESSIONS.keys()):
        try:
            CONVERT_SESSIONS[s_id]['path'].unlink(missing_ok=True)
        except: pass
    CONVERT_SESSIONS.clear()
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
    DOWNLOAD_LINK_MODE.clear()
    DOWNLOAD_T_MODE.clear()
    UPLOAD_DRIVE_MODE.clear()
    MISSING_EXT_QUEUE.clear()
    EXTENSION_WAIT.clear()
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
    PATH_MODE_SELECTION.clear()
    PATH_CONVERT_LIST.clear()
    PATH_BATCH_AUDIO_LIST1.clear()
    PATH_BATCH_AUDIO_LIST2.clear()
    PATH_BATCH_AUDIO_STAGE.clear()
    PATH_ZIP_LISTS.clear()
    PATH_ZIP_CURRENT_LIST.clear()
    shutil.rmtree(TMP, ignore_errors=True)
    TMP.mkdir(parents=True, exist_ok=True)
    await cb.answer("Bot completely reset to fresh state!", show_alert=True)
    await cb.message.edit_text(cb.message.text + "\n\n*(Bot Fully Reset & Cleaned)*")

@app.on_message(filters.command("upload_drive") & filters.private)
async def toggle_upload_drive_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    if uid in UPLOAD_DRIVE_MODE:
        UPLOAD_DRIVE_MODE.discard(uid)
        await m.reply_text("Google Drive Upload Mode **OFF**.")
    else:
        UPLOAD_DRIVE_MODE.add(uid)
        await m.reply_text("Google Drive Upload Mode **ON**.")
        await send_mode_tutorial(c, m.chat.id, "upload_drive")

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
        await m.reply_text("ZIP File Download Mode **ON**.")
        await send_mode_tutorial(c, m.chat.id, "zip_file_download")

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
        CONVERT_ZIP_MODE.discard(uid)
        ACTIVE_CONVERT_SESSION.pop(uid, None)
        CONVERT_BATCH_LIST.pop(uid, None)
        await m.reply_text("Convert Mode **OFF**.")
    else:
        CONVERT_MODE.add(uid)
        CONVERT_BATCH_LIST[uid] = []
        await m.reply_text("Convert Mode **ON**.")
        await send_mode_tutorial(c, m.chat.id, "convert")

@app.on_message(filters.command("download_only") & filters.private)
async def toggle_download_only_mode(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    if uid in DOWNLOAD_ONLY_MODE:
        DOWNLOAD_ONLY_MODE.discard(uid)
        DOWNLOAD_LINK_MODE.discard(uid)
        DOWNLOAD_T_MODE.discard(uid)
        await m.reply_text("Download Only Mode **OFF**.")
    else:
        DOWNLOAD_ONLY_MODE.add(uid)
        await m.reply_text("Download Only Mode **ON**.")
        await send_mode_tutorial(c, m.chat.id, "download_only")

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
        if uid in UPLOAD_DRIVE_MODE:
            original_name = m.photo.file_id + ".jpg"
            await add_to_queue(uid, c, m, original_name, is_url=False, original_caption=m.caption)

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
        await m.reply_text("Batch Audio Add Mode **ON**.")
        await send_mode_tutorial(c, m.chat.id, "batch_audio_add")

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
    drive_status = "✅ ON" if uid in UPLOAD_DRIVE_MODE else "❌ OFF"
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
        f"8. **Google Drive Mode:** `{drive_status}`\n"
        "Click the buttons below to toggle modes."
    )
    await m.reply_text(status_text, reply_markup=mode_check_keyboard(uid), parse_mode=ParseMode.MARKDOWN)

@app.on_callback_query(filters.regex("toggle_(audio|caption|ytdlp|zip|convert|batch_audio|dl_only|drive)_mode"))
async def mode_toggle_callback(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("You are not authorized.", show_alert=True)
        return
    action = cb.data
    message = ""
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
    elif action == "toggle_dl_only_mode":
        if uid in DOWNLOAD_ONLY_MODE:
            DOWNLOAD_ONLY_MODE.discard(uid)
            DOWNLOAD_LINK_MODE.discard(uid)
            DOWNLOAD_T_MODE.discard(uid)
            message = "Download Only Mode OFF."
        else:
            DOWNLOAD_ONLY_MODE.add(uid)
            message = "Download Only Mode ON."
    elif action == "toggle_drive_mode":
        if uid in UPLOAD_DRIVE_MODE:
            UPLOAD_DRIVE_MODE.discard(uid)
            message = "Google Drive Upload Mode OFF."
        else:
            UPLOAD_DRIVE_MODE.add(uid)
            message = "Google Drive Upload Mode ON."
    try:
        audio_status = "✅ ON" if uid in MKV_AUDIO_CHANGE_MODE else "❌ OFF"
        caption_status = "✅ ON" if uid in EDIT_CAPTION_MODE else "❌ OFF"
        yt_dlp_status = "✅ ON" if uid in YT_DLP_MODE else "❌ OFF"
        zip_status = "✅ ON" if uid in ZIP_DOWNLOAD_MODE else "❌ OFF"
        convert_status = "✅ ON" if uid in CONVERT_MODE else "❌ OFF"
        batch_audio_status = "✅ ON" if uid in BATCH_AUDIO_MODE else "❌ OFF"
        dl_only_status = "✅ ON" if uid in DOWNLOAD_ONLY_MODE else "❌ OFF"
        drive_status = "✅ ON" if uid in UPLOAD_DRIVE_MODE else "❌ OFF"
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
            f"8. **Google Drive Mode:** `{drive_status}`\n"
            "Click the buttons below to toggle modes."
        )
        await cb.message.edit_text(status_text, reply_markup=mode_check_keyboard(uid), parse_mode=ParseMode.MARKDOWN)
        await cb.answer(message, show_alert=True)
    except Exception as e:
        logger.error(f"Callback edit error: {e}")
        await cb.answer(message, show_alert=True)

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
            await execute_zip_download_and_extract(c, task_data['message'], task_data.get('url'), task_data.get('local_path'), task_data.get('target_list'), is_dl_only=task_data.get('is_dl_only', False))
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
            break 
        fpath = files[idx - 1]
        if not fpath.exists(): continue
        original_name = fpath.name
        renamed_file = get_dynamic_filename(uid, original_name)
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
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

async def execute_zip_download_and_extract(c, m, url=None, local_path=None, target_list=None, is_dl_only=False):
    uid = m.from_user.id
    status_msg = await c.send_message(m.chat.id, "Downloading Queue Item..." if url else "Processing Local Archive...", reply_markup=progress_keyboard(task_type='download'))
    safe_name = f"zip_dl_{uid}_{int(time.time())}"
    if url:
        original_name_pass = await get_filename_from_url(url)
    elif local_path:
        original_name_pass = Path(local_path).name
    else:
        original_name_pass = m.video.file_name if getattr(m, 'video', None) else (m.document.file_name if getattr(m, 'document', None) else "telegram_file.zip")
    if not Path(original_name_pass).suffix:
        original_name_pass += ".zip"
    safe_name = re.sub(r"[\\/*?\"<>|:]", "_", original_name_pass)
    tmp_in = get_unique_path(TMP, safe_name)
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    DOWNLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    try:
        ok, err = False, None
        if local_path:
            shutil.copy(local_path, tmp_in)
            ok = True
        elif url:
            if is_drive_url(url):
                fid = extract_drive_id(url)
                if fid: ok, err = await download_drive_file(fid, tmp_in, status_msg, cancel_event, original_name=original_name_pass)
            else:
                ok, err = await download_url_generic(url, tmp_in, status_msg, cancel_event, original_name=original_name_pass)
        else: 
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
            if is_dl_only:
                if uid in DOWNLOAD_LINK_MODE:
                    link = f"{PUBLIC_BASE_URL}/dl/{urllib.parse.quote(tmp_in.name)}"
                    await status_msg.edit(f"✅ **File Downloaded:** `{tmp_in.name}`\n🔗 **Direct Link:** {link}")
                else:
                    await status_msg.edit(f"✅ **File Downloaded:** `{tmp_in.name}`\nSaved to local storage.")
                return
            await status_msg.edit("Non-archive file detected. Handling as direct video...", reply_markup=None)
            if target_list is not None:
                new_path = get_unique_path(tmp_in.parent, original_name_pass)
                shutil.move(tmp_in, new_path)
                target_list.append({'path': str(new_path), 'name': new_path.name})
                await status_msg.edit(f"File added to list. Total: {len(target_list)}")
                return
            ZIP_READY_LIST.setdefault(uid, []).append({
                'root_dir': None,
                'files_to_upload': [tmp_in]
            })
            await check_and_show_next_zip(c, m.chat.id, uid)
            return
        await status_msg.edit("Extracting Archive file...", reply_markup=progress_keyboard(task_type='download'))
        ext_dir = TMP / f"zip_ext_{uid}_{int(time.time())}"
        ext_dir.mkdir(parents=True, exist_ok=True)
        start_t = time.time()
        extracted = False
        ext = tmp_in.suffix.lower()
        try:
            if ext == '.zip':
                with zipfile.ZipFile(tmp_in, 'r') as zip_ref:
                    total_size = sum(info.file_size for info in zip_ref.infolist())
                    extracted_size = 0
                    for info in zip_ref.infolist():
                        if cancel_event.is_set(): break
                        await asyncio.to_thread(zip_ref.extract, info, ext_dir)
                        extracted_size += info.file_size
                        await progress_callback(extracted_size, total_size, "Extracting ZIP...", status_msg, start_t)
                extracted = True
            elif ext == '.rar' and 'rarfile' in globals():
                with rarfile.RarFile(tmp_in, 'r') as rar_ref:
                    total_size = sum(info.file_size for info in rar_ref.infolist())
                    extracted_size = 0
                    for info in rar_ref.infolist():
                        if cancel_event.is_set(): break
                        await asyncio.to_thread(rar_ref.extract, info, ext_dir)
                        extracted_size += info.file_size
                        await progress_callback(extracted_size, total_size, "Extracting RAR...", status_msg, start_t)
                extracted = True
            elif ext == '.7z' and 'py7zr' in globals():
                with py7zr.SevenZipFile(tmp_in, mode='r') as sz_ref:
                    await asyncio.to_thread(sz_ref.extractall, path=ext_dir)
                extracted = True
            elif ext in ['.tar', '.gz', '.bz2', '.xz']:
                with tarfile.open(tmp_in, 'r:*') as tar_ref:
                    await asyncio.to_thread(tar_ref.extractall, path=ext_dir)
                extracted = True
            else:
                try:
                    cmd = ['7z', 'x', str(tmp_in), '-p-', '-aoa', f'-o{ext_dir}']
                    process = await asyncio.create_subprocess_exec(*cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    await process.communicate()
                    if process.returncode == 0:
                        extracted = True
                except Exception:
                    pass
                if not extracted:
                    await asyncio.to_thread(shutil.unpack_archive, str(tmp_in), str(ext_dir))
                    extracted = True
        except Exception as e:
            logger.warning(f"Primary extraction failed: {e}, trying fallback methods")
            extracted = False
        if not extracted:
            tried = set()
            for method in ['.zip', '.rar', '.7z', '.tar', '.gz', '.bz2', '.xz', 'generic']:
                if method in tried: continue
                tried.add(method)
                try:
                    if method == '.zip':
                        with zipfile.ZipFile(tmp_in, 'r') as zip_ref:
                            await asyncio.to_thread(zip_ref.extractall, ext_dir)
                    elif method == '.rar' and 'rarfile' in globals():
                        with rarfile.RarFile(tmp_in, 'r') as rar_ref:
                            await asyncio.to_thread(rar_ref.extractall, ext_dir)
                    elif method == '.7z' and 'py7zr' in globals():
                        with py7zr.SevenZipFile(tmp_in, mode='r') as sz_ref:
                            await asyncio.to_thread(sz_ref.extractall, path=ext_dir)
                    elif method in ['.tar', '.gz', '.bz2', '.xz']:
                        with tarfile.open(tmp_in, 'r:*') as tar_ref:
                            await asyncio.to_thread(tar_ref.extractall, path=ext_dir)
                    elif method == 'generic':
                        cmd = ['7z', 'x', str(tmp_in), '-p-', '-aoa', f'-o{ext_dir}']
                        process = await asyncio.create_subprocess_exec(*cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                        await process.communicate()
                        if process.returncode != 0:
                            raise Exception("7z failed")
                    else:
                        continue
                    extracted = True
                    break
                except Exception:
                    continue
        if not extracted:
            raise Exception("All extraction methods failed. Archive may be corrupted or unsupported.")
        found_zip = True
        while found_zip:
            found_zip = False
            for root, dirs, files in os.walk(ext_dir):
                for file in files:
                    nested_zip_path = Path(root) / file
                    if is_archive_file(nested_zip_path):
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
                            else:
                                try:
                                    cmd = ['7z', 'x', str(nested_zip_path), '-p-', '-aoa', f'-o{root}']
                                    process = await asyncio.create_subprocess_exec(*cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                                    await process.communicate()
                                    if process.returncode != 0: raise Exception("7z fail")
                                except Exception:
                                    await asyncio.to_thread(shutil.unpack_archive, str(nested_zip_path), str(root))
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
        if is_dl_only:
            try: await status_msg.delete()
            except: pass
            if uid in DOWNLOAD_LINK_MODE:
                link_text = "**Extracted Files Direct Links:**\n"
                for f in all_files:
                    link = f"{PUBLIC_BASE_URL}/dl/{urllib.parse.quote(f.relative_to(TMP).as_posix())}"
                    link_text += f"‣ `{f.name}`\n🔗 {link}\n"
                await c.send_message(m.chat.id, link_text, disable_web_page_preview=True)
            else:
                await c.send_message(m.chat.id, f"✅ **Extracted {len(all_files)} files successfully.**\nSaved to local storage.")
            return
        if target_list is not None:
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
        if cancel_event in DOWNLOAD_TASKS.get(uid, []):
            DOWNLOAD_TASKS[uid].remove(cancel_event)

async def send_batch_audio_list_page(c, chat_id, uid, list_id, page=0, msg_id=None):
    if list_id == 'list1':
        target_list = BATCH_AUDIO_LIST1.get(uid, [])
        list_name = "List 1 (Base Videos)"
    elif list_id == 'list2':
        target_list = BATCH_AUDIO_LIST2.get(uid, [])
        list_name = "List 2 (Audio Sources)"
    else:
        target_list = CONVERT_BATCH_LIST.get(uid, [])
        list_name = "Convert Batch List"
    per_page = 10
    total_items = len(target_list)
    total_pages = max(1, math.ceil(total_items / per_page))
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    start_idx = page * per_page
    end_idx = min(start_idx + per_page, total_items)
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

async def send_path_ui(c, chat_id, uid, msg_id=None, page=0):
    current = NAV_PATHS[uid]['current']
    try:
        items = list(current.iterdir())
        items.sort(key=lambda x: (not x.is_dir(), x.name.lower()))
    except Exception as e:
        items = []
    NAV_PATHS[uid]['items'] = items
    NAV_PATHS[uid]['page'] = page
    per_page = 20
    total_items = len(items)
    total_pages = max(1, math.ceil(total_items / per_page))
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    start_idx = page * per_page
    end_idx = min(start_idx + per_page, total_items)
    text_lines = [f"**File Manager (Page {page+1}/{total_pages})**\n**Current Path:** `{current}`\n"]
    text_lines.append("**b.** ⬆️ Go Back (Up)")
    for i in range(start_idx, end_idx):
        item = items[i]
        name = item.name
        if item.is_dir():
            text_lines.append(f"**{i+1}.** 📁 `{name}`")
        else:
            text_lines.append(f"**{i+1}.** 📄 `{name}`")
    text_lines.append("\n**Options:**")
    text_lines.append("‣ Send `b` to go back up.")
    text_lines.append("‣ Send a number to open folder/select file (e.g., `1`).")
    text_lines.append("‣ Send `1-3,5` to upload multiple files serially via queue.")
    text_lines.append("‣ Send `e 1` to extract archive and delete original.")
    text_lines.append("‣ Send `d 1-3,all` to delete selected items/all items.")
    text_lines.append("‣ Send `l 1-3,all` to get direct download links.")
    text_lines.append("‣ Send `r zip 1` or `r 1-3,all` to rename based on saved file format.")
    text_lines.append("‣ Send `np` or `pp` for Next/Prev Page.")
    text_lines.append("‣ Send `close` to exit manager.")
    full_text = "\n".join(text_lines)
    keyboard = []
    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton("⬅️ Previous", callback_data=f"path_page_{uid}_{page-1}"))
    nav_row.append(InlineKeyboardButton(f"{page+1}/{total_pages}", callback_data="ignore"))
    if page < total_pages - 1:
        nav_row.append(InlineKeyboardButton("Next ➡️", callback_data=f"path_page_{uid}_{page+1}"))
    keyboard.append(nav_row)
    keyboard.append([InlineKeyboardButton("⬆️ Back", callback_data=f"path_back_{uid}")])
    mode_convert = PATH_MODE_SELECTION.get(uid) == 'convert'
    mode_batch_audio = PATH_MODE_SELECTION.get(uid) == 'batch_audio'
    mode_zip = PATH_MODE_SELECTION.get(uid) == 'zip'
    keyboard.append([
        InlineKeyboardButton(f"{'✅ ' if mode_convert else ''}Convert", callback_data=f"path_mode_{uid}_convert"),
        InlineKeyboardButton(f"{'✅ ' if mode_batch_audio else ''}BatchAudio", callback_data=f"path_mode_{uid}_batch_audio"),
        InlineKeyboardButton(f"{'✅ ' if mode_zip else ''}ZIP Upload", callback_data=f"path_mode_{uid}_zip")
    ])
    if mode_batch_audio and PATH_BATCH_AUDIO_STAGE.get(uid) == 1:
        keyboard.append([InlineKeyboardButton("Next List ➡️", callback_data=f"path_nextlist_{uid}")])
    elif mode_zip:
        keyboard.append([InlineKeyboardButton("Next List ➕", callback_data=f"path_nextlist_{uid}")])
    keyboard.append([
        InlineKeyboardButton("All Select", callback_data=f"path_all_{uid}"),
        InlineKeyboardButton("Done", callback_data=f"path_done_{uid}")
    ])
    keyboard.append([InlineKeyboardButton("Close ❌", callback_data=f"path_close_{uid}")])
    markup = InlineKeyboardMarkup(keyboard)
    chunks = [full_text[i:i+4000] for i in range(0, len(full_text), 4000)]
    for idx, chunk in enumerate(chunks):
        if msg_id and idx == 0:
            try:
                await c.edit_message_text(chat_id, msg_id, chunk, reply_markup=markup)
                NAV_PATHS[uid]['msg_id'] = msg_id
            except:
                new_msg = await c.send_message(chat_id, chunk, reply_markup=markup if idx==0 else None)
                NAV_PATHS[uid]['msg_id'] = new_msg.id
        else:
            new_msg = await c.send_message(chat_id, chunk, reply_markup=markup if idx==0 else None)
            if idx == 0:
                NAV_PATHS[uid]['msg_id'] = new_msg.id

async def process_path_uploads(uid, c, m, files_to_upload):
    for fpath in files_to_upload:
        while uid in USER_QUEUE_PAUSED:
            await asyncio.sleep(1)
        if not fpath.suffix:
            EXTENSION_WAIT[uid] = {
                'file_path': fpath,
                'message': m,
                'callback': process_path_uploads,
                'args': (uid, c, m, files_to_upload),  
                'kwargs': {}
            }
            keyboard = InlineKeyboardMarkup([
                [InlineKeyboardButton(".zip", callback_data=f"extsel_local_{uid}_.zip"),
                 InlineKeyboardButton(".mkv", callback_data=f"extsel_local_{uid}_.mkv")],
                [InlineKeyboardButton(".mp4", callback_data=f"extsel_local_{uid}_.mp4"),
                 InlineKeyboardButton(".rar", callback_data=f"extsel_local_{uid}_.rar")]
            ])
            await c.send_message(m.chat.id, f"File `{fpath.name}` has no extension. Please select a format:", reply_markup=keyboard)
            return
        original_name = fpath.name
        renamed_file = get_dynamic_filename(uid, original_name)
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
        try:
            status_msg = await c.send_message(m.chat.id, f"Uploading `{original_name}`...", reply_markup=progress_keyboard(task_type='upload'))
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

@app.on_callback_query(filters.regex(r"^path_page_"))
async def path_page_cb(c, cb):
    uid = int(cb.data.split('_')[2])
    page = int(cb.data.split('_')[3])
    if uid != cb.from_user.id:
        await cb.answer("Not your session.", show_alert=True)
        return
    if uid in NAV_PATHS:
        await send_path_ui(c, cb.message.chat.id, uid, msg_id=cb.message.id, page=page)
        await cb.answer()

@app.on_callback_query(filters.regex(r"^path_back_"))
async def path_back_cb(c, cb):
    uid = int(cb.data.split('_')[2])
    if uid != cb.from_user.id:
        await cb.answer("Not your session.", show_alert=True)
        return
    if uid in NAV_PATHS:
        current = NAV_PATHS[uid]['current']
        if current != TMP:
            NAV_PATHS[uid]['current'] = current.parent
        await send_path_ui(c, cb.message.chat.id, uid, msg_id=cb.message.id, page=0)
        await cb.answer()

@app.on_callback_query(filters.regex(r"^path_mode_"))
async def path_mode_cb(c, cb):
    uid = int(cb.data.split('_')[2])
    mode = cb.data.split('_')[3]
    if uid != cb.from_user.id:
        await cb.answer("Not your session.", show_alert=True)
        return
    current = PATH_MODE_SELECTION.get(uid)
    if current == mode:
        PATH_MODE_SELECTION.pop(uid, None)
        PATH_CONVERT_LIST.pop(uid, None)
        PATH_BATCH_AUDIO_LIST1.pop(uid, None)
        PATH_BATCH_AUDIO_LIST2.pop(uid, None)
        PATH_BATCH_AUDIO_STAGE.pop(uid, None)
        PATH_ZIP_LISTS.pop(uid, None)
        PATH_ZIP_CURRENT_LIST.pop(uid, None)
        await cb.answer(f"{mode} unselected.", show_alert=False)
    else:
        PATH_MODE_SELECTION[uid] = mode
        if mode == 'convert':
            PATH_CONVERT_LIST[uid] = []
        elif mode == 'batch_audio':
            PATH_BATCH_AUDIO_LIST1[uid] = []
            PATH_BATCH_AUDIO_LIST2[uid] = []
            PATH_BATCH_AUDIO_STAGE[uid] = 1
        elif mode == 'zip':
            PATH_ZIP_LISTS[uid] = [[]]
            PATH_ZIP_CURRENT_LIST[uid] = 0
        await cb.answer(f"{mode} selected.", show_alert=False)
    await send_path_ui(c, cb.message.chat.id, uid, msg_id=cb.message.id, page=NAV_PATHS[uid]['page'])

@app.on_callback_query(filters.regex(r"^path_nextlist_"))
async def path_nextlist_cb(c, cb):
    uid = int(cb.data.split('_')[2])
    if uid != cb.from_user.id:
        await cb.answer("Not your session.", show_alert=True)
        return
    mode = PATH_MODE_SELECTION.get(uid)
    if mode == 'batch_audio':
        PATH_BATCH_AUDIO_STAGE[uid] = 2
        await cb.answer("Switched to List 2. Now add audio source files.", show_alert=False)
    elif mode == 'zip':
        if uid not in PATH_ZIP_LISTS:
            PATH_ZIP_LISTS[uid] = [[]]
        PATH_ZIP_LISTS[uid].append([])
        PATH_ZIP_CURRENT_LIST[uid] = len(PATH_ZIP_LISTS[uid]) - 1
        await cb.answer(f"Created new list {PATH_ZIP_CURRENT_LIST[uid]+1}.", show_alert=False)
    else:
        await cb.answer("No active mode for Next List.", show_alert=True)
        return
    await send_path_ui(c, cb.message.chat.id, uid, msg_id=cb.message.id, page=NAV_PATHS[uid]['page'])

@app.on_callback_query(filters.regex(r"^path_all_"))
async def path_all_cb(c, cb):
    uid = int(cb.data.split('_')[2])
    if uid != cb.from_user.id:
        await cb.answer("Not your session.", show_alert=True)
        return
    if uid not in NAV_PATHS:
        await cb.answer("No active path.", show_alert=True)
        return
    current = NAV_PATHS[uid]['current']
    all_files = [f for f in current.iterdir() if f.is_file()]
    if not all_files:
        await cb.answer("No files in this directory.", show_alert=True)
        return
    mode = PATH_MODE_SELECTION.get(uid)
    if mode == 'convert':
        if uid not in PATH_CONVERT_LIST:
            PATH_CONVERT_LIST[uid] = []
        for f in all_files:
            PATH_CONVERT_LIST[uid].append(f)
        await cb.answer(f"Added {len(all_files)} files to Convert list.", show_alert=False)
    elif mode == 'batch_audio':
        stage = PATH_BATCH_AUDIO_STAGE.get(uid, 1)
        if stage == 1:
            if uid not in PATH_BATCH_AUDIO_LIST1:
                PATH_BATCH_AUDIO_LIST1[uid] = []
            for f in all_files:
                PATH_BATCH_AUDIO_LIST1[uid].append(f)
            await cb.answer(f"Added {len(all_files)} files to List 1.", show_alert=False)
        else:
            if uid not in PATH_BATCH_AUDIO_LIST2:
                PATH_BATCH_AUDIO_LIST2[uid] = []
            for f in all_files:
                PATH_BATCH_AUDIO_LIST2[uid].append(f)
            await cb.answer(f"Added {len(all_files)} files to List 2.", show_alert=False)
    elif mode == 'zip':
        if uid not in PATH_ZIP_LISTS or not PATH_ZIP_LISTS[uid]:
            PATH_ZIP_LISTS[uid] = [[]]
            PATH_ZIP_CURRENT_LIST[uid] = 0
        current_list_idx = PATH_ZIP_CURRENT_LIST[uid]
        for f in all_files:
            PATH_ZIP_LISTS[uid][current_list_idx].append(f)
        await cb.answer(f"Added {len(all_files)} files to current ZIP list.", show_alert=False)
    else:
        await process_path_uploads(uid, c, cb.message, all_files)
        await cb.answer("Uploading all files...", show_alert=False)
        if uid in NAV_PATHS and 'msg_id' in NAV_PATHS[uid]:
            try:
                await c.delete_messages(cb.message.chat.id, NAV_PATHS[uid]['msg_id'])
            except:
                pass
            NAV_PATHS.pop(uid, None)
    if mode:
        await send_path_ui(c, cb.message.chat.id, uid, msg_id=cb.message.id, page=NAV_PATHS[uid]['page'])

@app.on_callback_query(filters.regex(r"^path_done_"))
async def path_done_cb(c, cb):
    uid = int(cb.data.split('_')[2])
    if uid != cb.from_user.id:
        await cb.answer("Not your session.", show_alert=True)
        return
    mode = PATH_MODE_SELECTION.get(uid)
    if not mode:
        await cb.answer("No mode selected. Please select a mode first.", show_alert=True)
        return
    if mode == 'convert':
        if uid not in PATH_CONVERT_LIST or not PATH_CONVERT_LIST[uid]:
            await cb.answer("Convert list is empty.", show_alert=True)
            return
        first_file = PATH_CONVERT_LIST[uid][0]
        batch_files = [{'path': str(f), 'name': f.name} for f in PATH_CONVERT_LIST[uid]]
        await handle_convert_input(c, cb.message, override_path=str(first_file), batch_list=batch_files)
        await cb.answer("Convert started.", show_alert=False)
        PATH_MODE_SELECTION.pop(uid, None)
        PATH_CONVERT_LIST.pop(uid, None)
        if uid in NAV_PATHS and 'msg_id' in NAV_PATHS[uid]:
            try:
                await c.delete_messages(cb.message.chat.id, NAV_PATHS[uid]['msg_id'])
            except:
                pass
            NAV_PATHS.pop(uid, None)
    elif mode == 'batch_audio':
        if uid not in PATH_BATCH_AUDIO_LIST1 or not PATH_BATCH_AUDIO_LIST1[uid]:
            await cb.answer("List 1 is empty.", show_alert=True)
            return
        if uid not in PATH_BATCH_AUDIO_LIST2 or not PATH_BATCH_AUDIO_LIST2[uid]:
            await cb.answer("List 2 is empty. Use 'Next List' to switch to List 2 and add files.", show_alert=True)
            return
        list1_dicts = [{'path': str(f), 'name': f.name} for f in PATH_BATCH_AUDIO_LIST1[uid]]
        list2_dicts = [{'path': str(f), 'name': f.name} for f in PATH_BATCH_AUDIO_LIST2[uid]]
        BATCH_AUDIO_LIST1[uid] = list1_dicts
        BATCH_AUDIO_LIST2[uid] = list2_dicts
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
        list1_chunks = chunk_and_send(list1_dicts, "List 1 (Base Videos)")
        list2_chunks = chunk_and_send(list2_dicts, "List 2 (Audio Sources)")
        for c_msg in list1_chunks: await cb.message.reply_text(c_msg)
        for c_msg in list2_chunks: await cb.message.reply_text(c_msg)
        keyboard = InlineKeyboardMarkup([
            [InlineKeyboardButton("Upload All 🚀", callback_data="baud_list_ok")],
            [InlineKeyboardButton("Cancel ❌", callback_data="baud_list_cancel")]
        ])
        await cb.message.reply_text(
            "**Mapping Rules:**\n"
            "‣ Default matches 1 to 1, 2 to 2.\n"
            "‣ Custom mapping: send `1-13=1-13, 14=16, 15=14`\n"
            "‣ Click Upload All or send custom string.",
            reply_markup=keyboard
        )
        PATH_MODE_SELECTION.pop(uid, None)
        PATH_BATCH_AUDIO_LIST1.pop(uid, None)
        PATH_BATCH_AUDIO_LIST2.pop(uid, None)
        PATH_BATCH_AUDIO_STAGE.pop(uid, None)
        if uid in NAV_PATHS and 'msg_id' in NAV_PATHS[uid]:
            try:
                await c.delete_messages(cb.message.chat.id, NAV_PATHS[uid]['msg_id'])
            except:
                pass
            NAV_PATHS.pop(uid, None)
        await cb.answer("Batch audio started.", show_alert=False)
    elif mode == 'zip':
        if uid not in PATH_ZIP_LISTS or not any(PATH_ZIP_LISTS[uid]):
            await cb.answer("ZIP lists are empty.", show_alert=True)
            return
        all_lists = PATH_ZIP_LISTS[uid]
        total_files = sum(len(lst) for lst in all_lists)
        status_msg = await cb.message.reply_text(f"Starting upload of {total_files} files across {len(all_lists)} lists...")
        for list_idx, file_list in enumerate(all_lists):
            if not file_list:
                continue
            await cb.message.reply_text(f"Uploading list {list_idx+1}/{len(all_lists)} ({len(file_list)} files)...")
            await process_path_uploads(uid, c, cb.message, file_list)
        PATH_MODE_SELECTION.pop(uid, None)
        PATH_ZIP_LISTS.pop(uid, None)
        PATH_ZIP_CURRENT_LIST.pop(uid, None)
        await cb.message.reply_text("All ZIP lists uploaded.")
        if uid in NAV_PATHS and 'msg_id' in NAV_PATHS[uid]:
            try:
                await c.delete_messages(cb.message.chat.id, NAV_PATHS[uid]['msg_id'])
            except:
                pass
            NAV_PATHS.pop(uid, None)
        await cb.answer("ZIP upload completed.", show_alert=False)

@app.on_callback_query(filters.regex(r"^path_close_"))
async def path_close_cb(c, cb):
    uid = int(cb.data.split('_')[2])
    if uid != cb.from_user.id:
        await cb.answer("Not your session.", show_alert=True)
        return
    if uid in NAV_PATHS:
        try:
            await c.delete_messages(cb.message.chat.id, NAV_PATHS[uid]['msg_id'])
        except:
            pass
        NAV_PATHS.pop(uid, None)
    await cb.answer("File Manager closed.", show_alert=False)

async def process_convert_queue_worker(uid, client):
    if uid not in CONVERT_LOCKS:
        CONVERT_LOCKS[uid] = asyncio.Lock()
    pass

async def handle_convert_input(c, m, url=None, file_info=None, override_path=None, batch_list=None):
    uid = m.from_user.id
    status_msg = await m.reply_text("📥 Initializing file for conversion...", reply_markup=progress_keyboard(task_type='download'))
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    DOWNLOAD_TASKS.setdefault(uid, []).append(cancel_event)
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
        tmp_in = get_unique_path(TMP, safe_name)
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
        batch_files = batch_list if batch_list else None
        CONVERT_SESSIONS[session_id] = {
            'uid': uid,
            'path': tmp_in,
            'original_name': tmp_in.name,
            'meta': meta,
            'configs': [],
            'upload_original': False,
            'current_config': {
                'res': None,
                'v_bitrate': meta['v_bitrate'],
                'a_bitrate': 128000 if not meta['audio_streams'] else meta['audio_streams'][0]['bitrate'],
            },
            'msg_id': status_msg.id,
            'source_message': m,
            'batch_index': 0,
            'batch_list': batch_files  
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
        if cancel_event in DOWNLOAD_TASKS.get(uid, []):
            DOWNLOAD_TASKS[uid].remove(cancel_event)

@app.on_callback_query(filters.regex(r"^cv_(res|vb_minus|vb_plus|ab_minus|ab_plus|orig|add|next|selectall)_"))
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
            session['current_config']['res'] = None
        else:
            session['current_config']['res'] = int(val)
    elif action == "vb_minus":
        session['current_config']['v_bitrate'] = max(100000, session['current_config']['v_bitrate'] - 100000)
    elif action == "vb_plus":
        session['current_config']['v_bitrate'] += 100000
    elif action == "ab_minus":
        session['current_config']['a_bitrate'] = max(32000, session['current_config']['a_bitrate'] - 32000)
    elif action == "ab_plus":
        session['current_config']['a_bitrate'] += 32000
    elif action == "orig":
        session['upload_original'] = not session['upload_original']
    elif action == "add":
        session['configs'].append(session['current_config'].copy())
        meta = session['meta']
        session['current_config'] = {
            'res': None,
            'v_bitrate': meta['v_bitrate'],
            'a_bitrate': 128000 if not meta['audio_streams'] else meta['audio_streams'][0]['bitrate'],
        }
        await cb.answer(f"Quality saved. Total configs: {len(session['configs'])}", show_alert=False)
    elif action == "next":
        session['configs'].append(session['current_config'].copy())
        batch_list = session.get('batch_list')
        if batch_list and session['batch_index'] + 1 < len(batch_list):
            session['batch_index'] += 1
            next_item = batch_list[session['batch_index']]
            next_path = Path(next_item['path'])
            if next_path.exists():
                session['path'] = next_path
                session['original_name'] = next_path.name
                session['meta'] = await asyncio.to_thread(get_detailed_metadata, next_path)
                session['configs'] = []
                session['upload_original'] = False
                session['current_config'] = {
                    'res': None,
                    'v_bitrate': session['meta']['v_bitrate'],
                    'a_bitrate': 128000 if not session['meta']['audio_streams'] else session['meta']['audio_streams'][0]['bitrate'],
                }
                text, markup = build_convert_ui(session_id)
                await cb.message.edit_text(text, reply_markup=markup, parse_mode=ParseMode.MARKDOWN)
                await cb.answer("Next video loaded.", show_alert=False)
                return
            else:
                await cb.answer("Next video file not found.", show_alert=True)
                return
        else:
            await cb.answer("All videos queued. Starting conversion...", show_alert=False)
            asyncio.create_task(execute_conversions(session_id, c))
            return
    elif action == "selectall":
        session['configs'].append(session['current_config'].copy())
        batch_list = session.get('batch_list')
        if batch_list:
            for idx, item in enumerate(batch_list):
                if idx != session['batch_index']:
                    item['configs'] = session['configs'].copy()
                    item['upload_original'] = session['upload_original']
            batch_list[session['batch_index']]['configs'] = session['configs'].copy()
            batch_list[session['batch_index']]['upload_original'] = session['upload_original']
        else:
            pass
        await cb.answer("Select All applied. Starting conversion...", show_alert=False)
        asyncio.create_task(execute_conversions(session_id, c, batch_apply=True))
        return
    text, markup = build_convert_ui(session_id)
    try: await cb.message.edit_text(text, reply_markup=markup, parse_mode=ParseMode.MARKDOWN)
    except: pass

async def execute_conversions(session_id, client, batch_apply=False):
    session = CONVERT_SESSIONS.pop(session_id, None)
    if not session: return
    uid = session['uid']
    msg = session['source_message']
    status_msg_id = session['msg_id']
    videos_to_convert = []
    if batch_apply and session.get('batch_list'):
        for item in session['batch_list']:
            f_path = Path(item['path'])
            if f_path.exists():
                configs = item.get('configs', [])
                if not configs:
                    configs = []
                videos_to_convert.append({
                    'path': f_path,
                    'name': f_path.name,
                    'meta': item.get('meta', await asyncio.to_thread(get_detailed_metadata, f_path)),
                    'configs': configs,
                    'upload_original': item.get('upload_original', False),
                    'order': len(videos_to_convert)  
                })
    else:
        f_path = session['path']
        if f_path.exists():
            configs = session['configs']
            videos_to_convert.append({
                'path': f_path,
                'name': session['original_name'],
                'meta': session['meta'],
                'configs': configs,
                'upload_original': session['upload_original'],
                'order': 0
            })
    if not videos_to_convert:
        try: await client.edit_message_text(msg.chat.id, status_msg_id, "No files to convert.")
        except: pass
        return
    if uid not in CONVERT_LOCKS:
        CONVERT_LOCKS[uid] = asyncio.Lock()
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    USER_TASK_EVENTS.setdefault(uid, {})[status_msg_id] = cancel_event
    
    # Use semaphore for concurrent conversions
    async with CONVERT_SEMAPHORE:
        try:
            total_videos = len(videos_to_convert)
            for v_idx, video in enumerate(videos_to_convert, 1):
                if cancel_event.is_set(): break
                in_path = video['path']
                original_name = video['name']
                meta = video['meta']
                configs = video['configs']
                upload_original = video.get('upload_original', False)
                order = video.get('order', v_idx - 1)
                if not configs:
                    continue
                async with CONVERT_LOCKS[uid]:
                    if cancel_event.is_set(): break
                    for idx, config in enumerate(configs, 1):
                        if cancel_event.is_set(): break
                        res_val = config['res']
                        vb = config['v_bitrate']
                        ab = config['a_bitrate']
                        orig_vb = meta['v_bitrate']
                        out_ext = in_path.suffix if in_path.suffix else ".mp4"
                        res_str = f"{res_val}p" if res_val else "OrigRes"
                        out_name = f"[Convert_{res_str}_{vb//1000}k] {original_name}"
                        out_path = TMP / f"cv_out_{uid}_{int(time.time())}_{v_idx}_{idx}{out_ext}"
                        try:
                            await client.edit_message_text(
                                msg.chat.id, status_msg_id,
                                f"⚙️ **Converting Video {v_idx}/{total_videos}**\nRes: `{res_str}` | Vid: `{vb//1000}k` | Aud: `{ab//1000}k`\nOriginal: `{original_name}`",
                                reply_markup=progress_keyboard(task_type='upload')
                            )
                        except: pass
                        cmd = ["ffmpeg", "-y", "-i", str(in_path), "-map", "0:v", "-map", "0:a?", "-map", "0:s?"]
                        if res_val:
                            cmd.extend(["-vf", f"scale=w=-2:h={res_val}"])
                        if vb > orig_vb and orig_vb > 0:
                            cmd.extend(["-c:v", "h264_nvenc", "-pix_fmt", "yuv420p", "-profile:v", "high", "-preset", "p4",
                                        "-b:v", str(vb), "-minrate", str(vb), "-maxrate", str(vb), "-bufsize", str(vb*2)])
                        else:
                            cmd.extend(["-c:v", "h264_nvenc", "-pix_fmt", "yuv420p", "-profile:v", "high", "-preset", "p4", "-b:v", str(vb)])
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
                                        action_txt = f"Converting {v_idx}/{total_videos} [{res_str}]"
                                        await progress_callback(out_time_sec, meta['duration'], action_txt, dummy_status, start_t, is_time_based=True, original_name=out_name)
                                except: pass
                        await process.wait()
                        if cancel_event.is_set(): raise Exception("Cancelled by user")
                        if out_path.exists() and out_path.stat().st_size > 0:
                            # Add to ordered convert output queue
                            output_data = {
                                'message': msg,
                                'file_path': out_path,
                                'file_name': out_name,
                                'send_func': send_converted_file
                            }
                            await add_to_convert_output_queue(uid, output_data)
                        else:
                            logger.error("FFmpeg convert output failed.")
                    if upload_original and not cancel_event.is_set():
                        out_name = get_dynamic_filename(uid, original_name)
                        output_data = {
                            'message': msg,
                            'file_path': in_path,
                            'file_name': out_name,
                            'send_func': send_converted_file
                        }
                        await add_to_convert_output_queue(uid, output_data)
                    else:
                        in_path.unlink(missing_ok=True)
        except Exception as e:
            logger.error(f"Execution conversions error: {e}")
            try: await client.edit_message_text(msg.chat.id, status_msg_id, f"Conversion Error: {e}")
            except: pass
        finally:
            try:
                if cancel_event in TASKS.get(uid, []): TASKS[uid].remove(cancel_event)
                if cancel_event in UPLOAD_TASKS.get(uid, []): UPLOAD_TASKS[uid].remove(cancel_event)
                await client.delete_messages(msg.chat.id, status_msg_id)
            except: pass

async def send_converted_file(message, file_path, file_name):
    """Send a converted file to the user."""
    uid = message.from_user.id
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    try:
        await sequential_upload_task(uid, client, message, file_path, file_name, None, cancel_event, default_caption=file_name, original_caption=file_name, original_download_name=file_name)
    except Exception as e:
        logger.error(f"Error sending converted file: {e}")

@app.on_message(filters.text & filters.private)
async def text_handler(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    text = m.text.strip()
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
                session['current_config']['v_bitrate'] = kbps * 1000
                try:
                    t_ui, markup = build_convert_ui(session_id)
                    await c.edit_message_text(m.chat.id, session['msg_id'], t_ui, reply_markup=markup, parse_mode=ParseMode.MARKDOWN)
                except: pass
            try: await m.delete()
            except: pass
            return
    text_lower = text.lower()
    if text_lower == "list":
        if uid in BATCH_AUDIO_MODE:
            state = BATCH_AUDIO_STATE.get(uid)
            if state in ['list1', 'list2']:
                await send_batch_audio_list_page(c, m.chat.id, uid, state, 0)
            else:
                await m.reply_text("List viewing is only available while adding links/videos to lists.")
            return
        elif uid in CONVERT_MODE:
            await send_batch_audio_list_page(c, m.chat.id, uid, 'convert', 0)
            return
    if text_lower in ["path", "p"]:
        NAV_PATHS[uid] = {"current": TMP, "items": [], "page": 0}
        await send_path_ui(c, m.chat.id, uid, page=0)
        return
    if uid in CONVERT_MODE:
        if text_lower == "off":
            CONVERT_MODE.discard(uid)
            CONVERT_ZIP_MODE.discard(uid)
            ACTIVE_CONVERT_SESSION.pop(uid, None)
            for item in CONVERT_BATCH_LIST.get(uid, []):
                try: Path(item['path']).unlink(missing_ok=True)
                except: pass
            CONVERT_BATCH_LIST.pop(uid, None)
            await m.reply_text("Convert Mode **OFF**.")
            return
        elif text_lower == "next":
            if not CONVERT_BATCH_LIST.get(uid):
                await m.reply_text("Convert List is empty. Please send videos/zips first.")
                return
            batch_list = [{'path': item['path'], 'name': item['name']} for item in CONVERT_BATCH_LIST[uid]]
            first_item = CONVERT_BATCH_LIST[uid][0]
            await handle_convert_input(c, m, override_path=first_item['path'], batch_list=batch_list)
            return
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
        try:
            await m.delete()
        except:
            pass
        if text_lower == 'close':
            if uid in NAV_PATHS:
                try:
                    await c.delete_messages(m.chat.id, NAV_PATHS[uid]['msg_id'])
                except:
                    pass
                NAV_PATHS.pop(uid, None)
            await m.reply_text("File Manager closed.")
            return
        if text_lower == 'np':
            page = NAV_PATHS[uid].get('page', 0) + 1
            await send_path_ui(c, m.chat.id, uid, msg_id=NAV_PATHS[uid].get('msg_id'), page=page)
            return
        if text_lower == 'pp':
            page = max(0, NAV_PATHS[uid].get('page', 0) - 1)
            await send_path_ui(c, m.chat.id, uid, msg_id=NAV_PATHS[uid].get('msg_id'), page=page)
            return
        if text_lower == 'b':
            current = NAV_PATHS[uid]['current']
            if current != TMP:
                NAV_PATHS[uid]['current'] = current.parent
            await send_path_ui(c, m.chat.id, uid, msg_id=NAV_PATHS[uid].get('msg_id'), page=0)
            return
        is_delete = text_lower.startswith('d ')
        is_link = text_lower.startswith('l ')
        is_rename = text_lower.startswith('r ')
        is_extract = text_lower.startswith('e ')
        force_ext = None
        target_str = text_lower
        if is_rename:
            parts = text_lower.split()
            if len(parts) >= 3 and not parts[1].replace('-', '').replace(',', '').isdigit() and parts[1] != 'all':
                force_ext = parts[1]
                if not force_ext.startswith('.'):
                    force_ext = '.' + force_ext
                target_str = " ".join(parts[2:])
            else:
                target_str = text_lower.split(' ', 1)[1] if len(text_lower.split(' ', 1)) > 1 else ""
        elif is_delete or is_link or is_extract:
            target_str = text_lower.split(' ', 1)[1] if len(text_lower.split(' ', 1)) > 1 else ""
        items = NAV_PATHS[uid].get('items', [])
        selected_indices = []
        if target_str == 'all':
            selected_indices = list(range(1, len(items) + 1))
        else:
            try:
                parts = target_str.split(',')
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
            if len(selected_indices) == 1 and 1 <= selected_indices[0] <= len(items) and not (is_delete or is_link or is_rename or is_extract):
                idx = selected_indices[0] - 1
                selected_item = items[idx]
                if selected_item.is_dir():
                    NAV_PATHS[uid]['current'] = selected_item
                    await send_path_ui(c, m.chat.id, uid, msg_id=NAV_PATHS[uid].get('msg_id'), page=0)
                    return
            files_to_process = []
            for i in selected_indices:
                if 1 <= i <= len(items):
                    files_to_process.append(items[i-1])
            if files_to_process:
                if is_delete:
                    for f in files_to_process:
                        try:
                            if f.is_dir(): shutil.rmtree(f, ignore_errors=True)
                            else: f.unlink(missing_ok=True)
                        except: pass
                    await m.reply_text(f"Deleted {len(files_to_process)} items.")
                    await send_path_ui(c, m.chat.id, uid, msg_id=NAV_PATHS[uid].get('msg_id'), page=NAV_PATHS[uid].get('page', 0))
                elif is_link:
                    link_text = "**Direct Download Links:**\n"
                    for f in files_to_process:
                        if f.is_file():
                            safe_path = urllib.parse.quote(f.relative_to(TMP).as_posix())
                            link = f"{PUBLIC_BASE_URL}/dl/{safe_path}"
                            link_text += f"‣ `{f.name}`\n🔗 {link}\n"
                    await m.reply_text(link_text, disable_web_page_preview=True)
                elif is_rename:
                    renamed_count = 0
                    for f in files_to_process:
                        if f.is_file():
                            new_name = get_dynamic_filename(uid, f.name)
                            if force_ext:
                                new_name = Path(new_name).stem + force_ext
                            new_path = get_unique_path(f.parent, new_name)
                            try:
                                f.rename(new_path)
                                renamed_count += 1
                            except: pass
                    await m.reply_text(f"Renamed {renamed_count} files based on saved format.")
                    await send_path_ui(c, m.chat.id, uid, msg_id=NAV_PATHS[uid].get('msg_id'), page=NAV_PATHS[uid].get('page', 0))
                elif is_extract:
                    for f in files_to_process:
                        if is_archive_file(f):
                            if uid not in ZIP_DL_QUEUES: ZIP_DL_QUEUES[uid] = asyncio.Queue()
                            queue_msg = await m.reply_text(f"Queued manual extract: `{f.name}`")
                            await ZIP_DL_QUEUES[uid].put({'local_path': str(f), 'message': m, 'queue_msg': queue_msg, 'is_dl_only': True})
                    if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
                        ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
                else:
                    mode = PATH_MODE_SELECTION.get(uid)
                    if mode:
                        if mode == 'convert':
                            if uid not in PATH_CONVERT_LIST:
                                PATH_CONVERT_LIST[uid] = []
                            for f in files_to_process:
                                if f.is_file():
                                    PATH_CONVERT_LIST[uid].append(f)
                            await m.reply_text(f"Added {len([f for f in files_to_process if f.is_file()])} files to Convert list.")
                        elif mode == 'batch_audio':
                            stage = PATH_BATCH_AUDIO_STAGE.get(uid, 1)
                            if stage == 1:
                                if uid not in PATH_BATCH_AUDIO_LIST1:
                                    PATH_BATCH_AUDIO_LIST1[uid] = []
                                for f in files_to_process:
                                    if f.is_file():
                                        PATH_BATCH_AUDIO_LIST1[uid].append(f)
                                await m.reply_text(f"Added {len([f for f in files_to_process if f.is_file()])} files to List 1.")
                            else:
                                if uid not in PATH_BATCH_AUDIO_LIST2:
                                    PATH_BATCH_AUDIO_LIST2[uid] = []
                                for f in files_to_process:
                                    if f.is_file():
                                        PATH_BATCH_AUDIO_LIST2[uid].append(f)
                                await m.reply_text(f"Added {len([f for f in files_to_process if f.is_file()])} files to List 2.")
                        elif mode == 'zip':
                            if uid not in PATH_ZIP_LISTS or not PATH_ZIP_LISTS[uid]:
                                PATH_ZIP_LISTS[uid] = [[]]
                                PATH_ZIP_CURRENT_LIST[uid] = 0
                            current_list_idx = PATH_ZIP_CURRENT_LIST[uid]
                            for f in files_to_process:
                                if f.is_file():
                                    PATH_ZIP_LISTS[uid][current_list_idx].append(f)
                            await m.reply_text(f"Added {len([f for f in files_to_process if f.is_file()])} files to current ZIP list.")
                        await send_path_ui(c, m.chat.id, uid, msg_id=NAV_PATHS[uid].get('msg_id'), page=NAV_PATHS[uid]['page'])
                    else:
                        file_uploads = [f for f in files_to_process if f.is_file()]
                        await m.reply_text(f"Starting upload for {len(file_uploads)} selected files from path...")
                        asyncio.create_task(process_path_uploads(uid, c, m, file_uploads))
                        if uid in NAV_PATHS and 'msg_id' in NAV_PATHS[uid]:
                            try:
                                await c.delete_messages(m.chat.id, NAV_PATHS[uid]['msg_id'])
                            except:
                                pass
                            NAV_PATHS.pop(uid, None)
                return
    if uid in DOWNLOAD_ONLY_MODE:
        if text_lower == "link":
            DOWNLOAD_LINK_MODE.add(uid)
            DOWNLOAD_T_MODE.discard(uid)
            await m.reply_text("Download Link Mode **ON**. Direct download links will be provided after downloading.")
            return
        elif text_lower == "t":
            DOWNLOAD_T_MODE.add(uid)
            DOWNLOAD_LINK_MODE.discard(uid)
            await m.reply_text("Telegram Stream Link Mode **ON**. Direct download and stream links will be provided without downloading to local storage.")
            return
        elif text_lower == "off":
            DOWNLOAD_ONLY_MODE.discard(uid)
            DOWNLOAD_LINK_MODE.discard(uid)
            DOWNLOAD_T_MODE.discard(uid)
            await m.reply_text("Download Only Mode **OFF**.")
            return
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
        if uid in DOWNLOAD_T_MODE:
            dl_link = f"{PUBLIC_BASE_URL}/dl_stream?url={urllib.parse.quote(url)}"
            st_link = f"{PUBLIC_BASE_URL}/stream?url={urllib.parse.quote(url)}"
            await m.reply_text(f"🔗 **Download Link (Direct):**\n{dl_link}\n\n▶️ **Stream Link (Watch):**\n{st_link}", disable_web_page_preview=True)
            return
        if uid in DOWNLOAD_ONLY_MODE:
            if uid not in ZIP_DL_QUEUES:
                ZIP_DL_QUEUES[uid] = asyncio.Queue()
            queue_msg = await m.reply_text(f"Added to DL Only Queue. Pos: {ZIP_DL_QUEUES[uid].qsize() + 1}")
            await ZIP_DL_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg, 'is_dl_only': True})
            if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
                ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
            return
        if uid in CONVERT_MODE:
            if uid not in BATCH_AUDIO_QUEUES:
                BATCH_AUDIO_QUEUES[uid] = asyncio.Queue()
            original_name = await get_filename_from_url(url)
            queue_msg = await m.reply_text(f"Queue item added for `{original_name}` (Convert Batch). Position: {BATCH_AUDIO_QUEUES[uid].qsize() + 1}")
            await BATCH_AUDIO_QUEUES[uid].put({'url': url, 'message': m, 'target_list': CONVERT_BATCH_LIST[uid], 'queue_msg': queue_msg})
            if uid not in BATCH_AUDIO_WORKERS or BATCH_AUDIO_WORKERS[uid].done():
                BATCH_AUDIO_WORKERS[uid] = asyncio.create_task(batch_audio_worker(uid, c))
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
            await add_to_queue(uid, c, m, original_name, is_url=True, url=url, task_type='download')

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
    if target_list is CONVERT_BATCH_LIST.get(uid): list_num = "Convert Batch List"
    else: list_num = "1" if target_list is BATCH_AUDIO_LIST1.get(uid) else "2"
    if url or file_info:
        status_msg = None
        try:
            original_name = "video.mp4"
            if url: original_name = await get_filename_from_url(url)
            elif file_info: original_name = file_info.file_name or "video.mp4"
            status_msg = await m.reply_text(f"Downloading `{original_name}` to build list...", reply_markup=progress_keyboard(task_type='download'))
            safe_name = re.sub(r"[\\/*?\"<>|:]", "_", original_name)
            tmp_in = get_unique_path(TMP, safe_name)
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
                if not tmp_in.suffix:
                    EXTENSION_WAIT[uid] = {
                        'file_path': tmp_in,
                        'message': m,
                        'callback': process_batch_audio_input,
                        'args': (uid, c, m, None, None, target_list),
                        'kwargs': {}
                    }
                    keyboard = InlineKeyboardMarkup([
                        [InlineKeyboardButton(".zip", callback_data=f"extsel_local_{uid}_.zip"),
                         InlineKeyboardButton(".mkv", callback_data=f"extsel_local_{uid}_.mkv")],
                        [InlineKeyboardButton(".mp4", callback_data=f"extsel_local_{uid}_.mp4"),
                         InlineKeyboardButton(".rar", callback_data=f"extsel_local_{uid}_.rar")]
                    ])
                    await c.send_message(m.chat.id, f"File `{tmp_in.name}` has no extension. Please select a format:", reply_markup=keyboard)
                    return
                if is_archive_file(tmp_in):
                    await status_msg.delete()
                    await execute_zip_download_and_extract(c, m, url=None, local_path=str(tmp_in), target_list=target_list)
                    tmp_in.unlink(missing_ok=True)
                else:
                    target_list.append({'path': str(tmp_in), 'name': tmp_in.name})
                    await status_msg.edit(f"URL/File added to {list_num}. Total: {len(target_list)}")
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
    if uid in DOWNLOAD_T_MODE:
        dl_link = f"{PUBLIC_BASE_URL}/dl_stream?url={urllib.parse.quote(url)}"
        st_link = f"{PUBLIC_BASE_URL}/stream?url={urllib.parse.quote(url)}"
        await m.reply_text(f"🔗 **Download Link (Direct):**\n{dl_link}\n\n▶️ **Stream Link (Watch):**\n{st_link}", disable_web_page_preview=True)
        return
    if uid in DOWNLOAD_ONLY_MODE:
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Added to DL Only Queue. Pos: {ZIP_DL_QUEUES[uid].qsize() + 1}")
        await ZIP_DL_QUEUES[uid].put({'url': url, 'message': m, 'queue_msg': queue_msg, 'is_dl_only': True})
        if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
            ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
        return
    if uid in CONVERT_MODE:
        if uid not in BATCH_AUDIO_QUEUES:
            BATCH_AUDIO_QUEUES[uid] = asyncio.Queue()
        original_name = await get_filename_from_url(url)
        queue_msg = await m.reply_text(f"Queue item added for `{original_name}` (Convert Batch). Position: {BATCH_AUDIO_QUEUES[uid].qsize() + 1}")
        await BATCH_AUDIO_QUEUES[uid].put({'url': url, 'message': m, 'target_list': CONVERT_BATCH_LIST[uid], 'queue_msg': queue_msg})
        if uid not in BATCH_AUDIO_WORKERS or BATCH_AUDIO_WORKERS[uid].done():
            BATCH_AUDIO_WORKERS[uid] = asyncio.create_task(batch_audio_worker(uid, c))
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
        await add_to_queue(uid, c, m, original_name, is_url=True, url=url, task_type='download')

async def download_and_process_generic(c, m, url, status_msg, cancel_event_passed=None):
    uid = m.from_user.id
    cancel_event = cancel_event_passed or asyncio.Event()
    if not cancel_event_passed:
        TASKS.setdefault(uid, []).append(cancel_event)
        DOWNLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    if status_msg:
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    try:
        fname = await get_filename_from_url(url)
        safe_name = re.sub(r"[\\/*?\"<>|:]", "_", fname)
        if len(safe_name) > 100:
            ext = Path(safe_name).suffix
            safe_name = safe_name[:100 - len(ext)] + ext
        tmp_in = get_unique_path(TMP, safe_name)
        ok, err = False, None
        if is_drive_url(url):
            fid = extract_drive_id(url)
            if not fid:
                await status_msg.edit("Google Drive ID not found.")
                if cancel_event in TASKS.get(uid, []): TASKS[uid].remove(cancel_event)
                if cancel_event in DOWNLOAD_TASKS.get(uid, []): DOWNLOAD_TASKS[uid].remove(cancel_event)
                return
            ok, err = await download_drive_file(fid, tmp_in, status_msg, cancel_event=cancel_event, original_name=fname)
        else:
            ok, err = await download_url_generic(url, tmp_in, status_msg, cancel_event=cancel_event, original_name=fname)
        if not ok:
            raise Exception(f"Download Failed: {err}")
        await status_msg.edit("Download complete. Uploading...", reply_markup=None)
        renamed_file = get_dynamic_filename(uid, tmp_in.name)
        if uid in MKV_AUDIO_CHANGE_MODE:
            try:
                await status_msg.edit("Checking file for audio track analysis...", reply_markup=progress_keyboard(task_type='download'))
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
                await status_msg.edit(track_list_text, reply_markup=progress_keyboard(task_type='upload'))
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
    UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    try:
        status_msg = await m.reply_text("Editing caption...", reply_markup=progress_keyboard(task_type='upload'))
    except Exception:
        status_msg = await m.reply_text("Editing caption...", reply_markup=progress_keyboard(task_type='upload'))
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
            UPLOAD_TASKS[uid].remove(cancel_event)
        except Exception:
            pass

@app.on_message(filters.private & (filters.video | filters.document))
async def forwarded_file_or_direct_file(c: Client, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    file_info = m.video or m.document
    original_name = file_info.file_name if file_info and file_info.file_name else f"file_{file_info.file_unique_id}"
    if uid in DOWNLOAD_T_MODE:
        dl_link = f"{PUBLIC_BASE_URL}/dl_stream?file_id={file_info.file_id}&filename={urllib.parse.quote(original_name)}"
        st_link = f"{PUBLIC_BASE_URL}/stream?file_id={file_info.file_id}&filename={urllib.parse.quote(original_name)}"
        await m.reply_text(f"🔗 **Download Link (Direct):**\n{dl_link}\n\n▶️ **Stream Link (Watch):**\n{st_link}", disable_web_page_preview=True)
        return
    if uid in DOWNLOAD_ONLY_MODE:
        if uid not in ZIP_DL_QUEUES:
            ZIP_DL_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Added to DL Only Queue. Pos: {ZIP_DL_QUEUES[uid].qsize() + 1}")
        await ZIP_DL_QUEUES[uid].put({'message': m, 'queue_msg': queue_msg, 'is_telegram_file': True, 'is_dl_only': True})
        if uid not in ZIP_DL_WORKERS or ZIP_DL_WORKERS[uid].done():
            ZIP_DL_WORKERS[uid] = asyncio.create_task(zip_download_worker(uid, c))
        return
    if uid in CONVERT_MODE:
        if uid not in BATCH_AUDIO_QUEUES:
            BATCH_AUDIO_QUEUES[uid] = asyncio.Queue()
        queue_msg = await m.reply_text(f"Queue item added for `{original_name}` (Convert Batch). Position: {BATCH_AUDIO_QUEUES[uid].qsize() + 1}")
        await BATCH_AUDIO_QUEUES[uid].put({'file_info': file_info, 'message': m, 'target_list': CONVERT_BATCH_LIST[uid], 'queue_msg': queue_msg})
        if uid not in BATCH_AUDIO_WORKERS or BATCH_AUDIO_WORKERS[uid].done():
            BATCH_AUDIO_WORKERS[uid] = asyncio.create_task(batch_audio_worker(uid, c))
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
    await add_to_queue(uid, c, m, original_name, is_url=False, original_caption=m.caption, task_type='download')

async def show_batch_audio_ui(c, chat_id, uid):
    pair_idx = BATCH_AUDIO_CURRENT_PAIR_IDX[uid]
    pairs = BATCH_AUDIO_MAPPING[uid]
    if pair_idx >= len(pairs):
        await c.send_message(chat_id, "All track selections complete! Starting batch processing...")
        asyncio.create_task(execute_batch_audio_remux(uid, c, chat_id))
        return
    idx1, idx2 = pairs[pair_idx]
    vid_path1 = BATCH_AUDIO_LIST1[uid][idx1]['path']
    vid_path2 = BATCH_AUDIO_LIST2[uid][idx2]['path']
    name1 = BATCH_AUDIO_LIST1[uid][idx1]['name']
    name2 = BATCH_AUDIO_LIST2[uid][idx2]['name']
    msg = None
    if str(pair_idx) not in BATCH_AUDIO_TRACK_CONFIGS[uid]:
        try:
            if uid in BATCH_AUDIO_UI_MSG:
                try:
                    msg = await c.edit_message_text(chat_id, BATCH_AUDIO_UI_MSG[uid], "Analyzing tracks...")
                except Exception as e:
                    if "MESSAGE_NOT_MODIFIED" in str(e):
                        pass
                    else:
                        msg = await c.send_message(chat_id, "Analyzing tracks...")
                        BATCH_AUDIO_UI_MSG[uid] = msg.id
            else:
                msg = await c.send_message(chat_id, "Analyzing tracks...")
                BATCH_AUDIO_UI_MSG[uid] = msg.id
            tracks1 = await asyncio.to_thread(get_audio_tracks_ffprobe, vid_path1)
            tracks2 = await asyncio.to_thread(get_audio_tracks_ffprobe, vid_path2)
            if not tracks2:
                seen = set()
                unique_tracks = []
                for t in tracks1:
                    key = (t.get('language', 'und'), t.get('title', 'N/A'))
                    if key not in seen:
                        seen.add(key)
                        unique_tracks.append(t)
                tracks1 = unique_tracks
            combined_tracks = [{'src': 1, 'data': t} for t in tracks1] + [{'src': 2, 'data': t} for t in tracks2]
            BATCH_AUDIO_TRACK_CONFIGS[uid][str(pair_idx)] = {
                'keep': [],
                'default': -1,
                'tracks': combined_tracks
            }
        except Exception as e:
            logger.error(f"Batch Audio Analysis Error: {e}")
            await c.send_message(chat_id, f"Error: {e}")
            return
    config = BATCH_AUDIO_TRACK_CONFIGS[uid][str(pair_idx)]
    combined_tracks = config['tracks']
    text = (
        f"**🎵 Batch Audio Selection ({pair_idx + 1}/{len(pairs)})**\n\n"
        f"**Base Video:** `{name1}`\n"
        f"**Audio Source:** `{name2}`\n\n"
    )
    tracks1_display = [t for t in combined_tracks if t['src'] == 1]
    tracks2_display = [t for t in combined_tracks if t['src'] == 2]
    if tracks1_display:
        text += "**List 1 Audios:**\n"
        for t in tracks1_display:
            t_data = t['data']
            title_str = t_data['title'] if t_data['title'] and t_data['title'] != 'N/A' else 'Unknown'
            text += f"‣ Audio track - {title_str} ({t_data['language']})\n"
    if tracks2_display:
        text += "\n**List 2 Audios:**\n"
        for t in tracks2_display:
            t_data = t['data']
            title_str = t_data['title'] if t_data['title'] and t_data['title'] != 'N/A' else 'Unknown'
            text += f"‣ Audio track - {title_str} ({t_data['language']})\n"
    text += "\nSelect which tracks to keep and which should play by default:"
    keyboard = []
    for i, track_wrap in enumerate(combined_tracks):
        is_def = config['default'] == i
        is_keep = i in config['keep']
        def_text = "🔘 Default" if is_def else "📻 Set Def"
        keep_text = "✅ Keep" if is_keep else "❌ Drop"
        t_data = track_wrap['data']
        lang_code = t_data.get('language', 'und').lower()
        short_name = f"({lang_code})"
        keyboard.append([
            InlineKeyboardButton(def_text, callback_data=f"baud_def_{uid}_{pair_idx}_{i}"),
            InlineKeyboardButton(short_name, callback_data="ignore"),
            InlineKeyboardButton(keep_text, callback_data=f"baud_keep_{uid}_{pair_idx}_{i}")
        ])
    keyboard.append([
        InlineKeyboardButton("Cancel ❌", callback_data="baud_cancel"),
        InlineKeyboardButton("Select All 🚀", callback_data=f"baud_all_{uid}_{pair_idx}"),
        InlineKeyboardButton("Next / Done ✅", callback_data=f"baud_done_{uid}_{pair_idx}")
    ])
    try:
        await c.edit_message_text(chat_id, BATCH_AUDIO_UI_MSG[uid], text, reply_markup=InlineKeyboardMarkup(keyboard))
    except Exception as e:
        if "MESSAGE_NOT_MODIFIED" not in str(e):
            logger.error(f"UI edit error: {e}")

@app.on_callback_query(filters.regex(r"^baud_"))
async def batch_audio_callback(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    parts = cb.data.split('_')
    action = parts[1]
    if action == "use":
        if parts[2] == "list1":
            BATCH_AUDIO_LIST2[uid] = BATCH_AUDIO_LIST1[uid].copy()
            BATCH_AUDIO_STATE[uid] = 'mapping'
            keyboard = InlineKeyboardMarkup([
                [InlineKeyboardButton("Upload All 🚀", callback_data="baud_list_ok")],
                [InlineKeyboardButton("Cancel ❌", callback_data="baud_list_cancel")]
            ])
            await cb.message.edit_text(
                "**List 1 is now set as Audio Source (Internal Audio Change).**\n\n"
                "**Mapping Rules:**\n"
                "‣ Default matches 1 to 1, 2 to 2.\n"
                "‣ Custom mapping: send `1-13=1-13, 14=16, 15=14`\n"
                "‣ Click Upload All or send custom string.",
                reply_markup=keyboard
            )
        return
    if action == "list":
        sub_action = parts[2]
        if sub_action == "close":
            try: await cb.message.delete()
            except: pass
            return
        elif sub_action == "del":
            list_id = parts[3]
            index = int(parts[4])
            page = int(parts[5])
            if list_id == 'convert': target_list = CONVERT_BATCH_LIST.get(uid, [])
            else: target_list = BATCH_AUDIO_LIST1.get(uid, []) if list_id == 'list1' else BATCH_AUDIO_LIST2.get(uid, [])
            if 0 <= index < len(target_list):
                file_info = target_list.pop(index)
                try: Path(file_info['path']).unlink(missing_ok=True)
                except Exception: pass
                await cb.answer("Deleted from list.", show_alert=False)
            await send_batch_audio_list_page(c, cb.message.chat.id, uid, list_id, page, cb.message.id)
        elif sub_action == "page":
            list_id = parts[3]
            page = int(parts[4])
            await send_batch_audio_list_page(c, cb.message.chat.id, uid, list_id, page, cb.message.id)
        elif sub_action == "ok":
            count = min(len(BATCH_AUDIO_LIST1[uid]), len(BATCH_AUDIO_LIST2[uid]))
            pairs = [(i, i) for i in range(count)]
            if not pairs:
                await cb.answer("Lists are empty!", show_alert=True)
                return
            BATCH_AUDIO_MAPPING[uid] = pairs
            BATCH_AUDIO_STATE[uid] = 'ui'
            BATCH_AUDIO_CURRENT_PAIR_IDX[uid] = 0
            BATCH_AUDIO_TRACK_CONFIGS[uid] = {}
            BATCH_AUDIO_UI_MSG[uid] = cb.message.id
            await show_batch_audio_ui(c, cb.message.chat.id, uid)
        elif sub_action == "cancel":
            if len(parts) == 3: 
                keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton("Yes ✅", callback_data="baud_list_cancel_yes"),
                     InlineKeyboardButton("No ❌", callback_data="baud_list_cancel_no")]
                ])
                try:
                    await cb.message.edit_text("Are you sure you want to cancel and clear the list?", reply_markup=keyboard)
                except Exception: pass
            elif parts[3] == "yes": 
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
                try:
                    await cb.message.edit_text("Batch Audio Add Mode cancelled and data cleared.")
                except Exception: pass
            elif parts[3] == "no": 
                def chunk_and_send_return(lst, title):
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
                list1_chunks = chunk_and_send_return(BATCH_AUDIO_LIST1[uid], "List 1 (Base Videos)")
                list2_chunks = chunk_and_send_return(BATCH_AUDIO_LIST2[uid], "List 2 (Audio Sources)")
                for c_msg in list1_chunks: await cb.message.reply_text(c_msg)
                for c_msg in list2_chunks: await cb.message.reply_text(c_msg)
                keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton("Upload All 🚀", callback_data="baud_list_ok")],
                    [InlineKeyboardButton("Cancel ❌", callback_data="baud_list_cancel")]
                ])
                try:
                    await cb.message.reply_text(
                        "**Mapping Rules:**\n"
                        "‣ Default matches 1 to 1, 2 to 2.\n"
                        "‣ Custom mapping: send `1-13=1-13, 14=16, 15=14`\n"
                        "‣ Click Upload All or send custom string.",
                        reply_markup=keyboard
                    )
                except Exception: pass
        return
    if action == "cancel":
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
        try:
            await cb.message.edit_text("Batch Audio Add Mode cancelled.")
        except Exception: pass
        return
    if str(uid) != parts[2]:
        await cb.answer("Not your session.", show_alert=True)
        return
    pair_idx = int(parts[3])
    config = BATCH_AUDIO_TRACK_CONFIGS[uid][str(pair_idx)]
    if action == "def":
        track_idx = int(parts[4])
        config['default'] = track_idx
        if track_idx not in config['keep']:
            config['keep'].append(track_idx)
        await show_batch_audio_ui(c, cb.message.chat.id, uid)
        await cb.answer()
    elif action == "keep":
        track_idx = int(parts[4])
        if track_idx in config['keep']:
            config['keep'].remove(track_idx)
            if config['default'] == track_idx:
                config['default'] = -1
        else:
            config['keep'].append(track_idx)
        await show_batch_audio_ui(c, cb.message.chat.id, uid)
        await cb.answer()
    elif action == "done":
        BATCH_AUDIO_CURRENT_PAIR_IDX[uid] += 1
        await show_batch_audio_ui(c, cb.message.chat.id, uid)
        await cb.answer()
    elif action == "all":
            pairs = BATCH_AUDIO_MAPPING[uid]
            keep_idxs = config['keep']
            def_idx = config['default']
            target_count = len(config['tracks'])
            await cb.answer("Applying pattern to remaining files...", show_alert=False)
            for i in range(pair_idx + 1, len(pairs)):
                idx1, idx2 = pairs[i]
                vid1 = BATCH_AUDIO_LIST1[uid][idx1]['path']
                vid2 = BATCH_AUDIO_LIST2[uid][idx2]['path']
                t1 = await asyncio.to_thread(get_audio_tracks_ffprobe, vid1)
                t2 = await asyncio.to_thread(get_audio_tracks_ffprobe, vid2)
                if not t2:
                    seen = set()
                    unique_tracks = []
                    for t in t1:
                        key = (t.get('language', 'und'), t.get('title', 'N/A'))
                        if key not in seen:
                            seen.add(key)
                            unique_tracks.append(t)
                    t1 = unique_tracks
                c_tracks = [{'src': 1, 'data': t} for t in t1] + [{'src': 2, 'data': t} for t in t2]
                if len(c_tracks) != target_count:
                    BATCH_AUDIO_CURRENT_PAIR_IDX[uid] = i
                    await cb.message.reply_text(f"Track mismatch at pair {i+1}. Found {len(c_tracks)} tracks instead of {target_count}. Manual selection required.")
                    await show_batch_audio_ui(c, cb.message.chat.id, uid)
                    return
                BATCH_AUDIO_TRACK_CONFIGS[uid][str(i)] = {
                    'keep': keep_idxs.copy(),
                    'default': def_idx,
                    'tracks': c_tracks
                }
            BATCH_AUDIO_CURRENT_PAIR_IDX[uid] = len(pairs)
            await show_batch_audio_ui(c, cb.message.chat.id, uid)

async def execute_batch_audio_remux(uid, c, chat_id):
    pairs = BATCH_AUDIO_MAPPING.get(uid, [])
    if not pairs: return
    status_msg = await c.send_message(chat_id, f"Starting remux for {len(pairs)} files...")
    for i, (idx1, idx2) in enumerate(pairs):
        vid1 = BATCH_AUDIO_LIST1[uid][idx1]['path']
        vid2 = BATCH_AUDIO_LIST2[uid][idx2]['path']
        base_name = BATCH_AUDIO_LIST1[uid][idx1]['name']
        config = BATCH_AUDIO_TRACK_CONFIGS[uid][str(i)]
        keep_tracks = config['keep']
        def_track = config['default']
        tracks_data = config['tracks']
        out_name = get_dynamic_filename(uid, base_name)
        if not out_name.lower().endswith(".mkv"):
            out_name = Path(out_name).stem + ".mkv"
        out_path = TMP / f"ba_out_{uid}_{i}_{int(time.time())}.mkv"
        try:
            await status_msg.edit(f"Remuxing {i+1}/{len(pairs)}...\nBase: `{base_name}`")
        except Exception: pass
        map_args = ["-map", "0:v", "-map", "0:s?", "-map", "0:d?"]
        ordered_audio_keep = []
        if def_track != -1 and def_track in keep_tracks:
            ordered_audio_keep.append(def_track)
        for k in keep_tracks:
            if k != def_track:
                ordered_audio_keep.append(k)
        for k in ordered_audio_keep:
            track_wrap = tracks_data[k]
            stream_idx = track_wrap['data']['stream_index']
            src_file_idx = 0 if track_wrap['src'] == 1 else 1
            map_args.extend(["-map", f"{src_file_idx}:{stream_idx}"])
        cmd = [
            "ffmpeg", "-y",
            "-i", str(vid1),
            "-i", str(vid2),
            *map_args,
            "-disposition:a", "0"
        ]
        if def_track != -1 and def_track in keep_tracks:
            cmd.extend(["-disposition:a:0", "default"])
        used_titles = set()
        for idx, k in enumerate(ordered_audio_keep):
            t = tracks_data[k]['data']['title']
            if not t or t == 'N/A': t = "Audio"
            original_t = t
            if t in used_titles:
                j = 2
                while f"{original_t}{j}" in used_titles: j += 1
                t = f"{original_t}{j}"
            used_titles.add(t)
            cmd.extend([f"-metadata:s:a:{idx}", f"title={t}"])
            cmd.extend([f"-metadata:s:a:{idx}", "handler_name=[@TA_HD_Anime] Telegram Channel"])
        cmd.extend([
            "-metadata", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:v", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:v", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:a", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:a", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:s", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:s", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-c:v", "copy",
            "-c:a", "aac", "-ac", "2", "-b:a", "128k", 
            "-c:s", "copy",
            "-shortest", 
            str(out_path)
        ])
        try:
            res = await asyncio.to_thread(subprocess.run, cmd, capture_output=True, text=True)
            if res.returncode == 0 and out_path.exists():
                final_caption_template = USER_CAPTIONS.get(uid)
                if not final_caption_template or uid in USE_ORIGINAL_CAPTION_IN_MULTI_GROUP:
                    cap = base_name
                else:
                    cap = process_dynamic_caption(uid, final_caption_template)
                class FakeMessage:
                    def __init__(self, cid):
                        class Chat: id = cid
                        class User: id = uid
                        self.chat = Chat()
                        self.from_user = User()
                        self.id = status_msg.id
                        self.video = None
                        self.caption = None
                        self.caption_entities = None
                fm = FakeMessage(chat_id)
                cancel_event = asyncio.Event()
                TASKS.setdefault(uid, []).append(cancel_event)
                UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
                await sequential_upload_task(uid, c, fm, out_path, out_name, None, cancel_event, default_caption=cap, original_caption=cap, original_download_name=base_name)
            else:
                logger.error(f"Batch Audio Remux FFmpeg error: {res.stderr}")
                await c.send_message(chat_id, f"Error remuxing pair {i+1}.")
        except Exception as e:
            logger.error(f"Batch Audio Remux exception: {e}")
    try: await status_msg.edit("Batch Audio Processing Complete!")
    except Exception: pass
    for p in BATCH_AUDIO_LIST1.get(uid, []):
        try: Path(p['path']).unlink(missing_ok=True)
        except: pass
    for p in BATCH_AUDIO_LIST2.get(uid, []):
        try: Path(p['path']).unlink(missing_ok=True)
        except: pass
    BATCH_AUDIO_STATE[uid] = 'list1'
    BATCH_AUDIO_LIST1[uid] = []
    BATCH_AUDIO_LIST2[uid] = []
    try: await c.send_message(chat_id, "Batch processing complete. Batch Audio Add Mode is still ON.\nSend Base Videos for List 1, or type `off` to exit.")
    except Exception: pass

async def handle_audio_change_file(c: Client, m: Message):
    uid = m.from_user.id
    file_info = m.video or m.document
    if not file_info:
        await m.reply_text("This is not a video file.")
        return
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    DOWNLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    tmp_path = None
    status_msg = None
    try:
        original_name = file_info.file_name or f"video_{file_info.file_unique_id}.mkv"
        if not '.' in original_name:
            original_name += '.mkv'
        tmp_path = get_unique_path(TMP, original_name)
        status_msg = await m.reply_text("Downloading file to analyze audio tracks...", reply_markup=progress_keyboard(task_type='download'))
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
        await status_msg.edit(track_list_text, reply_markup=progress_keyboard(task_type='upload'))
        PENDING_AUDIO_ORDERS[status_msg.id] = {
            'uid': uid,
            'path': tmp_path,
            'original_name': tmp_path.name,
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
            DOWNLOAD_TASKS[uid].remove(cancel_event)
        except Exception:
            pass

async def handle_audio_remux(c: Client, m: Message, in_path: Path, original_name: str, new_stream_map: list, messages_to_delete: list = None, default_caption: str = None):
    uid = m.from_user.id
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    out_name = get_dynamic_filename(uid, original_name)
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
            *map_args,
            "-disposition:a", "0",
            "-disposition:a:0", "default",
            "-metadata", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:v", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:v", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:a", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:a", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:s", "title=[@TA_HD_Anime] Telegram Channel",
            "-metadata:s:s", "handler_name=[@TA_HD_Anime] Telegram Channel",
            "-c:v", "copy",
            "-c:a", "aac", "-ac", "2", "-b:a", "128k", 
            "-c:s", "copy",
            str(out_path)
        ]
        status_msg = None
        if messages_to_delete:
             pass
        try:
            status_msg = await m.reply_text("Changing audio track order (Remuxing)...", reply_markup=progress_keyboard(task_type='upload'))
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
            await status_msg.edit("Audio change complete, uploading file...", reply_markup=progress_keyboard(task_type='upload'))
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
                UPLOAD_TASKS[uid].remove(cancel_event)
            except Exception:
                pass

@app.on_message(filters.command("check_drive") & filters.private)
async def check_drive_cmd(c, m: Message):
    if not is_admin(m.from_user.id): return
    await m.reply_text("Checking Google Drive API connection...")
    service = get_gdrive_service()
    if service:
        try:
            about = await asyncio.to_thread(service.about().get(fields="user").execute)
            email = about['user']['emailAddress']
            msg = (
                f"✅ **Google Drive Connected Successfully!**\n\n"
                f"📧 **Service Email:** `{email}`\n\n"
                f"⚠️ **Note:** To see uploaded files in your personal drive, share a folder with this email as an 'Editor' and set the Folder ID in `GDRIVE_FOLDER_ID`."
            )
            await m.reply_text(msg)
        except Exception as e:
            await m.reply_text(f"❌ API Authenticated, but test failed. Error: {e}")
    else:
        await m.reply_text("❌ Google Drive Connection Failed! Check your `GDRIVE_SERVICE_KEY` JSON formatting.")

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
    new_name = re.sub(r'[\\/*?\"<>|:]', '_', new_name)  
    await m.reply_text(f"Video will be renamed to: {new_name}\n(The replied file will be downloaded and re-uploaded for renaming)")
    cancel_event = asyncio.Event()
    TASKS.setdefault(uid, []).append(cancel_event)
    DOWNLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    try:
        status_msg = await m.reply_text("Downloading file for renaming...", reply_markup=progress_keyboard(task_type='download'))
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    except Exception:
        status_msg = await m.reply_text("Downloading file for renaming...", reply_markup=progress_keyboard(task_type='download'))
        USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
    tmp_out = get_unique_path(TMP, new_name)
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

@app.on_callback_query(filters.regex("cancel_all_download"))
async def cancel_all_download_cb(c, cb):
    uid = cb.from_user.id
    count = 0
    if uid in DOWNLOAD_TASKS:
        for ev in DOWNLOAD_TASKS[uid]:
            try: ev.set()
            except: pass
            count += 1
        DOWNLOAD_TASKS[uid].clear()
    if uid in USER_QUEUES:
        new_queue = asyncio.Queue()
        while not USER_QUEUES[uid].empty():
            try:
                item = USER_QUEUES[uid].get_nowait()
                if item.get('task_type') == 'download':
                    if 'status_msg' in item and item['status_msg']:
                        try: await item['status_msg'].delete()
                        except: pass
                else:
                    await new_queue.put(item)
                USER_QUEUES[uid].task_done()
            except:
                pass
        USER_QUEUES[uid] = new_queue
    await cb.answer(f"Cancelled {count} download tasks and cleared download queue.", show_alert=True)
    try: await cb.message.delete()
    except: pass

@app.on_callback_query(filters.regex("cancel_all_upload"))
async def cancel_all_upload_cb(c, cb):
    uid = cb.from_user.id
    count = 0
    if uid in UPLOAD_TASKS:
        for ev in UPLOAD_TASKS[uid]:
            try: ev.set()
            except: pass
            count += 1
        UPLOAD_TASKS[uid].clear()
    if uid in USER_QUEUES:
        new_queue = asyncio.Queue()
        while not USER_QUEUES[uid].empty():
            try:
                item = USER_QUEUES[uid].get_nowait()
                if item.get('task_type') == 'upload':
                    if 'status_msg' in item and item['status_msg']:
                        try: await item['status_msg'].delete()
                        except: pass
                else:
                    await new_queue.put(item)
                USER_QUEUES[uid].task_done()
            except:
                pass
        USER_QUEUES[uid] = new_queue
    await cb.answer(f"Cancelled {count} upload tasks and cleared upload queue.", show_alert=True)
    try: await cb.message.delete()
    except: pass

@app.on_callback_query(filters.regex("cancel_all"))  
async def cancel_all_cb(c, cb):
    uid = cb.from_user.id
    count = 0
    ACTIVE_CONVERT_SESSION.pop(uid, None)
    if uid in ZIP_DL_QUEUES:
        while not ZIP_DL_QUEUES[uid].empty():
            try:
                item = ZIP_DL_QUEUES[uid].get_nowait()
                if 'queue_msg' in item and item['queue_msg']:
                    try: await item['queue_msg'].delete()
                    except: pass
                ZIP_DL_QUEUES[uid].task_done()
            except: pass
    if uid in USER_QUEUES:
        while not USER_QUEUES[uid].empty():
            try:
                item = USER_QUEUES[uid].get_nowait()
                if 'status_msg' in item and item['status_msg']:
                    try: await item['status_msg'].delete()
                    except: pass
                USER_QUEUES[uid].task_done()
            except: pass
    if uid in USER_WORKERS:
        USER_WORKERS[uid].cancel()
        del USER_WORKERS[uid]
    if uid in BATCH_AUDIO_QUEUES:
        while not BATCH_AUDIO_QUEUES[uid].empty():
            try:
                item = BATCH_AUDIO_QUEUES[uid].get_nowait()
                if 'queue_msg' in item and item['queue_msg']:
                    try: await item['queue_msg'].delete()
                    except: pass
                BATCH_AUDIO_QUEUES[uid].task_done()
            except: pass
    if uid in BATCH_AUDIO_WORKERS:
        BATCH_AUDIO_WORKERS[uid].cancel()
        del BATCH_AUDIO_WORKERS[uid]
    if uid in USER_TASK_EVENTS:
        for ev in USER_TASK_EVENTS[uid].values():
            ev.set()
            count += 1
        USER_TASK_EVENTS[uid].clear()
    if uid in TASKS:
        for ev in TASKS[uid]:
            try: ev.set()
            except: pass
        TASKS[uid].clear()
    if uid in DOWNLOAD_TASKS:
        for ev in DOWNLOAD_TASKS[uid]:
            try: ev.set()
            except: pass
        DOWNLOAD_TASKS[uid].clear()
    if uid in UPLOAD_TASKS:
        for ev in UPLOAD_TASKS[uid]:
            try: ev.set()
            except: pass
        UPLOAD_TASKS[uid].clear()
    for msg_id in list(PENDING_AUDIO_ORDERS.keys()):
        if PENDING_AUDIO_ORDERS[msg_id]['uid'] == uid:
            file_data = PENDING_AUDIO_ORDERS.pop(msg_id)
            try: Path(file_data['path']).unlink(missing_ok=True)
            except: pass
    await cb.answer(f"All {count} tasks and queues cancelled.", show_alert=True)
    try: await cb.message.delete()
    except: pass

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

async def process_file_and_upload(c: Client, m: Message, in_path: Path, target_name: str = None, messages_to_delete: list = None, cancel_event_passed: asyncio.Event = None, passed_uid: int = None, default_caption: str = None, original_caption_passed: str = None, original_download_name: str = None):
    uid = passed_uid if passed_uid else (m.from_user.id if m.from_user else m.chat.id)
    cancel_event = cancel_event_passed
    if not cancel_event:
        cancel_event = asyncio.Event()
        TASKS.setdefault(uid, []).append(cancel_event)
        UPLOAD_TASKS.setdefault(uid, []).append(cancel_event)
    upload_path = in_path
    temp_thumb_path = None
    final_caption_template = USER_CAPTIONS.get(uid)
    status_msg = None
    parts_to_upload = []
    try:
        if cancel_event.is_set():
             raise Exception("Cancelled")
        input_name = in_path.name
        target_name = target_name or input_name
        display_name = original_download_name or target_name
        video_exts = {".mp4", ".mkv", ".avi", ".mov", ".flv", ".wmv", ".webm"}
        audio_exts = {".mp3", ".m4a", ".flac", ".wav", ".aac"}
        is_video_file = getattr(m, 'video', None) or any(input_name.lower().endswith(ext) for ext in video_exts)
        is_audio_file = any(input_name.lower().endswith(ext) for ext in audio_exts)
        orig_metadata = get_video_metadata(in_path) if is_video_file else {'duration': 0}
        orig_duration = orig_metadata.get('duration', 0)
        if is_video_file:
            is_mp4_container = input_name.lower().endswith(".mp4")
            is_mkv_container = input_name.lower().endswith(".mkv")
            has_opus = has_opus_audio(in_path)
            if is_mp4_container:
                if has_opus:
                    final_ext = ".mkv"
                else:
                    final_ext = ".mp4"
            elif is_mkv_container:
                final_ext = ".mkv"
            else:
                final_ext = ".mkv"
            target_stem = Path(target_name).stem
            target_name = target_stem + final_ext
            processed_path = TMP / f"proc_{uid}_{int(datetime.now().timestamp())}_{target_name}"
            try:
                status_text = "Processing video (Metadata & Format Check)..."
                if messages_to_delete:
                     pass
                status_msg = await c.send_message(m.chat.id, status_text, reply_markup=progress_keyboard(task_type='upload'))
                USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            except Exception:
                status_msg = await c.send_message(m.chat.id, status_text, reply_markup=progress_keyboard(task_type='upload'))
                USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
            if messages_to_delete:
                messages_to_delete.append(status_msg.id)
            else:
                messages_to_delete = [status_msg.id]
            cmd = [
                "ffmpeg", "-y",
                "-i", str(in_path),
                "-map", "0",
                "-c", "copy",
                "-metadata", "title=[@TA_HD_Anime] Telegram Channel",
                "-metadata:s:v", "title=[@TA_HD_Anime] Telegram Channel",
                "-metadata:s:v", "handler_name=[@TA_HD_Anime] Telegram Channel",
                "-metadata:s:a", "title=[@TA_HD_Anime] Telegram Channel",
                "-metadata:s:a", "handler_name=[@TA_HD_Anime] Telegram Channel",
                "-metadata:s:s", "title=[@TA_HD_Anime] Telegram Channel",
                "-metadata:s:s", "handler_name=[@TA_HD_Anime] Telegram Channel",
                "-progress", "pipe:1",
                "-nostats",
                str(processed_path)
            ]
            if cancel_event.is_set(): raise Exception("Cancelled")
            if orig_duration > 0:
                process = await asyncio.create_subprocess_exec(
                    *cmd,
                    stdout=asyncio.subprocess.PIPE,
                    stderr=asyncio.subprocess.PIPE
                )
                start_t = time.time()
                while True:
                    if cancel_event.is_set():
                        process.terminate()
                        raise Exception("Cancelled")
                    line = await process.stdout.readline()
                    if not line:
                        break
                    line = line.decode('utf-8').strip()
                    if line.startswith("out_time_us="):
                        us_str = line.split("=")[1]
                        try:
                            if us_str != "N/A":
                                out_time_sec = int(us_str) / 1000000.0
                                await progress_callback(out_time_sec, orig_duration, "Processing video (Metadata & Format Check)...", status_msg, start_t, is_time_based=True, original_name=display_name)
                        except Exception:
                            pass
                await process.wait()
                if process.returncode == 0 and processed_path.exists() and processed_path.stat().st_size > 0:
                    upload_path = processed_path
                else:
                    logger.warning("Processing failed. Uploading original.")
            else:
                result = await asyncio.to_thread(subprocess.run, cmd, capture_output=True, text=True, check=False, timeout=3600)
                if result.returncode == 0 and processed_path.exists() and processed_path.stat().st_size > 0:
                    upload_path = processed_path
                else:
                    logger.warning(f"Processing failed: {result.stderr}. Uploading original.")
        video_metadata = get_video_metadata(upload_path) if (is_video_file and upload_path.exists()) else {'duration': 0, 'width': 0, 'height': 0}
        duration_sec = video_metadata.get('duration', 0)
        width_px = video_metadata.get('width', 0)
        height_px = video_metadata.get('height', 0)
        if is_video_file:
            thumb_path = USER_THUMBS.get(uid)
            if not thumb_path:
                temp_thumb_path = TMP / f"thumb_{uid}_{int(datetime.now().timestamp())}.jpg"
                if uid in USER_THUMB_TIME:
                    thumb_time_sec = USER_THUMB_TIME[uid]
                else:
                    if duration_sec > 60:
                        thumb_time_sec = 60
                    else:
                        thumb_time_sec = 1
                ok = await generate_video_thumbnail(upload_path, temp_thumb_path, timestamp_sec=thumb_time_sec)
                if ok:
                    thumb_path = str(temp_thumb_path)
        try:
            if status_msg:
                await status_msg.edit("Starting upload...", reply_markup=progress_keyboard(task_type='upload'))
            else:
                status_msg = await c.send_message(m.chat.id, "Starting upload...", reply_markup=progress_keyboard(task_type='upload'))
                USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
        except Exception:
             status_msg = await c.send_message(m.chat.id, "Starting upload...", reply_markup=progress_keyboard(task_type='upload'))
             USER_TASK_EVENTS.setdefault(uid, {})[status_msg.id] = cancel_event
        if messages_to_delete:
            if status_msg.id not in messages_to_delete:
                messages_to_delete.append(status_msg.id)
        else:
            messages_to_delete = [status_msg.id]
        if cancel_event.is_set():
            raise Exception("Cancelled")
        use_orig_cap = False
        if not final_caption_template or uid in USE_ORIGINAL_CAPTION_IN_MULTI_GROUP:
            use_orig_cap = True
        if use_orig_cap:
            if original_caption_passed:
                caption_to_use = original_caption_passed
            elif default_caption:
                caption_to_use = f"{default_caption}"
            else:
                caption_to_use = f"{display_name}"
        else:
            caption_to_use = process_dynamic_caption(uid, final_caption_template)
        caption_to_use = make_bold(caption_to_use)
        parts_to_upload = [(upload_path, target_name, None, duration_sec)]
        MAX_SPLIT_SIZE = 1950 * 1024 * 1024
        LIMIT_SIZE = 2000 * 1024 * 1024
        if is_video_file and upload_path.exists() and upload_path.stat().st_size > LIMIT_SIZE and duration_sec > 0:
            try:
                if status_msg:
                    await status_msg.edit("Video size is greater than 2000MB, splitting video into smaller parts...", reply_markup=progress_keyboard(task_type='upload'))
            except Exception: pass
            num_parts = math.ceil(upload_path.stat().st_size / MAX_SPLIT_SIZE)
            base_chunk = duration_sec / num_parts
            split_parts = []
            for i in range(num_parts):
                s_time = i * base_chunk
                e_time = (i + 1) * base_chunk
                if i > 0:
                    s_time -= 10
                if i < num_parts - 1:
                    e_time += 10
                s_time = max(0, s_time)
                e_time = min(duration_sec, e_time)
                part_duration = e_time - s_time
                part_stem = Path(target_name).stem
                part_ext = Path(target_name).suffix
                part_target_name = f"{part_stem} - Part {i+1:02d}{part_ext}"
                part_path = TMP / f"split_{uid}_{int(datetime.now().timestamp())}_{i}_{target_name}"
                cmd = [
                    "ffmpeg",
                    "-y",
                    "-i", str(upload_path),
                    "-ss", str(s_time),
                    "-to", str(e_time),
                    "-c", "copy",
                    str(part_path)
                ]
                if cancel_event.is_set(): raise Exception("Cancelled")
                await asyncio.to_thread(subprocess.run, cmd, capture_output=True, text=True, check=False)
                if part_path.exists() and part_path.stat().st_size > 0:
                    split_parts.append((part_path, part_target_name, i+1, part_duration))
            if split_parts:
                parts_to_upload = split_parts
        last_exc = None
        for current_upload_path, current_target_name, part_num, current_duration in parts_to_upload:
            if cancel_event.is_set(): raise Exception("Cancelled")
            part_caption = caption_to_use
            if part_num is not None:
                if part_caption.endswith("**"):
                    part_caption = part_caption[:-2] + f"\n✔️ Part - {part_num:02d}**"
                else:
                    part_caption += f"\n✔️ Part - {part_num:02d}"
            part_caption = make_bold(part_caption)
            try:
                if status_msg:
                    action_text = f"Starting upload... {'(Part ' + str(part_num) + ')' if part_num else ''}"
                    await status_msg.edit(action_text, reply_markup=progress_keyboard(task_type='upload'))
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
                            await progress_callback(current, total, action_text, status_msg, start_t, original_name=display_name)
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
            raise last_exc
    except Exception as e:
        raise e
    finally:
        try:
            if upload_path != in_path and upload_path.exists():
                upload_path.unlink()
            if in_path.exists():
                in_path.unlink()
            if temp_thumb_path and Path(temp_thumb_path).exists():
                Path(temp_thumb_path).unlink()
            for p_path, _, p_num, _ in parts_to_upload:
                 if p_num is not None and p_path.exists():
                      p_path.unlink()
            if cancel_event in TASKS.get(uid, []): TASKS[uid].remove(cancel_event)
            if cancel_event in UPLOAD_TASKS.get(uid, []): UPLOAD_TASKS[uid].remove(cancel_event)
            if status_msg and status_msg.id in USER_TASK_EVENTS.get(uid, {}):
                USER_TASK_EVENTS[uid].pop(status_msg.id)
        except Exception:
            pass

@flask_app.route('/')
def home():
    html_content = """
<!DOCTYPE html>
<html>
<head>
    <title>Bot Server</title>
</head>
<body>
    <h1>Bot is Running!</h1>
    <p>Telegram bot is active.</p>
</body>
</html>
    """
    return render_template_string(html_content)

@flask_app.route('/dl/<path:filename>')
def download_local_file(filename):
    file_path = TMP / filename
    if file_path.exists() and file_path.is_file():
        mime_type, _ = mimetypes.guess_type(str(file_path))
        return send_from_directory(TMP, filename, mimetype=mime_type, as_attachment=False)
    return "File not found.", 404

@flask_app.route('/dl_stream')
def force_download_remote_file():
    url = request.args.get('url')
    if not url:
        return "URL parameter is required.", 400
    def generate():
        try:
            headers = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"}
            with requests.get(url, stream=True, timeout=15, headers=headers) as r:
                r.raise_for_status()
                for chunk in r.iter_content(chunk_size=8192):
                    if chunk:
                        yield chunk
        except Exception as e:
            yield str(e).encode()
    mime_type, _ = mimetypes.guess_type(url)
    if not mime_type:
        mime_type = 'application/octet-stream'
    filename = os.path.basename(urllib.parse.urlparse(url).path)
    if not filename:
        filename = "downloaded_video.mp4"
    headers = {
        'Content-Disposition': f'attachment; filename="{filename}"',
        'Content-Type': mime_type
    }
    return Response(generate(), headers=headers)

@flask_app.route('/stream')
def stream_remote_file():
    url = request.args.get('url')
    if not url:
        return "URL parameter is required.", 400
    def generate():
        try:
            headers = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64)"}
            with requests.get(url, stream=True, timeout=15, headers=headers) as r:
                r.raise_for_status()
                for chunk in r.iter_content(chunk_size=8192):
                    if chunk:
                        yield chunk
        except Exception as e:
            yield str(e).encode()
    mime_type, _ = mimetypes.guess_type(url)
    if not mime_type:
        mime_type = 'video/mp4'
    headers = {
        'Content-Disposition': 'inline',
        'Content-Type': mime_type
    }
    return Response(generate(), headers=headers)

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

@app.on_message(filters.command("check") & filters.private)
async def check_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized.")
        return
    ping_status = "✅ **Ping Service:** Active" if RENDER_EXTERNAL_HOSTNAME else "❌ **Ping Service:** Not active (RENDER_EXTERNAL_HOSTNAME not set)"
    if RENDER_EXTERNAL_HOSTNAME:
        url = f"http://{RENDER_EXTERNAL_HOSTNAME}"
        try:
            response = requests.get(url, timeout=5)
            ping_result = f"✅ **Ping Test:** Success (Status {response.status_code})"
        except Exception as e:
            ping_result = f"❌ **Ping Test:** Failed – {str(e)}"
    else:
        ping_result = "⚠️ Cannot test ping – RENDER_EXTERNAL_HOSTNAME not set"
    flask_status = "✅ **Flask Server:** Running"
    bot_status = "✅ **Bot:** Running"  
    msg = (
        f"**Bot Health Check**\n\n"
        f"{bot_status}\n"
        f"{flask_status}\n"
        f"{ping_status}\n"
        f"{ping_result}\n\n"
        f"**RENDER_EXTERNAL_HOSTNAME:** `{RENDER_EXTERNAL_HOSTNAME}`\n"
        f"**PORT:** `{PORT}`"
    )
    await m.reply_text(msg)

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
