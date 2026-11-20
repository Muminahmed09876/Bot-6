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
from pyrogram.enums import ParseMode, ChatType
from pyrogram.errors import FloodWait, RPCError
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

ADD_MODE = set()
EDIT_MODE = set()
EDIT_BUTTONS = {}
SAVED_CHANNELS = {}
EDIT_SESSION = {}
EDIT_SESSION_MSG = {}

ADMIN_ID = int(os.getenv("ADMIN_ID", ""))
MAX_SIZE = 1000 * 1024 * 1024 * 1024

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
        status_msg = await message.reply_text(f"Uploading `{file_name}` to Google Drive...", reply_markup=progress_keyboard())
        
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
        ),
        "add_edit": (
            "📢 **Add/Edit Feature - Tutorial**\n\n"
            "**/add** - চ্যানেলের মেসেজ forward করে channel save করবেন।\n"
            "**/edit** - ৪টি button আসবে:\n"
            "‣ 🎬 **Cover Only** - শুধু video cover/thumbnail change\n"
            "‣ 📝 **Caption Only** - শুধু caption change\n"
            "‣ 🎬📝 **Cover and Caption** - দুটোই change\n"
            "‣ 🤖 **Bot Send: OFF/ON** - OFF হলে channel post edit হবে, ON হলে bot নিজে send করবে\n\n"
            "**কীভাবে ব্যবহার করবেন:**\n"
            "1. আগে `/setthumb` দিয়ে cover এবং `/set_caption` দিয়ে caption সেট করুন\n"
            "2. `/add` দিয়ে চ্যানেল save করুন\n"
            "3. `/edit` দিয়ে mode select করুন\n"
            "4. চ্যানেল থেকে video forward করুন (file_id save হবে)\n"
            "5. **OK** button ক্লিক করুন - ছোট file_id থেকে শুরু হবে\n"
            "6. Video download ছাড়াই edit হবে!"
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
        BotCommand("add", "Add channel for editing (admin only)"),
        BotCommand("edit", "Edit channel posts (admin only)"),
        BotCommand("cancel", "Cancel current operation (admin only)"),
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
                        await status_msg.edit(f"Starting YT-DLP Download for {res}p...", reply_markup=progress_keyboard())
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

def extract_media_info_from_msg(message: Message):
    if message.video:
        return {
            "kind": "video",
            "api_type": "video",
            "file_id": message.video.file_id,
            "file_unique_id": message.video.file_unique_id,
        }
    if message.document:
        mime = (message.document.mime_type or "").lower()
        fname = (message.document.file_name or "").lower()
        is_vid = mime.startswith("video/") or fname.endswith(
            (".mp4", ".mkv", ".mov", ".avi", ".webm", ".flv", ".3gp")
        )
        return {
            "kind": "video_doc" if is_vid else "document",
            "api_type": "video" if is_vid else "document",
            "file_id": message.document.file_id,
            "file_unique_id": message.document.file_unique_id,
        }
    return None

def build_edit_keyboard(uid: int) -> InlineKeyboardMarkup:
    state = EDIT_BUTTONS.get(uid, {'cover': False, 'caption': False, 'bot_send': False})
    cover_mark = "✅" if state.get('cover') else "⬜"
    caption_mark = "✅" if state.get('caption') else "⬜"
    bot_mark = "✅ ON" if state.get('bot_send') else "❌ OFF"
    
    keyboard = [
        [InlineKeyboardButton(f"{cover_mark} Cover Only", callback_data="edit_mode_cover")],
        [InlineKeyboardButton(f"{caption_mark} Caption Only", callback_data="edit_mode_caption")],
        [InlineKeyboardButton(f"{cover_mark} Cover + {caption_mark} Caption", callback_data="edit_mode_both")],
        [InlineKeyboardButton(f"🤖 Bot Send: {bot_mark}", callback_data="edit_toggle_bot_send")],
        [InlineKeyboardButton("❌ Exit Edit Mode", callback_data="edit_exit")]
    ]
    return InlineKeyboardMarkup(keyboard)

async def api_edit_message_media_cover(chat_id: int, message_id: int, api_type: str, file_id: str, cover_file_id: str = None, caption: str = ""):
    api_base = f"https://api.telegram.org/bot{BOT_TOKEN}"
    media_obj = {
        "type": api_type,
        "media": file_id,
        "caption": caption,
    }
    if cover_file_id and api_type == "video":
        media_obj["cover"] = cover_file_id

    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "media": media_obj,
    }
    async with aiohttp.ClientSession() as session:
        async with session.post(f"{api_base}/editMessageMedia", json=payload) as resp:
            return await resp.json()

async def api_edit_message_caption(chat_id: int, message_id: int, caption: str):
    api_base = f"https://api.telegram.org/bot{BOT_TOKEN}"
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "caption": caption,
    }
    async with aiohttp.ClientSession() as session:
        async with session.post(f"{api_base}/editMessageCaption", json=payload) as resp:
            return await resp.json()

async def api_send_media(chat_id: int, api_type: str, file_id: str, cover_file_id: str = None, caption: str = ""):
    api_base = f"https://api.telegram.org/bot{BOT_TOKEN}"
    if api_type == "video":
        method = "sendVideo"
        payload = {
            "chat_id": chat_id,
            "video": file_id,
            "caption": caption,
            "supports_streaming": True,
        }
        if cover_file_id:
            payload["cover"] = cover_file_id
    else:
        method = "sendDocument"
        payload = {
            "chat_id": chat_id,
            "document": file_id,
            "caption": caption,
        }

    async with aiohttp.ClientSession() as session:
        async with session.post(f"{api_base}/{method}", json=payload) as resp:
            return await resp.json()

@app.on_message(filters.command("add") & filters.private)
async def add_channel_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    
    ADD_MODE.add(uid)
    EDIT_MODE.discard(uid)
    await m.reply_text(
        "📢 **Add Channel Mode**\n\n"
        "Please **forward any message** from your channel to this chat.\n"
        "The bot will save the channel info for future editing.\n\n"
        "Type /cancel to cancel."
    )

@app.on_message(filters.command("cancel") & filters.private)
async def cancel_cmd(c, m: Message):
    uid = m.from_user.id
    ADD_MODE.discard(uid)
    EDIT_MODE.discard(uid)
    EDIT_SESSION.pop(uid, None)
    await m.reply_text("Cancelled.")

@app.on_message(filters.command("edit") & filters.private)
async def edit_cmd(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        await m.reply_text("You are not authorized to use this command.")
        return
    
    if uid not in SAVED_CHANNELS:
        await m.reply_text(
            "⚠️ No channel saved yet.\n\n"
            "Use /add first to save your channel by forwarding a message from it."
        )
        return
    
    if uid not in EDIT_BUTTONS:
        EDIT_BUTTONS[uid] = {'cover': False, 'caption': False, 'bot_send': False}
    
    EDIT_MODE.add(uid)
    ADD_MODE.discard(uid)
    EDIT_SESSION.pop(uid, None)
    
    ch = SAVED_CHANNELS[uid]
    cover_id = USER_THUMBS.get(uid)
    caption_text = USER_CAPTIONS.get(uid)
    
    info_text = (
        f"✏️ **Edit Channel Mode**\n\n"
        f"**Saved Channel:** `{ch['title']}`\n"
        f"**Channel ID:** `{ch['chat_id']}`\n\n"
        f"**Cover (from /setthumb):** {'✅ Set' if cover_id else '❌ Not set'}\n"
        f"**Caption (from /set_caption):** {'✅ Set' if caption_text else '❌ Not set'}\n\n"
        f"**Select edit options below:**\n"
        f"1. **Cover Only** - only change video thumbnail/cover\n"
        f"2. **Caption Only** - only change caption\n"
        f"3. **Cover + Caption** - change both\n"
        f"4. **Bot Send ON/OFF** - OFF = edit channel post, ON = bot sends to user\n\n"
        f"After selecting, **forward videos from your channel** to this chat.\n"
        f"The bot will save `file_id` and reply with an **OK** button.\n"
        f"Click **OK** to start editing from the smallest file_id."
    )
    
    await m.reply_text(info_text, reply_markup=build_edit_keyboard(uid))

@app.on_callback_query(filters.regex("^edit_mode_"))
async def edit_mode_callback(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("Not authorized.", show_alert=True)
        return
    
    if uid not in EDIT_BUTTONS:
        EDIT_BUTTONS[uid] = {'cover': False, 'caption': False, 'bot_send': False}
    
    state = EDIT_BUTTONS[uid]
    action = cb.data.replace("edit_mode_", "")
    
    if action == "cover":
        state['cover'] = True
        state['caption'] = False
        msg = "Cover Only mode selected. Forward channel videos now."
    elif action == "caption":
        state['cover'] = False
        state['caption'] = True
        msg = "Caption Only mode selected. Forward channel videos now."
    elif action == "both":
        state['cover'] = True
        state['caption'] = True
        msg = "Cover + Caption mode selected. Forward channel videos now."
    
    await cb.answer(msg, show_alert=True)
    try:
        await cb.message.edit_reply_markup(build_edit_keyboard(uid))
    except Exception:
        pass

@app.on_callback_query(filters.regex("^edit_toggle_bot_send$"))
async def edit_toggle_bot_send_cb(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("Not authorized.", show_alert=True)
        return
    
    if uid not in EDIT_BUTTONS:
        EDIT_BUTTONS[uid] = {'cover': False, 'caption': False, 'bot_send': False}
    
    EDIT_BUTTONS[uid]['bot_send'] = not EDIT_BUTTONS[uid].get('bot_send', False)
    new_state = "ON" if EDIT_BUTTONS[uid]['bot_send'] else "OFF"
    await cb.answer(f"Bot Send: {new_state}", show_alert=True)
    try:
        await cb.message.edit_reply_markup(build_edit_keyboard(uid))
    except Exception:
        pass

@app.on_callback_query(filters.regex("^edit_exit$"))
async def edit_exit_cb(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    EDIT_MODE.discard(uid)
    EDIT_SESSION.pop(uid, None)
    await cb.answer("Exited Edit Mode.", show_alert=True)
    try:
        await cb.message.edit_text("Edit mode has been closed.")
    except Exception:
        pass

@app.on_callback_query(filters.regex("^edit_ok_"))
async def edit_ok_cb(c: Client, cb: CallbackQuery):
    uid = cb.from_user.id
    if not is_admin(uid):
        await cb.answer("Not authorized.", show_alert=True)
        return
    
    if uid not in EDIT_SESSION or not EDIT_SESSION[uid]:
        await cb.answer("No pending media to edit.", show_alert=True)
        return
    
    await cb.answer("Starting edit process...", show_alert=False)
    
    items = list(EDIT_SESSION[uid])
    items.sort(key=lambda x: x['origin_msg_id'])
    
    state = EDIT_BUTTONS.get(uid, {'cover': False, 'caption': False, 'bot_send': False})
    cover_fid = USER_THUMBS.get(uid)
    caption_template = USER_CAPTIONS.get(uid)
    ch = SAVED_CHANNELS.get(uid)
    
    if not ch:
        await cb.message.edit_text("❌ No saved channel.")
        return
    
    if state['cover'] and not cover_fid:
        await cb.message.edit_text("❌ Cover mode selected but no thumbnail set. Use /setthumb first.")
        return
    
    if state['caption'] and not caption_template:
        await cb.message.edit_text("❌ Caption mode selected but no caption set. Use /set_caption first.")
        return
    
    do_cover = state.get('cover', False)
    do_caption = state.get('caption', False)
    bot_send = state.get('bot_send', False)
    
    if not do_cover and not do_caption:
        await cb.message.edit_text("❌ No edit mode selected. Use /edit to choose options.")
        return
    
    status_msg = await cb.message.edit_text(f"⏳ Processing {len(items)} item(s)...")
    
    success_count = 0
    fail_count = 0
    
    for idx, item in enumerate(items, 1):
        try:
            new_caption = None
            if do_caption:
                if caption_template:
                    new_caption = process_dynamic_caption(uid, caption_template)
            
            if bot_send:
                api_type = item['api_type']
                result = await api_send_media(
                    chat_id=uid,
                    api_type=api_type,
                    file_id=item['file_id'],
                    cover_file_id=cover_fid if do_cover else None,
                    caption=new_caption if new_caption is not None else (item.get('original_caption') or "")
                )
                if result.get('ok'):
                    success_count += 1
                else:
                    fail_count += 1
                    logger.error(f"Bot send failed: {result}")
            else:
                if do_cover and do_caption:
                    result = await api_edit_message_media_cover(
                        chat_id=ch['chat_id'],
                        message_id=item['origin_msg_id'],
                        api_type=item['api_type'],
                        file_id=item['file_id'],
                        cover_file_id=cover_fid,
                        caption=new_caption if new_caption is not None else (item.get('original_caption') or "")
                    )
                    if result.get('ok'):
                        success_count += 1
                    else:
                        fail_count += 1
                        logger.error(f"Edit media+caption failed: {result}")
                elif do_cover:
                    result = await api_edit_message_media_cover(
                        chat_id=ch['chat_id'],
                        message_id=item['origin_msg_id'],
                        api_type=item['api_type'],
                        file_id=item['file_id'],
                        cover_file_id=cover_fid,
                        caption=item.get('original_caption') or ""
                    )
                    if result.get('ok'):
                        success_count += 1
                    else:
                        fail_count += 1
                        logger.error(f"Edit cover failed: {result}")
                elif do_caption:
                    if new_caption is not None:
                        result = await api_edit_message_caption(
                            chat_id=ch['chat_id'],
                            message_id=item['origin_msg_id'],
                            caption=new_caption
                        )
                        if result.get('ok'):
                            success_count += 1
                        else:
                            fail_count += 1
                            logger.error(f"Edit caption failed: {result}")
            
            await asyncio.sleep(1)
            
            if idx % 5 == 0:
                try:
                    await status_msg.edit_text(
                        f"⏳ Processing... {idx}/{len(items)}\n"
                        f"✅ Success: {success_count}\n"
                        f"❌ Failed: {fail_count}"
                    )
                except Exception:
                    pass
                    
        except Exception as e:
            logger.error(f"Edit item error: {e}")
            fail_count += 1
    
    EDIT_SESSION.pop(uid, None)
    
    summary = (
        f"✅ **Edit Complete!**\n\n"
        f"**Total:** {len(items)}\n"
        f"**Success:** {success_count}\n"
        f"**Failed:** {fail_count}\n"
        f"**Mode:** {'Cover + Caption' if (do_cover and do_caption) else ('Cover Only' if do_cover else 'Caption Only')}\n"
        f"**Target:** {'Bot Send' if bot_send else 'Channel Edit'}"
    )
    try:
        await status_msg.edit_text(summary)
    except Exception:
        pass

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
        "/add - Add channel for editing (admin only)\n"
        "/edit - Edit channel posts (admin only)\n"
        "/cancel - Cancel current operation (admin only)\n"
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
    
    ADD_MODE.clear()
    EDIT_MODE.clear()
    EDIT_BUTTONS.clear()
    SAVED_CHANNELS.clear()
    EDIT_SESSION.clear()
    EDIT_SESSION_MSG.clear()
    
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

@app.on_message(filters.forwarded & filters.private)
async def forwarded_handler(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    
    origin_chat = m.forward_from_chat
    origin_msg_id = m.forward_from_message_id
    
    if uid in ADD_MODE:
        if not origin_chat or origin_chat.type != ChatType.CHANNEL:
            await m.reply_text("Please forward a message from a **Channel**.")
            return
        
        SAVED_CHANNELS[uid] = {
            'chat_id': origin_chat.id,
            'title': origin_chat.title or "Channel"
        }
        ADD_MODE.discard(uid)
        await m.reply_text(
            f"✅ **Channel Saved!**\n\n"
            f"**Title:** `{SAVED_CHANNELS[uid]['title']}`\n"
            f"**ID:** `{SAVED_CHANNELS[uid]['chat_id']}`\n\n"
            f"Now use /edit to start editing this channel's posts."
        )
        return
    
    if uid in EDIT_MODE:
        info = extract_media_info_from_msg(m)
        if not info:
            return
        
        if info['kind'] == 'document':
            await m.reply_text("Only video or video-document supported. Please forward a video.")
            return
        
        if not origin_chat or origin_chat.id != SAVED_CHANNELS.get(uid, {}).get('chat_id'):
            await m.reply_text(
                f"⚠️ This message is not from your saved channel.\n"
                f"Please forward from: **{SAVED_CHANNELS.get(uid, {}).get('title', 'your channel')}**\n"
                f"Or use /add to save a different channel first."
            )
            return
        
        if not origin_msg_id:
            await m.reply_text("Could not detect original message ID. Make sure the channel is public or bot is admin.")
            return
        
        if uid not in EDIT_SESSION:
            EDIT_SESSION[uid] = []
        
        EDIT_SESSION[uid].append({
            'file_id': info['file_id'],
            'api_type': info['api_type'],
            'kind': info['kind'],
            'origin_msg_id': origin_msg_id,
            'original_caption': m.caption or "",
            'file_unique_id': info.get('file_unique_id', '')
        })
        
        count = len(EDIT_SESSION[uid])
        sort_order = sorted(EDIT_SESSION[uid], key=lambda x: x['origin_msg_id'])
        min_id = sort_order[0]['origin_msg_id']
        
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ OK - Start Editing", callback_data=f"edit_ok_{uid}")],
            [InlineKeyboardButton("❌ Clear Session", callback_data="edit_exit")]
        ])
        
        await m.reply_text(
            f"📥 **Media saved to session** (#{count})\n"
            f"**Orig Message ID:** `{origin_msg_id}`\n"
            f"**Smallest ID in session:** `{min_id}`\n\n"
            f"Forward more videos, or click **OK** to start editing from smallest file_id.",
            reply_markup=markup
        )
        return

@app.on_message((filters.video | filters.document) & filters.private)
async def video_handler(c, m: Message):
    uid = m.from_user.id
    if not is_admin(uid):
        return
    
    if uid in EDIT_MODE:
        await m.reply_text(
            "⚠️ In Edit Mode, please **forward** videos from your channel.\n"
            "Direct uploads are not supported for edit mode."
        )
        return
    
    if m.video:
        original_name = m.video.file_name or f"{m.video.file_unique_id}.mp4"
    else:
        original_name = m.document.file_name or f"{m.document.file_unique_id}.bin"
    
    if uid in UPLOAD_DRIVE_MODE or uid in DOWNLOAD_ONLY_MODE or True:
        await add_to_queue(uid, c, m, original_name, is_url=False, original_caption=m.caption)

async def process_file_and_upload(client, message, file_path, target_name=None, original_download_name=None, messages_to_delete=None, cancel_event_passed=None, passed_uid=None, default_caption=None, original_caption_passed=None):
    pass

async def download_and_process_generic(client, m, url, status_msg, cancel_event):
    pass

async def text_handler(c, m: Message):
    pass

@app.on_message(filters.command("check") & filters.private)
async def check_handler(c, m: Message):
    await m.reply_text("Bot is alive and responding.")

if __name__ == "__main__":
    app.run()
