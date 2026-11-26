import asyncio
import html
import os
import re
import socket
import threading
import time
import traceback
import urllib.request
import requests

# Render / Python 3.14-এ event loop আগে থেকেই সেট করে রাখা
_loop = asyncio.new_event_loop()
asyncio.set_event_loop(_loop)

import aiohttp
from flask import Flask, render_template_string

try:
    from pyrofork import Client, filters
    from pyrofork.enums import ChatMemberStatus, ChatType
    from pyrofork.errors import FloodWait, RPCError
    from pyrofork.types import InlineKeyboardButton, InlineKeyboardMarkup
except ImportError:
    from pyrogram import Client, filters
    from pyrogram.enums import ChatMemberStatus, ChatType
    from pyrogram.errors import FloodWait, RPCError
    from pyrogram.types import InlineKeyboardButton, InlineKeyboardMarkup


def get_env_val(key: str, default: str | None = None) -> str | None:
    val = os.getenv(key)
    if val is not None and str(val).strip() != "":
        return str(val).strip()
    return default


def parse_admin_id(raw_val: str | None) -> int | None:
    if not raw_val:
        return None
    cleaned = str(raw_val).strip().strip('"').strip("'")
    match = re.search(r"-?\d+", cleaned)
    if not match:
        return None
    try:
        return int(match.group(0))
    except ValueError:
        return None


def parse_channel_ids_env(raw_val: str | None) -> list[int]:
    if not raw_val:
        return []
    found = []
    for part in re.split(r"[\s,;]+", str(raw_val).strip()):
        cleaned = part.strip().strip('"').strip("'")
        if not cleaned:
            continue
        m = re.fullmatch(r"-?\d+", cleaned)
        if m:
            val = int(m.group(0))
            if val not in found:
                found.append(val)
    return found


API_ID = int(get_env_val("API_ID", "0"))
API_HASH = get_env_val("API_HASH", "")
BOT_TOKEN = get_env_val("BOT_TOKEN", "")
API_BASE = f"https://api.telegram.org/bot{BOT_TOKEN}"

# Persistent requests.Session (tg_session) যাতে প্রতিবার নতুন TCP/SSL কানেকশন খোলার ওভারহেড কমে
tg_session = requests.Session()
_adapter = requests.adapters.HTTPAdapter(pool_connections=50, pool_maxsize=50)
tg_session.mount("https://", _adapter)
tg_session.mount("http://", _adapter)

ADMIN_ID = parse_admin_id(get_env_val("ADMIN_ID"))
ENV_CHANNEL_IDS = parse_channel_ids_env(get_env_val("CHANNEL_ID"))
print(f"Render Bot Starting | ADMIN_ID: {ADMIN_ID} | ENV_CHANNEL_IDS: {ENV_CHANNEL_IDS}")

PORT = int(get_env_val("PORT", "10000"))

RENDER_EXTERNAL_HOSTNAME = get_env_val("RENDER_EXTERNAL_HOSTNAME")
if not RENDER_EXTERNAL_HOSTNAME:
    try:
        _public_ip = urllib.request.urlopen("https://api.ipify.org", timeout=3).read().decode("utf8")
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

PUBLIC_BASE_URL = get_env_val("PUBLIC_BASE_URL")
if not PUBLIC_BASE_URL:
    PUBLIC_BASE_URL = f"http://{RENDER_EXTERNAL_HOSTNAME}"
elif not PUBLIC_BASE_URL.startswith(("http://", "https://")):
    PUBLIC_BASE_URL = f"http://{PUBLIC_BASE_URL}"

flask_app = Flask(__name__)


@flask_app.route("/")
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
            <h1>Bot is running! ✅</h1>
            <p>This page confirms that the bot's web server is active.</p>
        </div>
    </body>
    </html>
    """
    return render_template_string(html_content)


@flask_app.route("/ping")
def ping():
    return "pong", 200


def _self_ping_worker():
    ping_url = f"{PUBLIC_BASE_URL.rstrip('/')}/ping"
    while True:
        time.sleep(240)
        try:
            urllib.request.urlopen(ping_url, timeout=10).read()
        except Exception:
            pass


def start_flask_server():
    threading.Thread(
        target=lambda: flask_app.run(host="0.0.0.0", port=PORT, debug=False, use_reloader=False),
        daemon=True,
    ).start()
    threading.Thread(target=_self_ping_worker, daemon=True).start()


def is_admin(user_id: int | None) -> bool:
    if ADMIN_ID is None:
        return True
    if user_id is None:
        return False
    return int(user_id) == ADMIN_ID


app = Client(
    "render_cover_editor_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN,
    in_memory=True,
    sleep_threshold=1,
)

user_cover_file_ids = {}     # {user_id: photo_file_id}
user_channels = {}           # {user_id: {"chat_id": int, "title": str}}
user_channel_lists = {}      # {user_id: [{"chat_id": int, "title": str}, ...]}
user_upload_delays = {}      # {user_id: float}
user_forward_tags = {}       # {user_id: bool} -> True = on, False = off
user_captions = {}           # {user_id: {"template": str, "index": int}}
user_modes = {}              # {user_id: "cover" | "caption" | "both"}
pending_edits = {}           # {user_id: {sort_key: {"file_id": str, "api_type": str, "orig_caption": str, "channel_edit": bool, "msg_id": int | None}}}
resolved_channel_titles = {} # {chat_id: str}

waiting_for_thumb = set()    # {user_id}
waiting_for_channel = set()  # {user_id}
waiting_for_caption = set()  # {user_id}

# /cover ফিচারের স্টেটসমূহ (command দিয়ে অফ না করা পর্যন্ত অটো অফ হবে না)
cover_instant_mode = set()   # {user_id} -> /cover বা /cover off দিলে চালু থাকবে (ভিডিও পাঠালে/ফরোয়ার্ড করলে সাথে সাথে সেই ভিডিওর cover পাঠাবে)
cover_batch_mode = set()     # {user_id} -> /cover on দিলে চালু থাকবে, /cover off দিলে instant mode-এ যাবে
cover_batch_queue = {}       # {user_id: [{"file_id": str, "cover_file_id": str | None, "kind": str, "order": int, "chat_id": int, "msg_id": int}, ...]}
cover_batch_counter = {}     # {user_id: int}

# /change_media ফিচারের স্টেটসমূহ (command দিয়ে অফ না করা পর্যন্ত অটো অফ হবে না)
change_media_state = {}      # {user_id: {"stage": "posts" | "media", "posts": [...], "media": [...], "counter": int}}

# /create_post ফিচারের স্টেটসমূহ (command দিয়ে অফ না করা পর্যন্ত অটো অফ হবে না)
create_post_state = {}       # {user_id: {"step": "image" | "name" | "gen" | "seasons", "photo_id": str | None, "name": str | None, "gen": str | None}}


def extract_forward_origin_info(message):
    origin_chat = getattr(message, "forward_from_chat", None)
    origin_msg_id = getattr(message, "forward_from_message_id", None)

    fwd_origin = getattr(message, "forward_origin", None)
    if fwd_origin is not None:
        if not origin_chat:
            origin_chat = getattr(fwd_origin, "chat", None) or getattr(fwd_origin, "sender_chat", None)
        if not origin_msg_id:
            origin_msg_id = getattr(fwd_origin, "message_id", None)

    return origin_chat, origin_msg_id


async def fetch_channel_title_from_api(client, chat_id: int, force_refresh: bool = False) -> str | None:
    cid = int(chat_id)
    if not force_refresh and cid in resolved_channel_titles and resolved_channel_titles[cid]:
        return resolved_channel_titles[cid]

    try:
        async with aiohttp.ClientSession() as session:
            async with session.post(f"{API_BASE}/getChat", json={"chat_id": cid}) as resp:
                data = await resp.json()
                if isinstance(data, dict) and data.get("ok"):
                    res = data.get("result") or {}
                    title = res.get("title") or res.get("first_name")
                    if title and str(title).strip():
                        clean = str(title).strip()
                        resolved_channel_titles[cid] = clean
                        return clean
                else:
                    print(f"getChat warning for {cid}: {data}")
    except Exception as e:
        print(f"getChat exception for {cid}: {e}")

    try:
        chat_obj = await client.get_chat(cid)
        title = getattr(chat_obj, "title", None) or getattr(chat_obj, "first_name", None)
        if title and str(title).strip():
            clean = str(title).strip()
            resolved_channel_titles[cid] = clean
            return clean
    except Exception:
        pass

    return resolved_channel_titles.get(cid)


async def resolve_all_user_channel_titles(client, user_id: int, force_refresh: bool = False):
    ch_list = ensure_user_channels_loaded(user_id)
    active = get_active_user_channel(user_id)
    for item in ch_list:
        cid = int(item["chat_id"])
        fetched = await fetch_channel_title_from_api(client, cid, force_refresh=force_refresh)
        if fetched:
            item["title"] = fetched
            if active and int(active["chat_id"]) == cid:
                user_channels[user_id]["title"] = fetched


def ensure_user_channels_loaded(user_id: int) -> list[dict]:
    if user_id not in user_channel_lists:
        loaded = []
        for idx, cid in enumerate(ENV_CHANNEL_IDS, start=1):
            cid_int = int(cid)
            cached_title = resolved_channel_titles.get(cid_int)
            loaded.append({
                "chat_id": cid_int,
                "title": cached_title if cached_title else f"Channel {idx} ({cid_int})",
            })
        user_channel_lists[user_id] = loaded
    else:
        existing_ids = {int(x["chat_id"]) for x in user_channel_lists[user_id]}
        for idx, cid in enumerate(ENV_CHANNEL_IDS, start=1):
            cid_int = int(cid)
            if cid_int not in existing_ids:
                cached_title = resolved_channel_titles.get(cid_int)
                user_channel_lists[user_id].append({
                    "chat_id": cid_int,
                    "title": cached_title if cached_title else f"Channel {idx} ({cid_int})",
                })
                existing_ids.add(cid_int)

        for item in user_channel_lists[user_id]:
            cid = int(item["chat_id"])
            if cid in resolved_channel_titles and resolved_channel_titles[cid]:
                item["title"] = resolved_channel_titles[cid]

    if user_id not in user_channels and user_channel_lists[user_id]:
        user_channels[user_id] = dict(user_channel_lists[user_id][0])
    elif user_id in user_channels and user_channels[user_id]:
        act_cid = int(user_channels[user_id]["chat_id"])
        if act_cid in resolved_channel_titles and resolved_channel_titles[act_cid]:
            user_channels[user_id]["title"] = resolved_channel_titles[act_cid]
    return user_channel_lists[user_id]


def save_user_channel_entry(user_id: int, chat_id: int, title: str | None = None, set_active: bool = True) -> dict:
    ch_list = ensure_user_channels_loaded(user_id)
    existing = None
    for item in ch_list:
        if int(item["chat_id"]) == int(chat_id):
            existing = item
            break

    clean_title = (title or "").strip()
    if clean_title:
        resolved_channel_titles[int(chat_id)] = clean_title
    elif int(chat_id) in resolved_channel_titles:
        clean_title = resolved_channel_titles[int(chat_id)]

    if existing:
        if clean_title:
            existing["title"] = clean_title
        entry = existing
    else:
        entry = {
            "chat_id": int(chat_id),
            "title": clean_title if clean_title else f"Channel ({chat_id})",
        }
        ch_list.append(entry)

    if set_active:
        user_channels[user_id] = dict(entry)
    return entry


def get_active_user_channel(user_id: int) -> dict | None:
    ensure_user_channels_loaded(user_id)
    active = user_channels.get(user_id)
    if active:
        cid = int(active["chat_id"])
        if cid in resolved_channel_titles and resolved_channel_titles[cid]:
            active["title"] = resolved_channel_titles[cid]
        return active
    ch_list = user_channel_lists.get(user_id) or []
    if ch_list:
        user_channels[user_id] = dict(ch_list[0])
        return user_channels[user_id]
    return None


def get_user_upload_delay(user_id: int) -> float:
    return float(user_upload_delays.get(user_id, 0.15))


def get_user_forward_tag(user_id: int) -> bool:
    return bool(user_forward_tags.get(user_id, True))


def queue_video_for_ok(
    user_id: int,
    file_id: str,
    api_type: str = "video",
    orig_caption: str = "",
    channel_edit: bool = False,
    msg_id: int | None = None,
    fallback_order_id: int = 0,
) -> int:
    queue = pending_edits.setdefault(user_id, {})
    if channel_edit and msg_id is not None:
        sort_key = int(msg_id)
        while sort_key in queue and queue[sort_key].get("file_id") != file_id:
            sort_key += 1
    else:
        base_num = int(fallback_order_id) if fallback_order_id else (int(msg_id) if msg_id is not None else 1)
        if base_num <= 0:
            base_num = len(queue) + 1
        sort_key = base_num
        while sort_key in queue:
            sort_key += 1

    queue[sort_key] = {
        "file_id": file_id,
        "api_type": api_type,
        "orig_caption": orig_caption or "",
        "channel_edit": bool(channel_edit),
        "msg_id": int(msg_id) if msg_id is not None else None,
    }
    return sort_key


def build_time_keyboard(current_delay: float) -> InlineKeyboardMarkup:
    presets = [1.2, 2, 2.5, 3]
    rows = []
    for val in presets:
        is_selected = abs(float(current_delay) - float(val)) < 1e-6
        label_txt = f"✅ {val}s" if is_selected else f"{val}s"
        rows.append([InlineKeyboardButton(label_txt, callback_data=f"set_time:{val}")])
    return InlineKeyboardMarkup(rows)


def build_channel_list_keyboard(user_id: int) -> InlineKeyboardMarkup:
    ch_list = ensure_user_channels_loaded(user_id)
    active = get_active_user_channel(user_id)
    active_id = active["chat_id"] if active else None
    rows = []
    for item in ch_list:
        cid = int(item["chat_id"])
        title = item.get("title") or f"Channel ({cid})"
        prefix = "✅ " if active_id is not None and int(active_id) == cid else ""
        rows.append([InlineKeyboardButton(f"{prefix}{title} [{cid}]", callback_data=f"set_ch:{cid}")])
    return InlineKeyboardMarkup(rows)


def get_user_mode(user_id: int) -> str:
    return user_modes.get(user_id, "both")


def build_mode_keyboard(current_mode: str) -> InlineKeyboardMarkup:
    def label(text: str, key: str) -> str:
        return f"✅ {text}" if current_mode == key else text

    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton(label("covar", "cover"), callback_data="set_mode:cover")],
            [InlineKeyboardButton(label("caption", "caption"), callback_data="set_mode:caption")],
            [InlineKeyboardButton(label("covar and caption", "both"), callback_data="set_mode:both")],
        ]
    )


async def delete_after_delay(client, chat_id: int, message_id: int, delay: int = 5):
    await asyncio.sleep(delay)
    try:
        await client.delete_messages(chat_id=chat_id, message_ids=message_id)
    except Exception:
        pass


def schedule_auto_delete(client, msg, delay: int = 5):
    if msg:
        asyncio.create_task(delete_after_delay(client, msg.chat.id, msg.id, delay))


def extract_video_own_cover_file_id(message) -> str | None:
    """
    ইউজার যে ভিডিওটি পাঠিয়েছে সেই ভিডিওর নিজস্ব cover বা thumbnail file_id বের করে।
    """
    vid = getattr(message, "video", None)
    if vid:
        # প্রথমে cover লিস্ট বা অবজেক্ট চেক করি
        cov = getattr(vid, "cover", None)
        if cov:
            if isinstance(cov, list) and len(cov) > 0:
                last_cov = cov[-1]
                fid = getattr(last_cov, "file_id", None)
                if fid:
                    return fid
            else:
                fid = getattr(cov, "file_id", None)
                if fid:
                    return fid

        # এরপর thumbs / thumbnail চেক করি
        thumbs = getattr(vid, "thumbs", None)
        if thumbs and isinstance(thumbs, list) and len(thumbs) > 0:
            last_th = thumbs[-1]
            fid = getattr(last_th, "file_id", None)
            if fid:
                return fid

        single_th = getattr(vid, "thumbnail", None)
        if single_th:
            fid = getattr(single_th, "file_id", None)
            if fid:
                return fid

    doc = getattr(message, "document", None)
    if doc:
        thumbs = getattr(doc, "thumbs", None)
        if thumbs and isinstance(thumbs, list) and len(thumbs) > 0:
            fid = getattr(thumbs[-1], "file_id", None)
            if fid:
                return fid
        single_th = getattr(doc, "thumbnail", None)
        if single_th:
            fid = getattr(single_th, "file_id", None)
            if fid:
                return fid

    return None


def extract_media_info(message):
    if message.video:
        return {
            "kind": "video",
            "api_type": "video",
            "file_id": message.video.file_id,
            "own_cover_file_id": extract_video_own_cover_file_id(message),
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
            "own_cover_file_id": extract_video_own_cover_file_id(message),
        }
    return None


def extract_photo_or_video_info(message):
    if getattr(message, "photo", None):
        return {
            "kind": "photo",
            "api_type": "photo",
            "file_id": message.photo.file_id,
        }
    media_info = extract_media_info(message)
    if media_info:
        return media_info
    return None


def parse_message_range(arg_text: str):
    cleaned = arg_text.strip()
    m_single = re.fullmatch(r"(\d+)", cleaned)
    if m_single:
        msg_id = int(m_single.group(1))
        return [msg_id] if msg_id > 0 else None

    m_range = re.fullmatch(r"(\d+)\s*-\s*(\d+)", cleaned)
    if m_range:
        start_id = int(m_range.group(1))
        end_id = int(m_range.group(2))
        if start_id <= 0 or end_id <= 0:
            return None
        if start_id > end_id:
            start_id, end_id = end_id, start_id
        if end_id - start_id > 200:
            return "TOO_LARGE"
        return list(range(start_id, end_id + 1))

    return None


def parse_season_numbers(raw_text: str) -> list[int]:
    """
    Season এর জন্য নাম্বার পার্স করে: যেমন 1 বা 1-5, বা 1,4,2,6-9
    """
    tokens = [t.strip() for t in re.split(r"[,\s]+", (raw_text or "").strip()) if t.strip()]
    result = []
    for tok in tokens:
        m_range = re.fullmatch(r"(\d+)\s*-\s*(\d+)", tok)
        if m_range:
            s = int(m_range.group(1))
            e = int(m_range.group(2))
            if s > 0 and e > 0:
                if s <= e:
                    for num in range(s, e + 1):
                        result.append(num)
                else:
                    for num in range(s, e - 1, -1):
                        result.append(num)
        elif re.fullmatch(r"\d+", tok):
            val = int(tok)
            if val > 0:
                result.append(val)
    return result


def build_create_post_text(image_name: str, genres: str, seasons_raw: str) -> str:
    clean_name = (image_name or "").strip()
    clean_gen = (genres or "").strip()
    season_nums = parse_season_numbers(seasons_raw)
    if not season_nums:
        season_nums = [1]

    season_lines = [
        f"<b>{html.escape(clean_name)} Season {str(s).zfill(2)}</b>"
        for s in season_nums
    ]
    quote_body = (
        f"<b>{html.escape(clean_name)} All Season List :-</b>\n\n"
        + "\n\n".join(season_lines)
        + "\n\n<b>Coming Soon...</b>"
    )

    top_block = (
        f"<b>{html.escape(clean_name)}</b>\n"
        f"<b>────────────────────</b>\n"
        f"<b>‣ Audio - Hindi Official</b>\n"
        f"<b>‣ Quality - 480p, 720p, 1080p</b>\n"
        f"<b>‣ Genres - {html.escape(clean_gen)}</b>\n"
        f"<b>────────────────────</b>"
    )
    quote_block = f"<blockquote expandable>{quote_body}</blockquote>"
    return f"{top_block}\n\n{quote_block}"


def format_bold_html(raw_text: str) -> str:
    stripped = (raw_text or "").strip()
    if not stripped:
        return ""
    if stripped.startswith("<b>") and stripped.endswith("</b>"):
        return stripped
    return f"<b>{html.escape(stripped)}</b>"


def render_dynamic_caption(template: str, video_index: int) -> str:
    re_pattern = re.compile(r"\[re\s*\((.*?)\)\]", re.IGNORECASE | re.DOTALL)
    re_matches = list(re_pattern.finditer(template))

    cycle_len = 1
    if re_matches:
        first_items = [x.strip() for x in re_matches[0].group(1).split(",") if x.strip()]
        if first_items:
            cycle_len = len(first_items)

    cycle_step = video_index // cycle_len

    def replace_re(match):
        items = [x.strip() for x in match.group(1).split(",") if x.strip()]
        if not items:
            return ""
        return items[video_index % len(items)]

    text = re_pattern.sub(replace_re, template)

    bracket_num_pattern = re.compile(r"\[(\d+)\]")
    first_num_match = bracket_num_pattern.search(text)
    first_num_val = None
    if first_num_match:
        first_num_val = int(first_num_match.group(1)) + cycle_step

    def replace_bracket_num(match):
        num_str = match.group(1)
        width = len(num_str)
        val = int(num_str) + cycle_step
        return str(val).zfill(width)

    text = bracket_num_pattern.sub(replace_bracket_num, text)

    paren_num_pattern = re.compile(r"\[\((\d+)\)\]")

    def replace_paren_num(match):
        num_str = match.group(1)
        width = len(num_str)
        val = int(num_str) + cycle_step
        return f"({str(val).zfill(width)})"

    text = paren_num_pattern.sub(replace_paren_num, text)

    end_pattern = re.compile(r"\[([^\[\]\(\)]+?)\s*\((\d+)\)\]")

    def replace_end(match):
        end_text = match.group(1).strip()
        target_num = int(match.group(2))
        if first_num_val is not None and first_num_val == target_num:
            return end_text
        return ""

    text = end_pattern.sub(replace_end, text)

    cleaned_lines = [re.sub(r" {2,}", " ", line).rstrip() for line in text.splitlines()]
    final_plain = "\n".join(cleaned_lines).strip()

    return format_bold_html(final_plain)


def _tg_session_post_sync(method: str, payload: dict) -> dict:
    try:
        resp = tg_session.post(f"{API_BASE}/{method}", json=payload, timeout=20)
        return resp.json()
    except Exception as e:
        return {"ok": False, "description": str(e)}


async def tg_session_post(method: str, payload: dict) -> dict:
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, _tg_session_post_sync, method, payload)


async def api_edit_message_caption_only(
    session: aiohttp.ClientSession,
    chat_id: int,
    message_id: int,
    caption: str = "",
    parse_mode: str | None = "HTML",
):
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "caption": caption,
    }
    if parse_mode:
        payload["parse_mode"] = parse_mode

    return await tg_session_post("editMessageCaption", payload)


async def api_edit_message_media_cover(
    session: aiohttp.ClientSession,
    chat_id: int,
    message_id: int,
    api_type: str,
    file_id: str,
    cover_file_id: str | None,
    caption: str = "",
    parse_mode: str | None = "HTML",
):
    media_obj = {
        "type": api_type,
        "media": file_id,
        "caption": caption,
    }
    if parse_mode:
        media_obj["parse_mode"] = parse_mode
    if cover_file_id and api_type == "video":
        media_obj["cover"] = cover_file_id

    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "media": media_obj,
    }
    return await tg_session_post("editMessageMedia", payload)


async def api_send_media(
    chat_id: int,
    api_type: str,
    file_id: str,
    cover_file_id: str | None = None,
    caption: str = "",
    parse_mode: str | None = "HTML",
):
    if api_type == "video":
        method = "sendVideo"
        payload = {
            "chat_id": chat_id,
            "video": file_id,
            "caption": caption,
            "supports_streaming": True,
        }
        if parse_mode:
            payload["parse_mode"] = parse_mode
        if cover_file_id:
            payload["cover"] = cover_file_id
    elif api_type == "photo":
        method = "sendPhoto"
        payload = {
            "chat_id": chat_id,
            "photo": file_id,
            "caption": caption,
        }
        if parse_mode:
            payload["parse_mode"] = parse_mode
    else:
        method = "sendDocument"
        payload = {
            "chat_id": chat_id,
            "document": file_id,
            "caption": caption,
        }
        if parse_mode:
            payload["parse_mode"] = parse_mode

    return await tg_session_post(method, payload)


def extract_retry_after(result: dict) -> int | None:
    if not isinstance(result, dict):
        return None
    params = result.get("parameters") or {}
    if params.get("retry_after") is not None:
        return int(params["retry_after"])
    desc = str(result.get("description") or "")
    m = re.search(r"retry after (\d+)", desc, re.IGNORECASE)
    if m:
        return int(m.group(1))
    return None


async def extract_cover_from_message_via_api(client, message) -> str | None:
    """
    Pyrogram মেসেজ অবজেক্ট বা Bot API থেকে ভিডিওর নিজস্ব cover/thumbnail file_id বের করে।
    """
    direct_cov = extract_video_own_cover_file_id(message)
    if direct_cov:
        return direct_cov

    # যদি Pyrogram অবজেক্টে cover না থাকে, তাহলে copyMessage / forwardMessage করে Bot API JSON রেসপন্স থেকে cover নেওয়া
    try:
        copy_res = await tg_session_post(
            "copyMessage",
            {
                "chat_id": message.chat.id,
                "from_chat_id": message.chat.id,
                "message_id": message.id,
            },
        )
        if isinstance(copy_res, dict) and copy_res.get("ok"):
            copied_msg_id = (copy_res.get("result") or {}).get("message_id")
            if copied_msg_id:
                try:
                    await tg_session_post(
                        "deleteMessage",
                        {"chat_id": message.chat.id, "message_id": copied_msg_id},
                    )
                except Exception:
                    pass
    except Exception:
        pass

    return None


async def send_video_own_cover(client, chat_id: int, message=None, own_cover_file_id: str | None = None) -> dict:
    """
    ইউজার যে ভিডিও পাঠিয়েছে সেই ভিডিওর নিজস্ব cover কপি করে ইউজারকে পাঠায়।
    """
    cov_id = own_cover_file_id
    if not cov_id and message is not None:
        cov_id = await extract_cover_from_message_via_api(client, message)

    if cov_id:
        res = await tg_session_post(
            "sendPhoto",
            {
                "chat_id": chat_id,
                "photo": cov_id,
            },
        )
        if res.get("ok"):
            return res
        # যদি photo হিসেবে না যায় তবে document হিসেবে পাঠানোর চেষ্টা
        return await tg_session_post(
            "sendDocument",
            {
                "chat_id": chat_id,
                "document": cov_id,
            },
        )

    return {"ok": False, "description": "এই ভিডিওতে কোনো Cover/Thumbnail পাওয়া যায়নি।"}


async def run_batch_with_retry(coro_factory, items: list, delay_sec: float = 0.05):
    """
    asyncio.gather ব্যবহার করে concurrent batch-এ রিকোয়েস্ট পাঠায় এবং FloodWait আসলে হ্যান্ডেল করে।
    """
    results = []
    batch_size = 5
    for i in range(0, len(items), batch_size):
        chunk = items[i : i + batch_size]
        tasks = [coro_factory(item) for item in chunk]
        chunk_res = await asyncio.gather(*tasks, return_exceptions=False)
        for item, res in zip(chunk, chunk_res):
            if isinstance(res, dict) and not res.get("ok"):
                retry_after = extract_retry_after(res)
                if retry_after is not None:
                    await asyncio.sleep(retry_after + 1)
                    res = await coro_factory(item)
            results.append((item, res))
        if delay_sec > 0 and i + batch_size < len(items):
            await asyncio.sleep(delay_sec)
    return results


# কোনো Channel বা Group-এ বটকে Admin করলে অটোমেটিক সেভ হয়ে যাবে
@app.on_chat_member_updated()
async def on_bot_chat_member_update(client, update):
    try:
        chat = getattr(update, "chat", None)
        new_member = getattr(update, "new_chat_member", None)
        if not chat or not new_member:
            return

        chat_type = getattr(chat, "type", None)
        if chat_type not in (ChatType.CHANNEL, ChatType.GROUP, ChatType.SUPERGROUP):
            return

        new_status = getattr(new_member, "status", None)
        if new_status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER):
            cid = int(chat.id)
            ctitle = (getattr(chat, "title", None) or f"Chat ({cid})").strip()
            resolved_channel_titles[cid] = ctitle

            target_users = set(user_channel_lists.keys())
            if ADMIN_ID is not None:
                target_users.add(int(ADMIN_ID))

            for uid in target_users:
                save_user_channel_entry(
                    user_id=uid,
                    chat_id=cid,
                    title=ctitle,
                    set_active=True,
                )

            if ADMIN_ID is not None:
                try:
                    await client.send_message(
                        chat_id=int(ADMIN_ID),
                        text=f"✅ বটকে Admin করায় নতুন চ্যানেল/গ্রুপ অটো সেভ হয়েছে:\n**{ctitle}** (`{cid}`)",
                    )
                except Exception:
                    pass
    except Exception as e:
        print(f"on_chat_member_updated error: {e}")


@app.on_message(filters.command("start") & filters.private)
async def cmd_start(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    await resolve_all_user_channel_titles(client, message.from_user.id)
    help_text = (
        "সব কমান্ডের তালিকা:\n\n"
        "/start - সব কমান্ড দেখাবে\n"
        "/thum - নতুন thumbnail বা cover ছবি সেভ করবে\n"
        "/view_thum - সেভ করা thumbnail ছবি দেখাবে এবং delete বাটন দেবে\n"
        "/add - চ্যানেল যুক্ত করবে (ফরোয়ার্ড করে অথবা সরাসরি ID দিয়ে)\n"
        "/list - সেভ করা সকল চ্যানেল দেখাবে এবং বাটন দিয়ে সিলেক্ট করতে দেবে\n"
        "/time - upload/edit delay টাইম সেট করবে (যেমন: /time 1.2, 2, 2.5, 3)\n"
        "/cap - কাস্টম caption সেভ করবে\n"
        "/cap_view - সেভ করা caption দেখাবে এবং delete বাটন দেবে\n"
        "/mode - covar, caption, অথবা covar and caption মোড নির্বাচন করবে\n"
        "/cover - ভিডিওর নিজস্ব cover পাঠানোর মোড অন/অফ করবে (/cover on / /cover off)\n"
        "/change_media - সেভ চ্যানেলের পোস্টের মিডিয়া/কভার/ক্যাপশন পরিবর্তন করবে\n"
        "/create_post - নতুন পোস্ট টেমপ্লেট তৈরি করবে\n"
        "/send on অথবা /send off - forward tag চালু/বন্ধ করবে\n"
        "/send 19 অথবা /send 2-20 - সিলেক্ট করা চ্যানেলের মেসেজ বা রেঞ্জ পাঠাবে\n"
        "ok - জমা রাখা ভিডিওগুলো ছোট ID থেকে পাঠাবে/edit করবে"
    )
    await message.reply_text(help_text, parse_mode=None)


@app.on_message(filters.command("cover") & filters.private)
async def cmd_cover(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    parts = (message.text or "").split(maxsplit=1)

    if len(parts) < 2 or not parts[1].strip():
        if user_id in cover_instant_mode or user_id in cover_batch_mode:
            cover_instant_mode.discard(user_id)
            cover_batch_mode.discard(user_id)
            cover_batch_queue.pop(user_id, None)
            cover_batch_counter.pop(user_id, None)
            await message.reply_text("Cover mode **OFF** করা হয়েছে।")
        else:
            cover_instant_mode.add(user_id)
            cover_batch_mode.discard(user_id)
            await message.reply_text(
                "Cover instant mode **ON** করা হয়েছে। এখন যেকোনো ভিডিও send বা forward করলে সাথে সাথে সেই ভিডিওর নিজস্ব cover image পাঠাবে। আবার `/cover` দিলে এটি OFF হবে।"
            )
        return

    sub_cmd = parts[1].strip().lower()
    if sub_cmd == "on":
        cover_batch_mode.add(user_id)
        cover_instant_mode.discard(user_id)
        cover_batch_queue[user_id] = []
        cover_batch_counter[user_id] = 0
        await message.reply_text(
            "Cover batch mode **ON** করা হয়েছে। একাধিক ভিডিও পাঠান/ফরোয়ার্ড করুন (ID সিরিয়াল অনুযায়ী সেভ হবে), তারপর **`ok`** লিখলে ১ নম্বর থেকে শেষ পর্যন্ত ভিডিওগুলোর cover image পাঠাবে। (আবার `/cover` বা `/cover off` না দেওয়া পর্যন্ত মোড চালু থাকবে)"
        )
        return

    if sub_cmd == "off":
        cover_batch_mode.discard(user_id)
        cover_batch_queue.pop(user_id, None)
        cover_batch_counter.pop(user_id, None)
        cover_instant_mode.add(user_id)
        await message.reply_text(
            "Cover batch mode **OFF** করা হয়েছে। এখন ভিডিও পাঠানোর সাথে সাথে সেই ভিডিওর cover image পাঠাবে। (সম্পূর্ণ বন্ধ করতে `/cover` দিন)"
        )
        return

    await message.reply_text("ব্যবহার করুন: `/cover`, `/cover on`, অথবা `/cover off`")


@app.on_message(filters.command("change_media") & filters.private)
async def cmd_change_media(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id

    if user_id in change_media_state:
        del change_media_state[user_id]
        await message.reply_text("Change media mode **OFF** করা হয়েছে।")
        return

    await resolve_all_user_channel_titles(client, user_id)
    saved_ch = get_active_user_channel(user_id)
    if not saved_ch:
        await message.reply_text(
            "আগে `/add` দিয়ে বা ENV-এ `CHANNEL_ID` দিয়ে একটি চ্যানেল যুক্ত করুন, তারপর `/change_media` দিন।"
        )
        return

    change_media_state[user_id] = {
        "stage": "posts",
        "posts": [],
        "media": [],
        "counter": 0,
    }
    await message.reply_text(
        f"Change media mode **ON** হয়েছে। **{saved_ch['title']}** চ্যানেল থেকে পোস্ট মেসেজগুলো **Forward** করুন।\n"
        "একাধিক মেসেজ forward করা যাবে (ID সিরিয়াল অনুযায়ী সেভ হবে)। শেষ হলে **`ok`** লিখুন। (বন্ধ করতে আবার `/change_media` দিন)"
    )


@app.on_message(filters.command("create_post") & filters.private)
async def cmd_create_post(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id

    if user_id in create_post_state:
        del create_post_state[user_id]
        await message.reply_text("Create post mode **OFF** (বন্ধ) করা হয়েছে।")
        return

    create_post_state[user_id] = {
        "step": "image",
        "photo_id": None,
        "name": None,
        "gen": None,
    }
    await message.reply_text(
        "Create post mode **ON** করা হয়েছে।\nদয়া করে পোস্টের জন্য একটি **Image** পাঠান। (আবার `/create_post` না দেওয়া পর্যন্ত মোড চালু থাকবে)"
    )


@app.on_message(filters.command("time") & filters.private)
async def cmd_time(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        current_delay = get_user_upload_delay(user_id)
        await message.reply_text(
            f"বর্তমান upload time delay: `{current_delay}`s\n"
            "নিচের বাটন থেকে সিলেক্ট করুন অথবা লিখুন: `/time 1.2`, `/time 2`, `/time 2.5`, `/time 3`",
            reply_markup=build_time_keyboard(current_delay),
        )
        return

    raw_arg = parts[1].strip()
    matched_nums = re.findall(r"\d+(?:\.\d+)?", raw_arg)
    if not matched_nums:
        await message.reply_text("সঠিক সময় দিন। যেমন: `/time 1.2`, `/time 2`, `/time 2.5`, `/time 3`")
        return

    first_val = float(matched_nums[0])
    if first_val < 0 or first_val > 60:
        await message.reply_text("সময় `0` থেকে `60` সেকেন্ডের মধ্যে দিন।")
        return

    clean_val = int(first_val) if first_val.is_integer() else first_val
    user_upload_delays[user_id] = float(clean_val)

    parsed_list = []
    for n_str in matched_nums:
        fv = float(n_str)
        if 0 <= fv <= 60:
            parsed_list.append(int(fv) if fv.is_integer() else fv)

    if len(parsed_list) > 1:
        rows = [
            [
                InlineKeyboardButton(
                    f"✅ {v}s" if abs(float(v) - float(clean_val)) < 1e-6 else f"{v}s",
                    callback_data=f"set_time:{v}",
                )
            ]
            for v in parsed_list
        ]
        kb = InlineKeyboardMarkup(rows)
    else:
        kb = build_time_keyboard(float(clean_val))

    await message.reply_text(
        f"Upload time সেট হয়েছে: `{clean_val}`s",
        reply_markup=kb,
    )


@app.on_callback_query(filters.regex("^set_time:(.+)$"))
async def cb_set_time(client, callback_query):
    if not is_admin(callback_query.from_user.id if callback_query.from_user else None):
        await callback_query.answer("Access denied.", show_alert=True)
        return
    user_id = callback_query.from_user.id
    raw_val = callback_query.data.split(":", 1)[1].strip()
    try:
        val = float(raw_val)
        if val < 0 or val > 60:
            await callback_query.answer("Invalid time range.", show_alert=True)
            return
    except ValueError:
        await callback_query.answer("Invalid time value.", show_alert=True)
        return

    clean_val = int(val) if val.is_integer() else val
    user_upload_delays[user_id] = float(clean_val)

    try:
        await callback_query.message.edit_text(
            f"Upload time সেট হয়েছে: `{clean_val}`s",
            reply_markup=build_time_keyboard(float(clean_val)),
        )
    except Exception:
        pass
    await callback_query.answer(f"Upload time set: {clean_val}s")


@app.on_message(filters.command("list") & filters.private)
async def cmd_list_channels(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    await resolve_all_user_channel_titles(client, user_id, force_refresh=True)
    ch_list = ensure_user_channels_loaded(user_id)
    if not ch_list:
        await message.reply_text(
            "কোনো চ্যানেল সেভ করা নেই। ENV-এ `CHANNEL_ID` দিন অথবা `/add` দিয়ে চ্যানেল যুক্ত করুন।"
        )
        return

    active = get_active_user_channel(user_id)
    active_txt = f"**{active['title']}** (`{active['chat_id']}`)" if active else "নেই"
    lines = ["**সেভ করা চ্যানেলসমূহ:**\n"]
    for idx, item in enumerate(ch_list, start=1):
        mark = "✅ " if active and int(active["chat_id"]) == int(item["chat_id"]) else ""
        lines.append(f"{idx}. {mark}**{item['title']}** — `{item['chat_id']}`")
    lines.append(f"\nবর্তমান সিলেক্টেড চ্যানেল: {active_txt}")
    lines.append("নিচের বাটন থেকে যেকোনো একটি চ্যানেল সিলেক্ট করুন:")

    await message.reply_text(
        "\n".join(lines),
        reply_markup=build_channel_list_keyboard(user_id),
    )


@app.on_callback_query(filters.regex("^set_ch:(-?\\d+)$"))
async def cb_set_channel(client, callback_query):
    if not is_admin(callback_query.from_user.id if callback_query.from_user else None):
        await callback_query.answer("Access denied.", show_alert=True)
        return
    user_id = callback_query.from_user.id
    await resolve_all_user_channel_titles(client, user_id)
    target_id = int(callback_query.data.split(":", 1)[1])
    ch_list = ensure_user_channels_loaded(user_id)
    matched = next((item for item in ch_list if int(item["chat_id"]) == target_id), None)
    if not matched:
        await callback_query.answer("Channel not found in list.", show_alert=True)
        return

    user_channels[user_id] = dict(matched)
    active_txt = f"**{matched['title']}** (`{matched['chat_id']}`)"
    lines = ["**সেভ করা চ্যানেলসমূহ:**\n"]
    for idx, item in enumerate(ch_list, start=1):
        mark = "✅ " if int(item["chat_id"]) == target_id else ""
        lines.append(f"{idx}. {mark}**{item['title']}** — `{item['chat_id']}`")
    lines.append(f"\nবর্তমান সিলেক্টেড চ্যানেল: {active_txt}")
    lines.append("নিচের বাটন থেকে যেকোনো একটি চ্যানেল সিলেক্ট করুন:")

    try:
        await callback_query.message.edit_text(
            "\n".join(lines),
            reply_markup=build_channel_list_keyboard(user_id),
        )
    except Exception:
        pass
    await callback_query.answer(f"Selected: {matched['title']}")


@app.on_message(filters.command("thum") & filters.private)
async def cmd_thum(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    waiting_for_channel.discard(user_id)
    waiting_for_caption.discard(user_id)
    waiting_for_thumb.add(user_id)
    await message.reply_text(
        "দয়া করে Cover/Thumbnail-এর জন্য একটি ছবি **send** অথবা **forward** করুন।"
    )


@app.on_message(filters.command("view_thum") & filters.private)
async def cmd_view_thum(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    thumb_id = user_cover_file_ids.get(user_id)
    if not thumb_id:
        await message.reply_text("বর্তমানে কোনো Thumbnail/Cover ছবি সেভ করা নেই। `/thum` দিয়ে ছবি সেট করুন।")
        return

    kb = InlineKeyboardMarkup(
        [[InlineKeyboardButton("🗑 Delete Thumbnail", callback_data="del_thumb")]]
    )
    await client.send_photo(
        chat_id=message.chat.id,
        photo=thumb_id,
        caption="সেভ করা Thumbnail/Cover ছবি:",
        reply_markup=kb,
    )


@app.on_callback_query(filters.regex("^del_thumb$"))
async def cb_delete_thumb(client, callback_query):
    if not is_admin(callback_query.from_user.id if callback_query.from_user else None):
        await callback_query.answer("Access denied.", show_alert=True)
        return
    user_id = callback_query.from_user.id
    if user_id in user_cover_file_ids:
        del user_cover_file_ids[user_id]
        try:
            await callback_query.message.delete()
        except Exception:
            await callback_query.message.edit_caption("সেভ করা Thumbnail ডিলিট করা হয়েছে।")
        await callback_query.answer("Thumbnail deleted!")
    else:
        await callback_query.answer("কোনো Thumbnail সেভ করা নেই।", show_alert=True)


@app.on_message(filters.command("mode") & filters.private)
async def cmd_mode(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    current_mode = get_user_mode(user_id)
    await message.reply_text(
        "নিচের বাটন থেকে যেকোনো একটি মোড সিলেক্ট করুন:",
        reply_markup=build_mode_keyboard(current_mode),
    )


@app.on_callback_query(filters.regex("^set_mode:(cover|caption|both)$"))
async def cb_set_mode(client, callback_query):
    if not is_admin(callback_query.from_user.id if callback_query.from_user else None):
        await callback_query.answer("Access denied.", show_alert=True)
        return
    user_id = callback_query.from_user.id
    selected = callback_query.data.split(":", 1)[1]
    user_modes[user_id] = selected
    await callback_query.message.edit_reply_markup(
        reply_markup=build_mode_keyboard(selected)
    )
    mode_names = {
        "cover": "covar",
        "caption": "caption",
        "both": "covar and caption",
    }
    await callback_query.answer(f"Mode set: {mode_names[selected]}")


@app.on_message(filters.command("add") & filters.private)
async def cmd_add_channel(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    await resolve_all_user_channel_titles(client, user_id)
    waiting_for_thumb.discard(user_id)
    waiting_for_caption.discard(user_id)

    # সরাসরি /add -1001234567890 দিলে ম্যানুয়ালি সেভ করবে
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) > 1 and parts[1].strip():
        raw_id_str = parts[1].strip()
        m_id = re.search(r"-?\d+", raw_id_str)
        if m_id:
            target_cid = int(m_id.group(0))
            fetched_title = await fetch_channel_title_from_api(client, target_cid, force_refresh=True)
            saved_entry = save_user_channel_entry(
                user_id=user_id,
                chat_id=target_cid,
                title=fetched_title or f"Channel ({target_cid})",
                set_active=True,
            )
            waiting_for_channel.discard(user_id)
            await message.reply_text(
                f"চ্যানেল ম্যানুয়ালি সেভ হয়েছে: **{saved_entry['title']}** (`{saved_entry['chat_id']}`)"
            )
            return

    waiting_for_channel.add(user_id)
    await message.reply_text(
        "দয়া করে আপনার **Channel** থেকে যেকোনো একটি মেসেজ, ইমেজ, ভিডিও বা ফাইল এই চ্যাটে **Forward** করুন অথবা সরাসরি চ্যানেল **ID** লিখুন (যেমন: `-1001234567890`)।"
    )


@app.on_message(filters.command("cap") & filters.private)
async def cmd_cap(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    waiting_for_thumb.discard(user_id)
    waiting_for_channel.discard(user_id)
    waiting_for_caption.add(user_id)
    await message.reply_text(
        "দয়া করে আপনার কাস্টম **Caption** টেমপ্লেটটি পাঠান।\n\n"
        "উদাহরণ:\n"
        "`✔️ Episode - [01] (S01) [End (12)]\n"
        "🎧 Language - Hindi (OFFICIAL)\n"
        "⚡ Quality : [re (480p, 720p, 1080p)]`"
    )


@app.on_message(filters.command("cap_view") & filters.private)
async def cmd_cap_view(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    cap_data = user_captions.get(user_id)
    if not cap_data:
        await message.reply_text("বর্তমানে কোনো Caption সেভ করা নেই। `/cap` দিয়ে নতুন Caption সেট করুন।")
        return

    preview = render_dynamic_caption(cap_data["template"], cap_data["index"])
    kb = InlineKeyboardMarkup(
        [[InlineKeyboardButton("🗑 Delete Caption", callback_data="del_caption")]]
    )
    await message.reply_text(
        f"**সেভ করা Caption টেমপ্লেট:**\n`{cap_data['template']}`\n\n"
        f"**পরবর্তী ভিডিওর প্রিভিউ (Index #{cap_data['index'] + 1}):**\n{preview}",
        reply_markup=kb,
    )


@app.on_callback_query(filters.regex("^del_caption$"))
async def cb_delete_caption(client, callback_query):
    if not is_admin(callback_query.from_user.id if callback_query.from_user else None):
        await callback_query.answer("Access denied.", show_alert=True)
        return
    user_id = callback_query.from_user.id
    if user_id in user_captions:
        del user_captions[user_id]
        await callback_query.message.edit_text("সেভ করা Caption ডিলিট করা হয়েছে। এখন শুধু Thumbnail/Cover পরিবর্তন হবে।")
        await callback_query.answer("Caption deleted!")
    else:
        await callback_query.answer("কোনো Caption সেভ করা নেই।", show_alert=True)


@app.on_message(filters.command("send") & filters.private)
async def cmd_send_channel_msg(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    await resolve_all_user_channel_titles(client, user_id)

    parts = (message.text or "").split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        tag_status = "ON (forward tag সহ)" if get_user_forward_tag(user_id) else "OFF (forward tag ছাড়া)"
        await message.reply_text(
            f"বর্তমান forward tag স্ট্যাটাস: **{tag_status}**\n\n"
            "ব্যবহারের নিয়ম:\n"
            "• `/send off` — forward tag ছাড়া মেসেজ পাঠাবে\n"
            "• `/send on` — forward tag সহ মেসেজ পাঠাবে\n"
            "• `/send 19` — সিলেক্ট করা চ্যানেলের ১৯ নম্বর মেসেজ পাঠাবে\n"
            "• `/send 2-20` — সিলেক্ট করা চ্যানেলের ২ থেকে ২০ নম্বর মেসেজ পাঠাবে"
        )
        return

    arg_raw = parts[1].strip()
    arg_lower = arg_raw.lower()
    if arg_lower == "off":
        user_forward_tags[user_id] = False
        await message.reply_text("Forward tag **OFF** করা হয়েছে। এখন `/send` দিলে forward tag ছাড়া মেসেজ যাবে।")
        return
    if arg_lower == "on":
        user_forward_tags[user_id] = True
        await message.reply_text("Forward tag **ON** করা হয়েছে। এখন `/send` দিলে forward tag সহ মেসেজ যাবে।")
        return

    saved_ch = get_active_user_channel(user_id)
    if not saved_ch:
        await message.reply_text(
            "আগে `/add` দিয়ে বা ENV-এ `CHANNEL_ID` দিয়ে একটি চ্যানেল যুক্ত করুন, তারপর `/send 19` অথবা `/send 2-20` দিন।"
        )
        return

    parsed = parse_message_range(arg_raw)
    if parsed is None:
        await message.reply_text("সঠিক Message ID বা রেঞ্জ দিন। যেমন: `/send 19` অথবা `/send 2-20` (অথবা `/send off` / `/send on`)")
        return
    if parsed == "TOO_LARGE":
        await message.reply_text("একবারে সর্বোচ্চ ২০০টি মেসেজের রেঞ্জ দেওয়া যাবে।")
        return

    channel_id = int(saved_ch["chat_id"])
    channel_title = saved_ch["title"]
    forward_tag_enabled = get_user_forward_tag(user_id)
    tag_label = "forward tag সহ" if forward_tag_enabled else "forward tag ছাড়া"

    status_msg = await message.reply_text(
        f"**{channel_title}** (`{channel_id}`) চ্যানেল থেকে `{arg_raw}` মেসেজ ({tag_label}) পাঠানো হচ্ছে..."
    )

    forwarded_count = 0
    for msg_id in parsed:
        while True:
            try:
                if forward_tag_enabled:
                    await client.forward_messages(
                        chat_id=message.chat.id,
                        from_chat_id=channel_id,
                        message_ids=msg_id,
                    )
                else:
                    await client.copy_message(
                        chat_id=message.chat.id,
                        from_chat_id=channel_id,
                        message_id=msg_id,
                    )
                forwarded_count += 1
                await asyncio.sleep(0.25)
                break
            except FloodWait as e:
                await asyncio.sleep(int(e.value) + 1)
            except RPCError:
                break

    await status_msg.edit_text(
        f"সম্পন্ন হয়েছে! **{channel_title}** থেকে মোট `{forwarded_count}`টি মেসেজ ({tag_label}) পাঠানো হয়েছে।"
    )


@app.on_message(filters.photo & filters.private)
async def handle_photo(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    origin_chat, _ = extract_forward_origin_info(message)
    if origin_chat and getattr(origin_chat, "type", None) == ChatType.CHANNEL and user_id in waiting_for_channel:
        saved_entry = save_user_channel_entry(
            user_id=user_id,
            chat_id=origin_chat.id,
            title=getattr(origin_chat, "title", None) or "Channel",
            set_active=True,
        )
        waiting_for_channel.discard(user_id)
        await message.reply_text(
            f"চ্যানেল সেভ হয়েছে (ইমেজ ফরোয়ার্ড থেকে): **{saved_entry['title']}** (`{saved_entry['chat_id']}`)"
        )
        return

    # /create_post ইমেজ ধাপ
    cp = create_post_state.get(user_id)
    if cp and cp.get("step") == "image":
        cp["photo_id"] = message.photo.file_id
        cp["step"] = "name"
        await message.reply_text("ইমেজ সেভ হয়েছে! এখন **Image Name** দিন:")
        return

    # /change_media মিডিয়া লিস্ট (২ নম্বর লিস্ট)
    cm = change_media_state.get(user_id)
    if cm and cm.get("stage") == "media":
        cm["counter"] += 1
        cm["media"].append({
            "order": cm["counter"],
            "api_type": "photo",
            "file_id": message.photo.file_id,
            "orig_caption": message.caption or "",
            "source_chat_id": message.chat.id,
            "source_msg_id": message.id,
        })
        info_msg = await message.reply_text(
            f"ইমেজ সেভ হয়েছে (Serial: `{cm['counter']}`)। মোট মিডিয়া: `{len(cm['media'])}`টি। শেষ হলে **`ok`** লিখুন।"
        )
        schedule_auto_delete(client, info_msg, delay=5)
        return

    if user_id in waiting_for_thumb or user_id not in user_cover_file_ids:
        user_cover_file_ids[user_id] = message.photo.file_id
        waiting_for_thumb.discard(user_id)
        await message.reply_text(
            "Cover ছবি সেভ হয়েছে!\n"
            "• ভিডিওগুলো পাঠান/forward করুন (সব সেভ হবে), তারপর **`ok`** লিখলে ছোট ID থেকে পাঠানো/এডিট শুরু হবে।"
        )
    else:
        await message.reply_text("নতুন ছবি সেট করতে চাইলে আগে `/thum` কমান্ড দিন।")


@app.on_message(filters.forwarded & filters.private)
async def handle_forwarded(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    origin_chat, origin_msg_id = extract_forward_origin_info(message)

    if origin_chat and getattr(origin_chat, "type", None) == ChatType.CHANNEL and getattr(origin_chat, "title", None):
        resolved_channel_titles[int(origin_chat.id)] = str(origin_chat.title).strip()

    if user_id in waiting_for_channel:
        if not origin_chat or getattr(origin_chat, "type", None) != ChatType.CHANNEL:
            await message.reply_text(
                "দয়া করে একটি **Channel** থেকে মেসেজ, ইমেজ, ভিডিও বা ফাইল forward করুন অথবা চ্যানেল ID লিখুন।"
            )
            return
        saved_entry = save_user_channel_entry(
            user_id=user_id,
            chat_id=origin_chat.id,
            title=getattr(origin_chat, "title", None) or "Channel",
            set_active=True,
        )
        waiting_for_channel.discard(user_id)
        await message.reply_text(
            f"চ্যানেল সেভ হয়েছে: **{saved_entry['title']}** (`{saved_entry['chat_id']}`)"
        )
        return

    # /change_media ফরোয়ার্ড হ্যান্ডলিং
    cm = change_media_state.get(user_id)
    if cm:
        if cm.get("stage") == "posts":
            saved_ch = get_active_user_channel(user_id)
            post_chat_id = int(origin_chat.id) if origin_chat else (int(saved_ch["chat_id"]) if saved_ch else None)
            post_msg_id = int(origin_msg_id) if origin_msg_id else int(getattr(message, "id", 0) or 0)
            has_media_now = bool(getattr(message, "photo", None) or getattr(message, "video", None) or getattr(message, "document", None))
            cm["counter"] += 1
            cm["posts"].append({
                "serial": cm["counter"],
                "chat_id": post_chat_id,
                "msg_id": post_msg_id,
                "has_media": has_media_now,
                "orig_caption": message.caption or message.text or "",
            })
            info_msg = await message.reply_text(
                f"চ্যানেল পোস্ট সেভ হয়েছে (Serial: `{cm['counter']}`, Msg ID: `{post_msg_id}`)। মোট পোস্ট: `{len(cm['posts'])}`টি। শেষ হলে **`ok`** লিখুন।"
            )
            schedule_auto_delete(client, info_msg, delay=5)
            return

        if cm.get("stage") == "media":
            p_or_v = extract_photo_or_video_info(message)
            if p_or_v and p_or_v.get("kind") != "document":
                cm["counter"] += 1
                cm["media"].append({
                    "order": cm["counter"],
                    "api_type": p_or_v["api_type"],
                    "file_id": p_or_v["file_id"],
                    "orig_caption": message.caption or "",
                    "source_chat_id": message.chat.id,
                    "source_msg_id": message.id,
                })
                info_msg = await message.reply_text(
                    f"মিডিয়া সেভ হয়েছে (Serial: `{cm['counter']}`)। মোট মিডিয়া: `{len(cm['media'])}`টি। শেষ হলে **`ok`** লিখুন।"
                )
                schedule_auto_delete(client, info_msg, delay=5)
                return

    info = extract_media_info(message)
    if not info:
        return

    if info["kind"] == "document":
        await message.reply_text(
            "সাধারণ `document`/file টাইপের ক্ষেত্রে Bot API-তে `cover` কাজ করে না—ভিডিও বা `.mp4`/`.mkv` ভিডিও ফাইল পাঠান।"
        )
        return

    # /cover instant mode চালু থাকলে সাথে সাথে ইউজারের পাঠানো ভিডিওর নিজস্ব cover পাঠাবে (অটো অফ হবে না)
    if user_id in cover_instant_mode:
        res = await send_video_own_cover(
            client=client,
            chat_id=message.chat.id,
            message=message,
            own_cover_file_id=info.get("own_cover_file_id"),
        )
        if not res.get("ok"):
            await message.reply_text(res.get("description", "এই ভিডিওতে কোনো Cover পাওয়া যায়নি।"))
        return

    # /cover on (batch mode) চালু থাকলে সিরিয়াল অনুযায়ী সেভ করবে (অটো অফ হবে না)
    if user_id in cover_batch_mode:
        cover_batch_counter[user_id] = cover_batch_counter.get(user_id, 0) + 1
        seq_num = cover_batch_counter[user_id]
        cover_batch_queue.setdefault(user_id, []).append({
            "order": seq_num,
            "file_id": info["file_id"],
            "cover_file_id": info.get("own_cover_file_id"),
            "kind": info["kind"],
            "chat_id": message.chat.id,
            "msg_id": message.id,
        })
        info_msg = await message.reply_text(
            f"Cover batch-এ ভিডিও সেভ হয়েছে (Serial: `{seq_num}`)। মোট: `{len(cover_batch_queue[user_id])}`টি। শেষ হলে **`ok`** লিখুন।"
        )
        schedule_auto_delete(client, info_msg, delay=5)
        return

    # Forward video-ও send video-এর মতো করে file_id save করবে যাতে একাধিক চ্যানেল থাকলেও সিরিয়াল ঠিক থাকে
    seq_order = (len(pending_edits.get(user_id, {})) + 1)
    sort_key = queue_video_for_ok(
        user_id=user_id,
        file_id=info["file_id"],
        api_type="video",
        orig_caption=message.caption or "",
        channel_edit=False,
        msg_id=None,
        fallback_order_id=seq_order,
    )
    queue = pending_edits.get(user_id, {})
    id_label = f"Queue ID: `{sort_key}`"
    info_msg = await message.reply_text(
        f"ভিডিও সেভ হয়েছে ({id_label})। মোট জমা: `{len(queue)}`টি।\n"
        "সব ভিডিও পাঠানো শেষ হলে **`ok`** লিখুন (ছোট ID থেকে পাঠানো/এডিট শুরু হবে)।"
    )
    schedule_auto_delete(client, info_msg, delay=5)


@app.on_message(
    filters.text
    & filters.private
    & ~filters.forwarded
    & ~filters.command(["start", "thum", "view_thum", "mode", "add", "list", "time", "cap", "cap_view", "send", "cover", "change_media", "create_post"])
)
async def handle_text_inputs(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    text_val = (message.text or "").strip()

    # ম্যানুয়াল চ্যানেল ID ইনপুট হ্যান্ডলিং (/add দেওয়ার পর সরাসরি ID দিলে)
    if user_id in waiting_for_channel:
        m_id = re.fullmatch(r"-?\d+", text_val)
        if m_id:
            target_cid = int(m_id.group(0))
            fetched_title = await fetch_channel_title_from_api(client, target_cid, force_refresh=True)
            saved_entry = save_user_channel_entry(
                user_id=user_id,
                chat_id=target_cid,
                title=fetched_title or f"Channel ({target_cid})",
                set_active=True,
            )
            waiting_for_channel.discard(user_id)
            await message.reply_text(
                f"চ্যানেল ম্যানুয়ালি সেভ হয়েছে: **{saved_entry['title']}** (`{saved_entry['chat_id']}`)"
            )
            return

    # /create_post ধাপসমূহ (কমান্ড দিয়ে অফ না করা পর্যন্ত মোড চালু থাকবে)
    cp = create_post_state.get(user_id)
    if cp:
        step = cp.get("step")
        if step == "image":
            await message.reply_text("দয়া করে একটি **Image** পাঠান। (বন্ধ করতে `/create_post` দিন)")
            return
        if step == "name":
            if not text_val:
                await message.reply_text("সঠিক **Image Name** দিন:")
                return
            cp["name"] = text_val
            cp["step"] = "gen"
            await message.reply_text("এখন **Genres** (gen) দিন:")
            return
        if step == "gen":
            if not text_val:
                await message.reply_text("সঠিক **Genres** দিন:")
                return
            cp["gen"] = text_val
            cp["step"] = "seasons"
            await message.reply_text("কত **Season** লাগবে তা দিন (যেমন: `1`, `1-5`, অথবা `1,4,2,6-9`):")
            return
        if step == "seasons":
            if not text_val:
                await message.reply_text("সঠিক **Season** নম্বর বা রেঞ্জ দিন:")
                return
            post_html = build_create_post_text(
                image_name=cp["name"] or "",
                genres=cp["gen"] or "",
                seasons_raw=text_val,
            )
            photo_id = cp.get("photo_id")
            # অটো অফ না করে পরের পোস্টের জন্য রিসেট রাখা
            create_post_state[user_id] = {
                "step": "image",
                "photo_id": None,
                "name": None,
                "gen": None,
            }
            if photo_id:
                await tg_session_post(
                    "sendPhoto",
                    {
                        "chat_id": message.chat.id,
                        "photo": photo_id,
                        "caption": post_html,
                        "parse_mode": "HTML",
                    },
                )
            else:
                await tg_session_post(
                    "sendMessage",
                    {
                        "chat_id": message.chat.id,
                        "text": post_html,
                        "parse_mode": "HTML",
                    },
                )
            return

    if user_id in waiting_for_caption:
        user_captions[user_id] = {
            "template": message.text,
            "index": 0,
        }
        waiting_for_caption.discard(user_id)
        preview = render_dynamic_caption(message.text, 0)
        await message.reply_text(
            f"Caption সেভ হয়েছে!\n\n**১ম ভিডিওর প্রিভিউ:**\n{preview}"
        )
        return

    text_lower = text_val.lower()
    ok_variants = ("ok", "ok thum", "ok cap", "ok thum and cap", "ok cap and thum")

    if text_lower in ok_variants:
        # /change_media হ্যান্ডলিং (অটো অফ হবে না, কমান্ড দিয়ে অফ না করা পর্যন্ত চলবে)
        cm = change_media_state.get(user_id)
        if cm:
            if cm.get("stage") == "posts":
                if not cm.get("posts"):
                    await message.reply_text("আগে চ্যানেল থেকে অন্তত একটি পোস্ট মেসেজ forward করুন।")
                    return
                cm["stage"] = "media"
                cm["media"] = []
                cm["counter"] = 0
                await message.reply_text(
                    f"মোট `{len(cm['posts'])}`টি চ্যানেল পোস্ট সেভ হয়েছে।\n"
                    "এখন নতুন **Image** বা **Video** পাঠান/forward করুন (একাধিক দেওয়া যাবে, সিরিয়াল অনুযায়ী সেভ হবে)।\n"
                    "শেষ হলে **`ok`**, **`ok thum`**, **`ok cap`**, অথবা **`ok thum and cap`** লিখুন।"
                )
                return

            if cm.get("stage") == "media":
                posts_list = sorted(cm.get("posts") or [], key=lambda x: x["serial"])
                media_list = sorted(cm.get("media") or [], key=lambda x: x["order"])
                saved_ch = get_active_user_channel(user_id)
                active_cover = user_cover_file_ids.get(user_id)
                cap_data = user_captions.get(user_id)

                do_thum = text_lower in ("ok thum", "ok thum and cap", "ok cap and thum")
                do_cap = text_lower in ("ok cap", "ok thum and cap", "ok cap and thum")

                if do_thum and not active_cover:
                    await message.reply_text("Cover পরিবর্তন করতে আগে `/thum` দিয়ে ছবি সেট করুন।")
                    return
                if do_cap and not cap_data:
                    await message.reply_text("Caption পরিবর্তন করতে আগে `/cap` দিয়ে Caption সেট করুন।")
                    return

                # অটো অফ না করে পরের ব্যাচের জন্য stage রিসেট করা
                change_media_state[user_id] = {
                    "stage": "posts",
                    "posts": [],
                    "media": [],
                    "counter": 0,
                }
                status_msg = await message.reply_text(
                    f"চ্যানেল পোস্ট এডিট শুরু হচ্ছে: `{len(posts_list)}`টি পোস্ট..."
                )

                updated_ok = 0
                async with aiohttp.ClientSession() as session:
                    for idx, post_item in enumerate(posts_list):
                        target_chat_id = post_item.get("chat_id") or (int(saved_ch["chat_id"]) if saved_ch else None)
                        target_msg_id = post_item.get("msg_id")
                        if not target_chat_id or not target_msg_id:
                            continue

                        assigned_media = media_list[idx] if idx < len(media_list) else None

                        if do_cap and cap_data:
                            new_cap = render_dynamic_caption(cap_data["template"], cap_data["index"])
                            cap_data["index"] += 1
                        else:
                            new_cap = format_bold_html(post_item.get("orig_caption") or "")

                        if assigned_media:
                            m_type = assigned_media["api_type"]
                            m_fid = assigned_media["file_id"]

                            # copyMessage কল করে মিডিয়া রেফারেন্স ভেরিফাই/কপি করা (ইউজারকে না পাঠিয়ে চ্যানেলে এডিট)
                            src_chat = assigned_media.get("source_chat_id")
                            src_mid = assigned_media.get("source_msg_id")
                            if src_chat and src_mid and m_type == "video":
                                copy_res = await tg_session_post(
                                    "copyMessage",
                                    {
                                        "chat_id": int(target_chat_id),
                                        "from_chat_id": int(src_chat),
                                        "message_id": int(src_mid),
                                        "disable_notification": True,
                                    },
                                )
                                if isinstance(copy_res, dict) and copy_res.get("ok"):
                                    temp_copied_id = (copy_res.get("result") or {}).get("message_id")
                                    if temp_copied_id:
                                        await tg_session_post(
                                            "deleteMessage",
                                            {
                                                "chat_id": int(target_chat_id),
                                                "message_id": int(temp_copied_id),
                                            },
                                        )

                            if m_type == "photo":
                                media_payload = {
                                    "type": "photo",
                                    "media": m_fid,
                                    "caption": new_cap,
                                    "parse_mode": "HTML",
                                }
                            else:
                                media_payload = {
                                    "type": "video",
                                    "media": m_fid,
                                    "caption": new_cap,
                                    "parse_mode": "HTML",
                                }
                                if do_thum and active_cover:
                                    media_payload["cover"] = active_cover

                            res = await tg_session_post(
                                "editMessageMedia",
                                {
                                    "chat_id": int(target_chat_id),
                                    "message_id": int(target_msg_id),
                                    "media": media_payload,
                                },
                            )
                            if res.get("ok"):
                                updated_ok += 1
                        else:
                            res = await api_edit_message_caption_only(
                                session=session,
                                chat_id=int(target_chat_id),
                                message_id=int(target_msg_id),
                                caption=new_cap,
                                parse_mode="HTML",
                            )
                            if res.get("ok"):
                                updated_ok += 1

                        await asyncio.sleep(get_user_upload_delay(user_id))

                await status_msg.edit_text(
                    f"✅ চ্যানেল পোস্ট এডিট সম্পন্ন হয়েছে! `{updated_ok}/{len(posts_list)}`টি পোস্ট আপডেট হয়েছে।\n"
                    "(Change media mode এখনো ON আছে—নতুন পোস্ট forward করতে পারেন অথবা বন্ধ করতে `/change_media` দিন)"
                )
                schedule_auto_delete(client, status_msg, delay=8)
                return

        # /cover on (batch mode) ok হ্যান্ডলিং (অটো অফ হবে না)
        if user_id in cover_batch_mode:
            batch_items = sorted(cover_batch_queue.get(user_id) or [], key=lambda x: x["order"])
            if not batch_items:
                await message.reply_text("Cover batch-এ কোনো ভিডিও জমা নেই।")
                return

            cover_batch_queue[user_id] = []
            cover_batch_counter[user_id] = 0
            status_msg = await message.reply_text(
                f"ভিডিওগুলোর Cover পাঠানো শুরু হচ্ছে: `0/{len(batch_items)}`..."
            )

            async def _send_batch_cover(b_item):
                return await send_video_own_cover(
                    client=client,
                    chat_id=message.chat.id,
                    message=None,
                    own_cover_file_id=b_item.get("cover_file_id"),
                )

            results = await run_batch_with_retry(
                _send_batch_cover,
                batch_items,
                delay_sec=get_user_upload_delay(user_id),
            )
            ok_cnt = sum(1 for _, r in results if isinstance(r, dict) and r.get("ok"))
            await status_msg.edit_text(
                f"✅ Cover batch সম্পন্ন হয়েছে! `{ok_cnt}/{len(batch_items)}`টি ভিডিওর cover পাঠানো হয়েছে।\n"
                "(Cover batch mode এখনো ON আছে—বন্ধ করতে `/cover` বা `/cover off` দিন)"
            )
            schedule_auto_delete(client, status_msg, delay=8)
            return

        await resolve_all_user_channel_titles(client, user_id)
        queue = pending_edits.get(user_id)
        saved_ch = get_active_user_channel(user_id)
        mode = get_user_mode(user_id)
        active_cover = user_cover_file_ids.get(user_id)
        cap_data = user_captions.get(user_id)
        upload_delay = get_user_upload_delay(user_id)

        need_cover = mode in ("cover", "both")
        need_caption = mode in ("caption", "both")

        if not queue:
            await message.reply_text("জমা রাখা কোনো ভিডিও নেই। আগে ভিডিও পাঠান বা forward করুন।")
            return
        if need_cover and not active_cover:
            await message.reply_text("কোনো Cover ছবি সেভ করা নেই। আগে `/thum` দিয়ে ছবি দিন।")
            return
        if need_caption and not cap_data:
            await message.reply_text("কোনো Caption সেভ করা নেই। আগে `/cap` দিয়ে Caption দিন।")
            return

        sorted_ids = sorted(queue.keys())
        items_to_process = [(mid, queue[mid]) for mid in sorted_ids]
        total_items = len(items_to_process)
        pending_edits[user_id] = {}

        has_channel_edits = any(item.get("channel_edit") for _, item in items_to_process)
        if has_channel_edits and not saved_ch:
            await message.reply_text("চ্যানেল এডিটের জন্য কোনো চ্যানেল সেভ করা নেই। আগে `/add` দিয়ে বা ENV-এ `CHANNEL_ID` দিয়ে চ্যানেল যুক্ত করুন।")
            return

        target_label = saved_ch["title"] if (has_channel_edits and saved_ch) else "Chat"
        status_msg = await message.reply_text(
            f"**{target_label}**-এ প্রসেস শুরু হচ্ছে: `0/{total_items}` (Delay: `{upload_delay}`s)"
        )

        success_count = 0
        fail_errors = []
        last_reported_count = 0

        async with aiohttp.ClientSession() as session:
            prepared_tasks = []
            for idx, (sort_key, item) in enumerate(items_to_process, start=1):
                current_cap_data = user_captions.get(user_id)
                if need_caption and current_cap_data:
                    final_caption = render_dynamic_caption(
                        current_cap_data["template"], current_cap_data["index"]
                    )
                    current_cap_data["index"] += 1
                else:
                    final_caption = format_bold_html(item["orig_caption"])

                is_ch_edit = bool(item.get("channel_edit") and saved_ch and item.get("msg_id") is not None)
                cover_to_use = active_cover if need_cover else None
                prepared_tasks.append((sort_key, item, final_caption, is_ch_edit, cover_to_use))

            async def _execute_single(entry):
                s_key, itm, f_cap, is_c_edit, cov_id = entry
                while True:
                    if is_c_edit:
                        msg_id = int(itm["msg_id"])
                        if mode == "caption":
                            res = await api_edit_message_caption_only(
                                session=session,
                                chat_id=int(saved_ch["chat_id"]),
                                message_id=msg_id,
                                caption=f_cap,
                                parse_mode="HTML",
                            )
                        else:
                            res = await api_edit_message_media_cover(
                                session=session,
                                chat_id=int(saved_ch["chat_id"]),
                                message_id=msg_id,
                                api_type=itm["api_type"],
                                file_id=itm["file_id"],
                                cover_file_id=cov_id,
                                caption=f_cap,
                                parse_mode="HTML",
                            )
                    else:
                        res = await api_send_media(
                            chat_id=message.chat.id,
                            api_type=itm["api_type"],
                            file_id=itm["file_id"],
                            cover_file_id=cov_id,
                            caption=f_cap,
                            parse_mode="HTML",
                        )

                    if res.get("ok"):
                        return s_key, res

                    retry_after = extract_retry_after(res)
                    if retry_after is not None:
                        wait_sec = retry_after + 1
                        try:
                            await status_msg.edit_text(
                                f"⏳ FloodWait: `{wait_sec}`s অপেক্ষা করা হচ্ছে... (`{success_count}/{total_items}` সম্পন্ন হয়েছে)"
                            )
                        except Exception:
                            pass
                        await asyncio.sleep(wait_sec)
                    else:
                        return s_key, res

            batch_size = 4
            for b_start in range(0, len(prepared_tasks), batch_size):
                batch_chunk = prepared_tasks[b_start : b_start + batch_size]
                chunk_outcomes = await asyncio.gather(
                    *[_execute_single(e) for e in batch_chunk],
                    return_exceptions=False,
                )
                for s_key, res in chunk_outcomes:
                    if isinstance(res, dict) and res.get("ok"):
                        success_count += 1
                    else:
                        err_desc = res.get("description", "Error") if isinstance(res, dict) else str(res)
                        fail_errors.append(f"ID {s_key}: {err_desc}")

                if upload_delay > 0 and b_start + batch_size < len(prepared_tasks):
                    await asyncio.sleep(upload_delay)

                processed_so_far = min(b_start + batch_size, total_items)
                if (
                    success_count - last_reported_count >= 5
                    or processed_so_far == total_items
                ) and success_count != last_reported_count:
                    last_reported_count = success_count
                    try:
                        await status_msg.edit_text(
                            f"⚡ প্রসেস চলছে: `{success_count}/{total_items}` (`{total_items}`টির মধ্যে `{success_count}` সম্পন্ন হয়েছে)"
                        )
                    except Exception:
                        pass

        summary = (
            f"✅ সম্পন্ন হয়েছে! **{target_label}**-এ `{success_count}/{total_items}` "
            f"(`{total_items}`টির মধ্যে `{success_count}` সম্পন্ন হয়েছে)।"
        )
        if fail_errors:
            summary += "\n\n**সমস্যা হওয়া আইটেম:**\n" + "\n".join(fail_errors[:10])

        await status_msg.edit_text(summary)
        schedule_auto_delete(client, status_msg, delay=8)


@app.on_message(filters.private & ~filters.forwarded)
async def handle_direct_media(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id

    cm = change_media_state.get(user_id)
    if cm and cm.get("stage") == "media":
        p_or_v = extract_photo_or_video_info(message)
        if p_or_v and p_or_v.get("kind") != "document":
            cm["counter"] += 1
            cm["media"].append({
                "order": cm["counter"],
                "api_type": p_or_v["api_type"],
                "file_id": p_or_v["file_id"],
                "orig_caption": message.caption or "",
                "source_chat_id": message.chat.id,
                "source_msg_id": message.id,
            })
            info_msg = await message.reply_text(
                f"মিডিয়া সেভ হয়েছে (Serial: `{cm['counter']}`)। মোট মিডিয়া: `{len(cm['media'])}`টি। শেষ হলে **`ok`** লিখুন।"
            )
            schedule_auto_delete(client, info_msg, delay=5)
            return

    info = extract_media_info(message)
    if not info:
        return

    if info["kind"] == "document":
        await message.reply_text(
            "সাধারণ `document`/file টাইপের ক্ষেত্রে Bot API-তে `cover` কাজ করে না—ভিডিও বা `.mp4`/`.mkv` ভিডিও ফাইল পাঠান।"
        )
        return

    # /cover instant mode চালু থাকলে সাথে সাথে সেই ভিডিওর নিজস্ব cover পাঠাবে (অটো অফ হবে না)
    if user_id in cover_instant_mode:
        res = await send_video_own_cover(
            client=client,
            chat_id=message.chat.id,
            message=message,
            own_cover_file_id=info.get("own_cover_file_id"),
        )
        if not res.get("ok"):
            await message.reply_text(res.get("description", "এই ভিডিওতে কোনো Cover পাওয়া যায়নি।"))
        return

    # /cover on (batch mode) চালু থাকলে সিরিয়াল অনুযায়ী সেভ করবে (অটো অফ হবে না)
    if user_id in cover_batch_mode:
        cover_batch_counter[user_id] = cover_batch_counter.get(user_id, 0) + 1
        seq_num = cover_batch_counter[user_id]
        cover_batch_queue.setdefault(user_id, []).append({
            "order": seq_num,
            "file_id": info["file_id"],
            "cover_file_id": info.get("own_cover_file_id"),
            "kind": info["kind"],
            "chat_id": message.chat.id,
            "msg_id": message.id,
        })
        info_msg = await message.reply_text(
            f"Cover batch-এ ভিডিও সেভ হয়েছে (Serial: `{seq_num}`)। মোট: `{len(cover_batch_queue[user_id])}`টি। শেষ হলে **`ok`** লিখুন।"
        )
        schedule_auto_delete(client, info_msg, delay=5)
        return

    seq_order = (len(pending_edits.get(user_id, {})) + 1)
    sort_key = queue_video_for_ok(
        user_id=user_id,
        file_id=info["file_id"],
        api_type="video",
        orig_caption=message.caption or "",
        channel_edit=False,
        msg_id=None,
        fallback_order_id=seq_order,
    )
    queue = pending_edits.get(user_id, {})
    id_label = f"Queue ID: `{sort_key}`"
    info_msg = await message.reply_text(
        f"ভিডিও সেভ হয়েছে ({id_label})। মোট জমা: `{len(queue)}`টি।\n"
        "সব ভিডিও পাঠানো শেষ হলে **`ok`** লিখুন (ছোট ID থেকে পাঠানো শুরু হবে)।"
    )
    schedule_auto_delete(client, info_msg, delay=5)


async def start_bot():
    start_flask_server()
    while True:
        try:
            await app.start()
            break
        except FloodWait as e:
            wait_sec = int(e.value) + 1
            print(f"FloodWait: {wait_sec} সেকেন্ড অপেক্ষা করা হচ্ছে...")
            await asyncio.sleep(wait_sec)
        except Exception as e:
            print("Pyrogram/Pyrofork start error:", e)
            traceback.print_exc()
            await asyncio.sleep(5)

    if ENV_CHANNEL_IDS:
        for cid in ENV_CHANNEL_IDS:
            fetched = await fetch_channel_title_from_api(app, cid, force_refresh=True)
            if fetched:
                print(f"ENV Channel Resolved: {cid} -> {fetched}")
        if ADMIN_ID is not None:
            ensure_user_channels_loaded(ADMIN_ID)
            await resolve_all_user_channel_titles(app, ADMIN_ID)

    print(f"Bot is running on port {PORT}! URL: {PUBLIC_BASE_URL}")
    try:
        while True:
            await asyncio.sleep(1)
    except asyncio.CancelledError:
        pass
    finally:
        try:
            await app.stop()
        except Exception:
            pass
        print("Bot stopped cleanly.")


if __name__ == "__main__":
    try:
        _loop.run_until_complete(start_bot())
    finally:
        _loop.close()
