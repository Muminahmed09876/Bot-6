import asyncio
import html
import os
import re
import socket
import threading
import time
import traceback
import urllib.request

# Render / Python 3.14-এ event loop আগে থেকেই সেট করে রাখা
_loop = asyncio.new_event_loop()
asyncio.set_event_loop(_loop)

import aiohttp
from flask import Flask, render_template_string

try:
    from pyrofork import Client, filters
    from pyrofork.enums import ChatType
    from pyrofork.errors import FloodWait, RPCError
    from pyrofork.types import InlineKeyboardButton, InlineKeyboardMarkup
except ImportError:
    from pyrogram import Client, filters
    from pyrogram.enums import ChatType
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
user_captions = {}           # {user_id: {"template": str, "index": int}}
user_modes = {}              # {user_id: "cover" | "caption" | "both"}
pending_edits = {}           # {user_id: {msg_id: {"file_id": str, "api_type": str, "orig_caption": str}}}
resolved_channel_titles = {} # {chat_id: str}

waiting_for_thumb = set()    # {user_id}
waiting_for_channel = set()  # {user_id}
waiting_for_caption = set()  # {user_id}


async def fetch_channel_title_from_api(client, chat_id: int) -> str | None:
    cid = int(chat_id)
    if cid in resolved_channel_titles and resolved_channel_titles[cid]:
        return resolved_channel_titles[cid]

    try:
        chat_obj = await client.get_chat(cid)
        title = getattr(chat_obj, "title", None) or getattr(chat_obj, "first_name", None)
        if title and str(title).strip():
            clean = str(title).strip()
            resolved_channel_titles[cid] = clean
            return clean
    except Exception:
        pass

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
    except Exception:
        pass

    return None


async def resolve_all_user_channel_titles(client, user_id: int):
    ch_list = ensure_user_channels_loaded(user_id)
    active = get_active_user_channel(user_id)
    for item in ch_list:
        cid = int(item["chat_id"])
        fetched = await fetch_channel_title_from_api(client, cid)
        if fetched:
            item["title"] = fetched
            if active and int(active["chat_id"]) == cid:
                user_channels[user_id]["title"] = fetched


def ensure_user_channels_loaded(user_id: int) -> list[dict]:
    if user_id not in user_channel_lists:
        loaded = []
        for idx, cid in enumerate(ENV_CHANNEL_IDS, start=1):
            cached_title = resolved_channel_titles.get(int(cid))
            loaded.append({
                "chat_id": int(cid),
                "title": cached_title if cached_title else f"Channel {idx} ({cid})",
            })
        user_channel_lists[user_id] = loaded
    else:
        for idx, item in enumerate(user_channel_lists[user_id], start=1):
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


def extract_media_info(message):
    if message.video:
        return {
            "kind": "video",
            "api_type": "video",
            "file_id": message.video.file_id,
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
        }
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

    async with session.post(f"{API_BASE}/editMessageCaption", json=payload) as resp:
        return await resp.json()


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
    async with session.post(f"{API_BASE}/editMessageMedia", json=payload) as resp:
        return await resp.json()


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
    else:
        method = "sendDocument"
        payload = {
            "chat_id": chat_id,
            "document": file_id,
            "caption": caption,
        }
        if parse_mode:
            payload["parse_mode"] = parse_mode

    async with aiohttp.ClientSession() as session:
        async with session.post(f"{API_BASE}/{method}", json=payload) as resp:
            return await resp.json()


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
        "/add - চ্যানেল যুক্ত করবে (মেসেজ, ইমেজ, ভিডিও ইত্যাদি ফরোয়ার্ড করে)\n"
        "/list - সেভ করা সকল চ্যানেল দেখাবে এবং বাটন দিয়ে সিলেক্ট করতে দেবে\n"
        "/time - upload/edit delay টাইম সেট করবে (যেমন: /time 1.2, 2, 2.5, 3)\n"
        "/cap - কাস্টম caption সেভ করবে\n"
        "/cap_view - সেভ করা caption দেখাবে এবং delete বাটন দেবে\n"
        "/mode - covar, caption, অথবা covar and caption মোড নির্বাচন করবে\n"
        "/send 19 অথবা /send 2-20 - সিলেক্ট করা চ্যানেলের মেসেজ বা রেঞ্জ forward করবে\n"
        "ok - ফরোয়ার্ড করে জমা রাখা ভিডিওগুলো ছোট Post ID থেকে edit শুরু করবে"
    )
    await message.reply_text(help_text, parse_mode=None)


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
    await resolve_all_user_channel_titles(client, user_id)
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
    waiting_for_channel.add(user_id)
    await message.reply_text(
        "দয়া করে আপনার **Channel** থেকে যেকোনো একটি মেসেজ, ইমেজ, ভিডিও বা ফাইল এই চ্যাটে **Forward** করুন।"
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
    saved_ch = get_active_user_channel(user_id)
    if not saved_ch:
        await message.reply_text(
            "আগে `/add` দিয়ে বা ENV-এ `CHANNEL_ID` দিয়ে একটি চ্যানেল যুক্ত করুন, তারপর `/send 19` অথবা `/send 2-20` দিন।"
        )
        return

    parts = message.text.split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        await message.reply_text(
            "ব্যবহারের নিয়ম:\n"
            "• `/send 19` — সিলেক্ট করা চ্যানেলের ১৯ নম্বর মেসেজ forward করবে\n"
            "• `/send 2-20` — সিলেক্ট করা চ্যানেলের ২ থেকে ২০ নম্বর মেসেজ forward করবে"
        )
        return

    parsed = parse_message_range(parts[1])
    if parsed is None:
        await message.reply_text("সঠিক Message ID বা রেঞ্জ দিন। যেমন: `/send 19` অথবা `/send 2-20`")
        return
    if parsed == "TOO_LARGE":
        await message.reply_text("একবারে সর্বোচ্চ ২০০টি মেসেজের রেঞ্জ দেওয়া যাবে।")
        return

    channel_id = int(saved_ch["chat_id"])
    channel_title = saved_ch["title"]
    status_msg = await message.reply_text(
        f"**{channel_title}** (`{channel_id}`) চ্যানেল থেকে `{parts[1].strip()}` মেসেজ forward করা হচ্ছে..."
    )

    forwarded_count = 0
    for msg_id in parsed:
        while True:
            try:
                await client.forward_messages(
                    chat_id=message.chat.id,
                    from_chat_id=channel_id,
                    message_ids=msg_id,
                )
                forwarded_count += 1
                await asyncio.sleep(0.25)
                break
            except FloodWait as e:
                await asyncio.sleep(int(e.value) + 1)
            except RPCError:
                break

    await status_msg.edit_text(
        f"সম্পন্ন হয়েছে! **{channel_title}** থেকে মোট `{forwarded_count}`টি মেসেজ forward tag সহ পাঠানো হয়েছে।"
    )


@app.on_message(filters.photo & filters.private)
async def handle_photo(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    if message.forward_from_chat and message.forward_from_chat.type == ChatType.CHANNEL and user_id in waiting_for_channel:
        origin_chat = message.forward_from_chat
        saved_entry = save_user_channel_entry(
            user_id=user_id,
            chat_id=origin_chat.id,
            title=origin_chat.title or "Channel",
            set_active=True,
        )
        waiting_for_channel.discard(user_id)
        await message.reply_text(
            f"চ্যানেল সেভ হয়েছে (ইমেজ ফরোয়ার্ড থেকে): **{saved_entry['title']}** (`{saved_entry['chat_id']}`)"
        )
        return

    if user_id in waiting_for_thumb or user_id not in user_cover_file_ids:
        user_cover_file_ids[user_id] = message.photo.file_id
        waiting_for_thumb.discard(user_id)
        await message.reply_text(
            "Cover ছবি সেভ হয়েছে!\n"
            "• সেভ করা চ্যানেলের ভিডিওগুলো forward করুন (সব সেভ হবে), তারপর **`ok`** লিখলে ছোট Post ID থেকে এডিট শুরু হবে।"
        )
    else:
        await message.reply_text("নতুন ছবি সেট করতে চাইলে আগে `/thum` কমান্ড দিন।")


@app.on_message(filters.forwarded & filters.private)
async def handle_forwarded(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    origin_chat = message.forward_from_chat
    origin_msg_id = message.forward_from_message_id

    if origin_chat and origin_chat.type == ChatType.CHANNEL and origin_chat.title:
        resolved_channel_titles[int(origin_chat.id)] = str(origin_chat.title).strip()

    if user_id in waiting_for_channel:
        if not origin_chat or origin_chat.type != ChatType.CHANNEL:
            await message.reply_text(
                "দয়া করে একটি **Channel** থেকে মেসেজ, ইমেজ, ভিডিও বা ফাইল forward করুন।"
            )
            return
        saved_entry = save_user_channel_entry(
            user_id=user_id,
            chat_id=origin_chat.id,
            title=origin_chat.title or "Channel",
            set_active=True,
        )
        waiting_for_channel.discard(user_id)
        await message.reply_text(
            f"চ্যানেল সেভ হয়েছে: **{saved_entry['title']}** (`{saved_entry['chat_id']}`)"
        )
        return

    info = extract_media_info(message)
    if not info:
        return

    if info["kind"] == "document":
        await message.reply_text(
            "সাধারণ `document`/file টাইপের ক্ষেত্রে Bot API-তে `cover` কাজ করে না—ভিডিও বা `.mp4`/`.mkv` ভিডিও ফাইল পাঠান।"
        )
        return

    mode = get_user_mode(user_id)
    active_cover = user_cover_file_ids.get(user_id)
    cap_data = user_captions.get(user_id)

    need_cover = mode in ("cover", "both")
    need_caption = mode in ("caption", "both")

    if need_cover and not active_cover:
        await message.reply_text("আগে `/thum` কমান্ড দিয়ে একটি ছবি পাঠান।")
        return
    if need_caption and not cap_data:
        await message.reply_text("আগে `/cap` কমান্ড দিয়ে একটি caption সেট করুন।")
        return

    await resolve_all_user_channel_titles(client, user_id)
    saved_ch = get_active_user_channel(user_id)

    if saved_ch and origin_chat and int(origin_chat.id) == int(saved_ch["chat_id"]) and origin_msg_id:
        queue = pending_edits.setdefault(user_id, {})
        queue[origin_msg_id] = {
            "file_id": info["file_id"],
            "api_type": "video",
            "orig_caption": message.caption or "",
        }
        info_msg = await message.reply_text(
            f"ভিডিও সেভ হয়েছে (Post ID: `{origin_msg_id}`)। মোট জমা: `{len(queue)}`টি।\n"
            "সব ভিডিও পাঠানো শেষ হলে **`ok`** লিখুন (ছোট Post ID থেকে এডিট শুরু হবে)।"
        )
        schedule_auto_delete(client, info_msg, delay=5)
        return

    if need_caption and cap_data:
        final_caption = render_dynamic_caption(cap_data["template"], cap_data["index"])
        cap_data["index"] += 1
    else:
        final_caption = format_bold_html(message.caption or "")

    cover_to_use = active_cover if need_cover else None

    status_msg = await message.reply_text("বটে ভিডিও পাঠানো হচ্ছে...")
    result = await api_send_media(
        chat_id=message.chat.id,
        api_type="video",
        file_id=info["file_id"],
        cover_file_id=cover_to_use,
        caption=final_caption,
        parse_mode="HTML",
    )
    if result.get("ok"):
        await status_msg.delete()
    else:
        await status_msg.edit_text(
            f"Telegram API রেসপন্স: `{result.get('description', result)}`"
        )


@app.on_message(
    filters.text
    & filters.private
    & ~filters.forwarded
    & ~filters.command(["start", "thum", "view_thum", "mode", "add", "list", "time", "cap", "cap_view", "send"])
)
async def handle_text_inputs(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    user_id = message.from_user.id
    text_val = (message.text or "").strip()

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

    if text_val.lower() == "ok":
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
            await message.reply_text("এডিট করার জন্য কোনো ভিডিও জমা নেই। আগে চ্যানেল থেকে ভিডিও forward করুন।")
            return
        if not saved_ch:
            await message.reply_text("কোনো চ্যানেল সেভ করা নেই। আগে `/add` দিয়ে বা ENV-এ `CHANNEL_ID` দিয়ে চ্যানেল যুক্ত করুন।")
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

        status_msg = await message.reply_text(
            f"**{saved_ch['title']}** চ্যানেলে এডিট শুরু হচ্ছে: `0/{total_items}` (Delay: `{upload_delay}`s)"
        )

        success_count = 0
        fail_errors = []
        last_reported_count = 0

        async with aiohttp.ClientSession() as session:
            for idx, (msg_id, item) in enumerate(items_to_process, start=1):
                current_cap_data = user_captions.get(user_id)
                if need_caption and current_cap_data:
                    final_caption = render_dynamic_caption(
                        current_cap_data["template"], current_cap_data["index"]
                    )
                    current_cap_data["index"] += 1
                else:
                    final_caption = format_bold_html(item["orig_caption"])

                while True:
                    if mode == "caption":
                        result = await api_edit_message_caption_only(
                            session=session,
                            chat_id=saved_ch["chat_id"],
                            message_id=msg_id,
                            caption=final_caption,
                            parse_mode="HTML",
                        )
                    else:
                        cover_to_use = active_cover if need_cover else None
                        result = await api_edit_message_media_cover(
                            session=session,
                            chat_id=saved_ch["chat_id"],
                            message_id=msg_id,
                            api_type=item["api_type"],
                            file_id=item["file_id"],
                            cover_file_id=cover_to_use,
                            caption=final_caption,
                            parse_mode="HTML",
                        )

                    if result.get("ok"):
                        success_count += 1
                        await asyncio.sleep(get_user_upload_delay(user_id))
                        break

                    retry_after = extract_retry_after(result)
                    if retry_after is not None:
                        wait_sec = retry_after + 1
                        try:
                            await status_msg.edit_text(
                                f"⏳ FloodWait: `{wait_sec}`s অপেক্ষা করা হচ্ছে... (`{success_count}/{total_items}` edit হয়েছে)"
                            )
                        except Exception:
                            pass
                        await asyncio.sleep(wait_sec)
                    else:
                        fail_errors.append(f"ID {msg_id}: {result.get('description', 'Error')}")
                        break

                # প্রতি ৫টি এডিট পরপর প্রোগ্রেস আপডেট (`10/80`—৮০টি post edit এর মধ্যে 10 edit হয়েছে)
                if (
                    success_count - last_reported_count >= 5
                    or idx == total_items
                ) and success_count != last_reported_count:
                    last_reported_count = success_count
                    try:
                        await status_msg.edit_text(
                            f"⚡ এডিট চলছে: `{success_count}/{total_items}` (`{total_items}`টি post edit এর মধ্যে `{success_count}` edit হয়েছে)"
                        )
                    except Exception:
                        pass

        summary = (
            f"✅ সম্পন্ন হয়েছে! **{saved_ch['title']}** চ্যানেলে `{success_count}/{total_items}` "
            f"(`{total_items}`টি post edit এর মধ্যে `{success_count}` edit হয়েছে)।"
        )
        if fail_errors:
            summary += "\n\n**সমস্যা হওয়া পোস্ট:**\n" + "\n".join(fail_errors[:10])

        await status_msg.edit_text(summary)
        schedule_auto_delete(client, status_msg, delay=8)


@app.on_message(filters.private & ~filters.forwarded)
async def handle_direct_media(client, message):
    if not is_admin(message.from_user.id if message.from_user else None):
        return
    info = extract_media_info(message)
    if not info:
        return

    if info["kind"] == "document":
        await message.reply_text(
            "সাধারণ `document`/file টাইপের ক্ষেত্রে Bot API-তে `cover` কাজ করে না—ভিডিও বা `.mp4`/`.mkv` ভিডিও ফাইল পাঠান।"
        )
        return

    user_id = message.from_user.id
    mode = get_user_mode(user_id)
    active_cover = user_cover_file_ids.get(user_id)
    cap_data = user_captions.get(user_id)

    need_cover = mode in ("cover", "both")
    need_caption = mode in ("caption", "both")

    if need_cover and not active_cover:
        await message.reply_text("আগে `/thum` কমান্ড দিয়ে একটি ছবি পাঠান।")
        return
    if need_caption and not cap_data:
        await message.reply_text("আগে `/cap` কমান্ড দিয়ে একটি caption সেট করুন।")
        return

    if need_caption and cap_data:
        final_caption = render_dynamic_caption(cap_data["template"], cap_data["index"])
        cap_data["index"] += 1
    else:
        final_caption = format_bold_html(message.caption or "")

    cover_to_use = active_cover if need_cover else None

    status_msg = await message.reply_text("বটে ভিডিও পাঠানো হচ্ছে...")
    result = await api_send_media(
        chat_id=message.chat.id,
        api_type="video",
        file_id=info["file_id"],
        cover_file_id=cover_to_use,
        caption=final_caption,
        parse_mode="HTML",
    )
    if result.get("ok"):
        await status_msg.delete()
    else:
        await status_msg.edit_text(
            f"Telegram API রেসপন্স: `{result.get('description', result)}`"
        )


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
            fetched = await fetch_channel_title_from_api(app, cid)
            if fetched:
                print(f"ENV Channel Resolved: {cid} -> {fetched}")

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
