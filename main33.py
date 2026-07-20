import asyncio
import os
from pyrogram import Client, filters
from pyrogram.types import BotCommand

API_ID = int(os.getenv("API_ID"))
API_HASH = os.getenv("API_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
ADMIN_ID = int(os.getenv("ADMIN_ID", ""))

app = Client("test_drive", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN)

# Minimal drive mode state
DRIVE_MODE = set()
DRIVE_SESSION = {}

@app.on_message(filters.command("drive") & filters.private)
async def drive_cmd(c, m):
    print(f"🚀 Drive command received from {m.from_user.id}")
    uid = m.from_user.id
    if uid != ADMIN_ID:
        await m.reply_text("You are not authorized.")
        return
    if uid in DRIVE_MODE:
        DRIVE_MODE.discard(uid)
        DRIVE_SESSION.pop(uid, None)
        await m.reply_text("Drive Mode OFF.")
    else:
        DRIVE_MODE.add(uid)
        DRIVE_SESSION[uid] = {"path": "/content/drive/MyDrive"}
        await m.reply_text("Drive Mode ON. Use numbers to browse files.")

async def main():
    await app.start()
    await app.set_bot_commands([BotCommand("drive", "Test drive mode")])
    print("Bot started. Send /drive to your bot.")
    await asyncio.Event().wait()

if __name__ == "__main__":
    asyncio.run(main())
