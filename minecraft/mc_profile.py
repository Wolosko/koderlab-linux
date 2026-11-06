#!/usr/bin/env python3
"""Ник и настройки Legacy Launcher для KoderLab.

Лаунчер хранит:
  - аккаунты — в <папка игры>/tlauncher_profiles.json ("plain" = офлайн-ник);
  - настройки — в ~/.tlauncher/legacy.properties (Java .properties),
    на Windows — в %APPDATA%\\.tlauncher\\legacy.properties.
Модуль общий для koderlab-linux и koderlab-windows.
Формат проверен на Legacy Launcher 1.169.4: с этими файлами он сразу
открывается с нужным ником, версией «Forge 1.8.9» и папкой игры.

Запуск:
  mc_profile.py ensure <папка игры> <файл настроек> <файл ника> [ник]
      записать ник (новый или сохранённый) и настройки; печатает ник
  mc_profile.py nick <файл ника>
      показать ник этого компьютера (сохранённый или сгенерированный)
"""

import glob
import hashlib
import json
import os
import random
import re
import socket
import sys
import uuid

NICK_PREFIX = "Koder"
NICK_RE = re.compile(r"^[A-Za-z0-9_]{3,16}$")   # правила ников Minecraft
VERSION = "Forge 1.8.9"   # id в репозитории лаунчера = Forge 11.15.1.2318

# всегда переписываем: без них ученик увидит рекламу серверов и чужую версию
FORCED_SETTINGS = {
    "login.version": VERSION,
    "minecraft.versions.modified": "true",
    "minecraft.servers.promoted": "false",
    "minecraft.servers.promoted.ingame": "false",
    "notice.enabled": "false",
    "notice.promoted": "false",
    "gui.notices.enabled": "false",
}
# только если ещё не заданы; без settings.version лаунчер сбрасывает файл
DEFAULT_SETTINGS = {
    "settings.version": "3",
    "locale": "ru_RU",
}


def valid_nick(nick):
    return bool(nick and NICK_RE.match(nick))


def _machine_seed():
    """Отпечаток компьютера. Одного machine-id мало: компьютеры класса часто
    разворачивают из одного образа, и он у всех совпадает. MAC-адреса и имя
    компьютера у клонов разные."""
    parts = []
    if os.name == "nt":
        # Windows: MachineGuid (у клонов образа тоже бывает общим) + имя
        # компьютера + MAC — как и на Linux, вместе они различают ПК класса
        try:
            import winreg
            with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,
                                r"SOFTWARE\Microsoft\Cryptography", 0,
                                winreg.KEY_READ | winreg.KEY_WOW64_64KEY) as k:
                parts.append(str(winreg.QueryValueEx(k, "MachineGuid")[0]))
        except OSError:
            pass
        parts.append(socket.gethostname())
        mac = uuid.getnode()
        if not (mac >> 40) & 1:      # бит «случайный адрес» — значит, MAC не нашёлся
            parts.append("%012x" % mac)
        return "|".join(p for p in parts if p)
    for p in ("/etc/machine-id", "/var/lib/dbus/machine-id"):
        try:
            with open(p, encoding="ascii", errors="ignore") as f:
                parts.append(f.read().strip())
            break
        except OSError:
            pass
    parts.append(socket.gethostname())
    for addr in sorted(glob.glob("/sys/class/net/*/address")):
        if "/lo/" in addr:
            continue
        try:
            with open(addr, encoding="ascii", errors="ignore") as f:
                mac = f.read().strip()
            if mac and mac != "00:00:00:00:00:00":
                parts.append(mac)
        except OSError:
            pass
    return "|".join(p for p in parts if p)


def generate_nick():
    seed = _machine_seed()
    if seed:
        n = int(hashlib.sha256(seed.encode()).hexdigest(), 16) % 9000 + 1000
    else:
        n = random.randint(1000, 9999)
    return f"{NICK_PREFIX}{n}"


def random_nick():
    return f"{NICK_PREFIX}{random.randint(1000, 9999)}"


def load_nick(nick_file):
    try:
        with open(nick_file, encoding="utf-8") as f:
            nick = f.read().strip()
        if valid_nick(nick):
            return nick
    except OSError:
        pass
    return None


def save_nick(nick_file, nick):
    os.makedirs(os.path.dirname(nick_file), exist_ok=True)
    with open(nick_file, "w", encoding="utf-8") as f:
        f.write(nick + "\n")


def offline_uuid(nick):
    """UUID офлайн-игрока, как у Minecraft: v3 от "OfflinePlayer:<ник>"."""
    h = bytearray(hashlib.md5(("OfflinePlayer:" + nick).encode()).digest())
    h[6] = (h[6] & 0x0F) | 0x30
    h[8] = (h[8] & 0x3F) | 0x80
    return uuid.UUID(bytes=bytes(h)).hex


def _atomic_write(path, text):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
    os.replace(tmp, path)


def write_profiles(game_dir, nick, old_nick=None, force_select=True):
    """Добавляет офлайн-аккаунт. Чужие аккаунты (если ученик добавил свой)
    не трогаем; убираем только наш прежний ник.

    force_select=False — при обычном запуске: если ученик сам выбрал в лаунчере
    другой аккаунт, оставляем его выбор. Возвращает имя выбранного аккаунта."""
    path = os.path.join(game_dir, "tlauncher_profiles.json")
    data = {}
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        data = {}
    if not isinstance(data, dict):
        data = {}
    user_set = data.get("userSet")
    if not isinstance(user_set, dict):
        user_set = {}
    users = [u for u in user_set.get("list") or [] if isinstance(u, dict)
             and not (old_nick and old_nick != nick
                      and u.get("type") == "plain" and u.get("username") == old_nick)]
    if not any(u.get("type") == "plain" and u.get("username") == nick for u in users):
        users.append({"username": nick, "uuid": offline_uuid(nick),
                      "elySkins": False, "type": "plain"})
    user_set["list"] = users
    sel = user_set.get("selected")
    keep = (not force_select and isinstance(sel, dict) and any(
        u.get("username") == sel.get("username") and u.get("type") == sel.get("type")
        for u in users))
    if not keep:
        user_set["selected"] = {"username": nick, "type": "plain"}
    data["userSet"] = user_set
    _atomic_write(path, json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    return user_set["selected"]


def _prop_escape(value):
    """Java .properties: \\, переводы строк и всё не-ASCII — через \\uXXXX
    (путь вида /home/ученик иначе может прочитаться кракозябрами)."""
    out = []
    for ch in value:
        if ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ord(ch) > 126 or ord(ch) < 32:
            out.append("\\u%04x" % ord(ch))
        else:
            out.append(ch)
    return "".join(out)


def write_settings(settings_file, game_dir):
    """Правит только нужные ключи, остальные настройки ученика сохраняются."""
    lines = []
    try:
        with open(settings_file, encoding="latin-1") as f:
            lines = f.read().splitlines()
    except OSError:
        lines = ["# Legacy Launcher Stable properties"]
    forced = dict(FORCED_SETTINGS, **{"minecraft.gamedir": game_dir})
    seen = set()
    result = []
    for line in lines:
        key = re.split(r"\s*[=:]\s*|\s+", line.strip(), maxsplit=1)[0] \
            if line.strip() and not line.lstrip().startswith(("#", "!")) else None
        if key in forced:
            if key not in seen:              # повторы ключа выкидываем
                result.append(f"{key}={_prop_escape(forced[key])}")
                seen.add(key)
        else:
            if key:
                seen.add(key)
            result.append(line)
    for key, value in list(forced.items()) + list(DEFAULT_SETTINGS.items()):
        if key not in seen:
            result.append(f"{key}={_prop_escape(value)}")
            seen.add(key)
    _atomic_write(settings_file, "\n".join(result) + "\n")
    return settings_file


def ensure(game_dir, settings_file, nick_file, nick=None):
    """nick задан (окно, установка) — он становится выбранным.
    Не задан (каждый запуск) — сохраняем выбор, сделанный в самом лаунчере:
    ученик добавил там свой ник — он и останется, вводить заново не нужно.
    Если выбран офлайн-ник, запоминаем его в nick_file (покажется в окне)."""
    if nick and not valid_nick(nick):
        raise ValueError(f"недопустимый ник: {nick!r} (3–16 символов: латиница, цифры, _)")
    old_nick = load_nick(nick_file)
    explicit = bool(nick)
    nick = nick or old_nick or generate_nick()
    # убираем при смене только свой прежний Koder-ник: аккаунт, который
    # ученик завёл сам, остаётся в списке
    ours = old_nick if explicit and old_nick and old_nick.startswith(NICK_PREFIX) else None
    selected = write_profiles(game_dir, nick, ours, force_select=explicit)
    if selected.get("type") == "plain" and valid_nick(selected.get("username")):
        nick = selected["username"]
    save_nick(nick_file, nick)
    write_settings(settings_file, game_dir)
    return selected.get("username") or nick


def main(argv):
    if len(argv) >= 5 and argv[1] == "ensure":
        try:
            print(ensure(argv[2], argv[3], argv[4], argv[5] if len(argv) > 5 else None))
        except (OSError, ValueError) as e:
            print(f"ошибка: {e}", file=sys.stderr)
            return 1
        return 0
    if len(argv) == 3 and argv[1] == "nick":
        print(load_nick(argv[2]) or generate_nick())
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
