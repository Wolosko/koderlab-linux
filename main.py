#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Установщик курсов KoderLab — Linux (ROSA Linux, М ОС / Альт, Astra, Debian/Ubuntu).

Возможности:
  • Установка приложений по курсам: пакеты из репозитория дистрибутива,
    локальные .rpm/.deb, AppImage, tar.gz/tar.xz/zip-архивы, .sh-инсталляторы,
    flatpak, .jar (через Java), веб-ярлыки и моды Minecraft.
  • У каждого приложения виден статус: установлено / не установлено
    (проверка через rpm/dpkg/flatpak, наличие команды в PATH, путь или маркер).
  • Удаление приложений из этого же окна.
  • Раздача этой же папки по локальной сети (встроенный HTTP-сервер) и
    получение её с другого компьютера — без интернета и флешек.
  • Живой вывод (как в терминале) с прогресс-баром.
  • Права root запрашиваются один раз через pkexec (окно ввода пароля),
    дальше пакеты ставятся без повторных запросов.

Запуск:  ./start.sh   или   python3 main.py
"""

import functools
import glob as globmod
import http.server
import json
import os
import queue
import re
import shutil
import socket
import socketserver
import subprocess
import sys
import platform
import tarfile
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from datetime import datetime

if sys.platform.startswith("win"):
    print("Эта версия установщика предназначена для Linux.\n"
          "Для Windows используйте сборку koderlab-windows (main.py / main.exe).")
    sys.exit(1)

from PyQt5.QtCore import Qt, QThread, QTimer, pyqtSignal  # noqa: E402
from PyQt5.QtGui import (  # noqa: E402
    QColor, QTextCursor, QTextCharFormat, QPainter, QPixmap, QIcon, QFont,
    QBrush, QPen,
)
from PyQt5.QtWidgets import (  # noqa: E402
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QPushButton, QLabel, QTreeWidget, QTreeWidgetItem, QProgressBar,
    QTextEdit, QMessageBox, QFrame, QInputDialog, QLineEdit, QFileDialog,
    QDialog, QListWidget, QListWidgetItem, QDialogButtonBox, QCheckBox,
    QScrollArea, QGridLayout, QToolButton, QProgressDialog,
)

# ---------------------------------------------------------------------------
# Пути
# ---------------------------------------------------------------------------


def _base_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


BASE_DIR = _base_dir()
COURSES_FILE = os.path.join(BASE_DIR, "courses.json")
INSTALLERS_DIR = os.path.join(BASE_DIR, "installers")
ICONS_DIR = os.path.join(BASE_DIR, "icons")

HOME = os.path.expanduser("~")


def _real_home():
    """Домашняя папка настоящего пользователя, даже если программа запущена
    через pkexec/sudo (иначе всё уедет в /root и ученик ничего не увидит)."""
    user = os.environ.get("PKEXEC_UID")
    if user:
        try:
            import pwd
            return pwd.getpwuid(int(user)).pw_dir
        except Exception:
            pass
    sudo_user = os.environ.get("SUDO_USER")
    if sudo_user:
        try:
            import pwd
            return pwd.getpwnam(sudo_user).pw_dir
        except Exception:
            pass
    return HOME


USER_HOME = _real_home()
DATA_DIR = os.path.join(USER_HOME, ".local", "share", "KoderLab")
LOCAL_APPS_DIR = os.path.join(DATA_DIR, "apps")
MARKERS_DIR = os.path.join(DATA_DIR, "installed")
DESKTOP_DIR = os.path.join(USER_HOME, ".local", "share", "applications")
BIN_DIR = os.path.join(USER_HOME, ".local", "bin")
MINECRAFT_MODS_DIR = os.path.join(USER_HOME, ".minecraft", "mods")

SHARE_PORT = 8765
SHARE_DIR = os.path.join(DATA_DIR, "share")

LOG_COLORS = {
    "ok": "#4EC94E", "run": "#5AA9FF", "err": "#FF6B6B",
    "warn": "#FFC24B", "info": "#C8C8C8", "cmd": "#9B93E0",
}
SPINNER = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"

ARCHIVE_EXTS = (".tar.gz", ".tgz", ".tar.xz", ".tar.bz2", ".zip")


def ensure_dirs():
    for d in (LOCAL_APPS_DIR, MARKERS_DIR, DESKTOP_DIR, BIN_DIR):
        try:
            os.makedirs(d, exist_ok=True)
        except OSError:
            pass


def _user_makedirs(path):
    """Создаёт папку и сразу отдаёт её настоящему пользователю.

    Критично для Wine: если папку создал root, wine под пользователем
    отказывается работать — «is not owned by you». Владельца надо назначить
    всей цепочке папок, а не только последней."""
    os.makedirs(path, exist_ok=True)
    info = real_user_info()
    if not info:
        return path
    _user, home, uid = info
    try:
        import pwd
        gid = pwd.getpwuid(uid).pw_gid
    except (KeyError, ValueError):
        return path
    # поднимаемся вверх до домашней папки, выправляя владельца по дороге
    chain, cur = [], os.path.abspath(path)
    while cur.startswith(os.path.abspath(home)) and cur != os.path.abspath(home):
        chain.append(cur)
        cur = os.path.dirname(cur)
    for d in reversed(chain):
        try:
            st = os.stat(d)
            if st.st_uid != uid:
                os.chown(d, uid, gid)
        except OSError:
            pass
    return path


def _chown_to_user(path):
    """Если работаем под root — вернуть владельца файлам в домашней папке
    ученика, иначе он не сможет их изменить/удалить."""
    if os.geteuid() != 0:
        return
    uid = os.environ.get("PKEXEC_UID")
    try:
        if uid:
            uid = int(uid)
            import pwd
            gid = pwd.getpwuid(uid).pw_gid
        else:
            sudo_user = os.environ.get("SUDO_USER")
            if not sudo_user:
                return
            import pwd
            pw = pwd.getpwnam(sudo_user)
            uid, gid = pw.pw_uid, pw.pw_gid
        for root, dirs, files in os.walk(path):
            for name in dirs + files:
                try:
                    os.chown(os.path.join(root, name), uid, gid)
                except OSError:
                    pass
        os.chown(path, uid, gid)
    except Exception:
        pass


def _normalize(s):
    return re.sub(r"[^a-z0-9а-яё]", "", s.lower())


def _app_keywords(app_id, app):
    kws = app.get("match_keywords")
    if kws:
        return [k.lower() for k in kws]
    base = []
    if app.get("file"):
        base.append(_strip_ext(os.path.basename(app["file"])))
    base.append(app_id)
    return [k.lower() for k in base]


def _strip_ext(name):
    low = name.lower()
    for e in ARCHIVE_EXTS:
        if low.endswith(e):
            return name[: -len(e)]
    return os.path.splitext(name)[0]


def _clean(s):
    return "".join(ch for ch in s if ch >= " " or ch in "\n\r\t").replace("\t", "    ")


# ---------------------------------------------------------------------------
# Определение дистрибутива и пакетного менеджера
# ---------------------------------------------------------------------------

def read_os_release():
    data = {}
    for path in ("/etc/os-release", "/usr/lib/os-release"):
        if os.path.exists(path):
            try:
                with open(path, encoding="utf-8", errors="replace") as f:
                    for raw in f:
                        if "=" in raw:
                            k, v = raw.rstrip("\n").split("=", 1)
                            data[k] = v.strip().strip('"')
                break
            except OSError:
                pass
    return data


OS_RELEASE = read_os_release()


def detect_pkg_manager():
    """Возвращает (менеджер, семейство пакетов).

    Менеджеры: dnf, urpmi, apt-rpm (Альт / М ОС), zypper, apt (deb), rpm.
    Семейство: 'rpm' или 'deb' — от него зависит выбор имени пакета
    и локального файла (.rpm или .deb).
    """
    which = shutil.which
    has_rpm = bool(which("rpm"))
    has_dpkg = bool(which("dpkg"))
    ident = (OS_RELEASE.get("ID", "") + " " + OS_RELEASE.get("ID_LIKE", "")).lower()

    if has_rpm and not has_dpkg:
        if "altlinux" in ident or "alt" in ident.split():
            if which("apt-get"):
                return "apt-rpm", "rpm"
        if which("dnf"):
            return "dnf", "rpm"
        if which("urpmi"):
            return "urpmi", "rpm"
        if which("apt-get"):
            return "apt-rpm", "rpm"
        if which("zypper"):
            return "zypper", "rpm"
        return "rpm", "rpm"
    if has_dpkg and which("apt-get"):
        return "apt", "deb"
    if has_dpkg:
        return "dpkg", "deb"
    if which("dnf"):
        return "dnf", "rpm"
    return "", "rpm"


PKG_MANAGER, PKG_FAMILY = detect_pkg_manager()
DISTRO_NAME = OS_RELEASE.get("PRETTY_NAME") or OS_RELEASE.get("NAME") or "Linux"


def is_root():
    return os.geteuid() == 0


def _privileged(cmd):
    """Оборачивает команду в pkexec/sudo, если мы не root."""
    if is_root():
        return list(cmd)
    if shutil.which("pkexec"):
        return ["pkexec"] + list(cmd)
    if shutil.which("sudo"):
        return ["sudo", "-n"] + list(cmd)
    return list(cmd)


def relaunch_as_root():
    """Перезапускает программу под root через pkexec (один запрос пароля)."""
    pkexec = shutil.which("pkexec")
    if not pkexec:
        return False
    env_keep = []
    for var in ("DISPLAY", "XAUTHORITY", "WAYLAND_DISPLAY", "XDG_RUNTIME_DIR",
                "QT_QPA_PLATFORM", "LANG", "LC_ALL"):
        val = os.environ.get(var)
        if val:
            env_keep.append(f"{var}={val}")
    env_keep.append(f"PKEXEC_UID={os.getuid()}")
    if getattr(sys, "frozen", False):
        target = [sys.executable] + sys.argv[1:]
    else:
        target = [sys.executable, os.path.abspath(__file__)] + sys.argv[1:]
    cmd = [pkexec, "env"] + env_keep + target
    try:
        subprocess.Popen(cmd, cwd=BASE_DIR)
    except OSError:
        return False
    return True


# --- команды пакетного менеджера -------------------------------------------

def pkg_install_repo_cmd(packages):
    p = list(packages)
    if PKG_MANAGER == "dnf":
        # strict=0: если одного имени в репозитории нет, dnf ставит
        # остальные, а не отменяет всю транзакцию. Без этого одна
        # неподходящая строка («Нет соответствия аргументу: freetype.i686»)
        # обнуляла установку всех 16 пакетов разом.
        return ["dnf", "install", "-y", "--setopt=strict=0"] + p
    if PKG_MANAGER == "urpmi":
        return ["urpmi", "--auto"] + p
    if PKG_MANAGER in ("apt-rpm", "apt"):
        return ["apt-get", "install", "-y"] + p
    if PKG_MANAGER == "zypper":
        return ["zypper", "--non-interactive", "install"] + p
    return []


def pkg_remove_cmd(packages):
    p = list(packages)
    if PKG_MANAGER == "dnf":
        return ["dnf", "remove", "-y"] + p
    if PKG_MANAGER == "urpmi":
        return ["urpme", "--auto"] + p
    if PKG_MANAGER in ("apt-rpm", "apt"):
        return ["apt-get", "remove", "-y"] + p
    if PKG_MANAGER == "zypper":
        return ["zypper", "--non-interactive", "remove"] + p
    if PKG_MANAGER == "rpm":
        return ["rpm", "-e"] + p
    if PKG_MANAGER == "dpkg":
        return ["dpkg", "-r"] + p
    return []


def pkg_install_file_cmd(path):
    """Установка локального файла пакета."""
    low = path.lower()
    if low.endswith(".rpm"):
        if PKG_MANAGER == "dnf":
            return ["dnf", "install", "-y", path]
        if PKG_MANAGER == "zypper":
            return ["zypper", "--non-interactive", "install", "--allow-unsigned-rpm", path]
        if PKG_MANAGER == "urpmi":
            return ["urpmi", "--auto", path]
        # Альт (apt-rpm) и «голый» rpm ставят локальный файл напрямую
        return ["rpm", "-Uvh", "--replacepkgs", path]
    if low.endswith(".deb"):
        if PKG_MANAGER == "apt":
            return ["apt-get", "install", "-y", path]
        return ["dpkg", "-i", path]
    return []


def pkg_is_installed(names):
    """Установлен ли хотя бы один из пакетов."""
    for name in names:
        try:
            if PKG_FAMILY == "rpm" and shutil.which("rpm"):
                r = subprocess.run(["rpm", "-q", name], capture_output=True)
            elif shutil.which("dpkg-query"):
                r = subprocess.run(["dpkg-query", "-W", "-f=${Status}", name],
                                   capture_output=True, text=True)
                if r.returncode == 0 and "install ok installed" in (r.stdout or ""):
                    return True
                continue
            else:
                continue
            if r.returncode == 0:
                return True
        except OSError:
            continue
    return False


def app_packages(app):
    """Имена пакетов для текущего дистрибутива.

    "packages" может быть списком (одинаково везде) или словарём:
    {"rpm": [...], "deb": [...], "alt": [...], "rosa": [...], "default": [...]}
    """
    pk = app.get("packages")
    if not pk:
        return []
    if isinstance(pk, str):
        return [pk]
    if isinstance(pk, list):
        return list(pk)
    ident = (OS_RELEASE.get("ID", "") + " " + OS_RELEASE.get("ID_LIKE", "")).lower()
    for key in ("rosa", "alt", "altlinux", "astra", "debian", "ubuntu"):
        if key in ident and pk.get(key):
            v = pk[key]
            return [v] if isinstance(v, str) else list(v)
    for key in (PKG_FAMILY, "default"):
        if pk.get(key):
            v = pk[key]
            return [v] if isinstance(v, str) else list(v)
    return []


def flatpak_available():
    return bool(shutil.which("flatpak"))


# Официальный адрес Flathub во многих школьных сетях заблокирован,
# поэтому список адресов, которые пробуются по очереди. Можно переопределить
# полем "flatpak_repo_urls" в courses.json.
FLATHUB_URLS = [
    "https://dl.flathub.org/repo/flathub.flatpakrepo",
    "https://diallog.pro/downloads/flathub.flatpakrepo",
]


def flatpak_remotes():
    """Список уже подключённых удалённых репозиториев flatpak."""
    if not flatpak_available():
        return []
    out = []
    for scope in (["--system"], ["--user"]):
        try:
            r = subprocess.run(["flatpak", "remotes", "--columns=name"] + scope,
                               capture_output=True, text=True, timeout=30)
            if r.returncode == 0:
                out += [ln.strip() for ln in (r.stdout or "").splitlines() if ln.strip()]
        except (OSError, subprocess.SubprocessError):
            pass
    return out


def ensure_flatpak_remote(name, urls, line, progress, cancel):
    """Подключает репозиторий flatpak, если его ещё нет.

    Пробует адреса по очереди: сначала прямой, затем зеркала. Если прямое
    добавление не проходит (домен заблокирован), файл .flatpakrepo
    скачивается во временную папку и подключается уже локально."""
    if name in flatpak_remotes():
        return True
    line(f"○ Репозиторий «{name}» не подключён — подключаю…", "warn")
    for url in urls:
        line(f"→ Пробую адрес: {url}", "run")
        code = _stream(_privileged(["flatpak", "remote-add", "--if-not-exists",
                                    name, url]), line, progress, cancel)
        if code == -99:
            return False
        if code == 0 and name in flatpak_remotes():
            line(f"✓ Репозиторий «{name}» подключён", "ok")
            return True
        # адрес может быть недоступен для самого flatpak — качаем файл сами
        tmp = os.path.join(SHARE_DIR, f"{name}.flatpakrepo")
        if download_file(url, tmp, line, progress, cancel):
            code = _stream(_privileged(["flatpak", "remote-add", "--if-not-exists",
                                        name, tmp]), line, progress, cancel)
            if code == 0 and name in flatpak_remotes():
                line(f"✓ Репозиторий «{name}» подключён из скачанного файла", "ok")
                return True
    line(f"✗ Не удалось подключить репозиторий «{name}».", "err")
    line("   Подключите вручную (адрес зеркала можно заменить на свой):", "warn")
    line(f'   wget -O flathub.flatpakrepo "{urls[-1]}"', "info")
    line("   sudo flatpak remote-add --if-not-exists flathub flathub.flatpakrepo", "info")
    return False


# Признаки того, что сломан сам flatpak, а не сеть.
_FLATPAK_BROKEN_MARKS = ("flatpak_create_http_session", "CURLM", "assertion failed",
                         "undefined symbol", "symbol lookup error")


def flatpak_health(line=None):
    """Проверяет, работоспособен ли flatpak вообще.

    Возвращает "ok", "broken" (сломана сборка flatpak — обычно несовпадение
    версий libcurl) или "network" (flatpak исправен, но данные не приходят).
    Различать важно: при сломанном flatpak бесполезно менять адреса и
    зеркала, нужно чинить сам пакет."""
    try:
        r = subprocess.run(["flatpak", "remote-ls", "flathub", "--columns=application"],
                           capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as e:
        if line:
            line(f"   flatpak не запускается: {e}", "err")
        return "broken"
    out = (r.stdout or "") + (r.stderr or "")
    if any(mark in out for mark in _FLATPAK_BROKEN_MARKS):
        return "broken"
    if r.returncode == 0 and out.strip():
        return "ok"
    return "network"


def flatpak_repair_commands():
    """Команды починки flatpak под текущий дистрибутив."""
    if PKG_MANAGER == "dnf":
        return [["dnf", "reinstall", "-y", "flatpak"],
                ["dnf", "reinstall", "-y", "libcurl"],
                ["dnf", "update", "-y", "flatpak", "libcurl"]]
    if PKG_MANAGER == "urpmi":
        return [["urpmi", "--auto", "--replacepkgs", "flatpak", "libcurl"]]
    if PKG_MANAGER == "apt-rpm":
        return [["apt-get", "install", "-y", "--reinstall", "flatpak"],
                ["apt-get", "install", "-y", "--reinstall", "libcurl"]]
    if PKG_MANAGER == "apt":
        return [["apt-get", "install", "-y", "--reinstall", "flatpak", "libcurl4"],
                ["apt-get", "update"],
                ["apt-get", "install", "-y", "flatpak"]]
    if PKG_MANAGER == "zypper":
        return [["zypper", "--non-interactive", "install", "--force",
                 "flatpak", "libcurl4"]]
    return []


def check_stray_libcurl(line):
    """Ищет постороннюю libcurl, которая перекрывает системную.

    Частая причина поломки: кто-то собирал софт из исходников, и в
    /usr/local/lib осталась своя библиотека. Программа её не удаляет —
    это решение техника, — но показывает, что нашла."""
    stray = []
    for pat in ("/usr/local/lib/libcurl*", "/usr/local/lib64/libcurl*"):
        stray += sorted(globmod.glob(pat))
    if stray:
        line("⚠ Найдена посторонняя libcurl — скорее всего, причина именно в ней:", "warn")
        for f in stray[:6]:
            line(f"     {f}", "info")
        line("   Она перекрывает системную библиотеку. Если её ставили не вы и "
             "другой программе она не нужна, уберите её:", "info")
        line(f"     sudo mv {os.path.dirname(stray[0])}/libcurl.so* /root/backup-libcurl/",
             "info")
        line("   (папку сначала создайте: sudo mkdir -p /root/backup-libcurl)", "info")
    ldpath = os.environ.get("LD_LIBRARY_PATH")
    if ldpath and "/usr/local" in ldpath:
        line(f"⚠ В LD_LIBRARY_PATH указан /usr/local: {ldpath}. "
             "Это тоже может подсовывать чужие библиотеки.", "warn")
    return stray


class FlatpakRepairWorker(QThread):
    """Чинит flatpak прямо из окна: переустанавливает пакеты и проверяет
    результат, чтобы техник не набирал команды руками."""
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(str)

    def __init__(self):
        super().__init__()
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def _line(self, text, kind="info"):
        self.sig_line.emit(text, kind)

    def run(self):
        self._line("═══ Починка flatpak ═══", "run")
        state = flatpak_health(self._line) if flatpak_available() else "broken"
        if state == "ok":
            self._line("✓ flatpak и так работает — чинить нечего.", "ok")
            self.sig_done.emit("ok")
            return

        check_stray_libcurl(self._line)

        if not flatpak_available():
            self._line("○ flatpak не установлен — ставлю пакет…", "warn")
            cmd = pkg_install_repo_cmd(["flatpak"])
            if cmd:
                _stream(_privileged(cmd), self._line, self.sig_progress.emit,
                        lambda: self._cancel)

        cmds = flatpak_repair_commands()
        if not cmds:
            self._line(f"✗ Не знаю, как чинить в этой системе "
                       f"(менеджер пакетов: {PKG_MANAGER or 'не найден'}).", "err")
            self.sig_done.emit("error")
            return

        self._line("→ Переустанавливаю flatpak и libcurl. Потребуется пароль "
                   "администратора.", "run")
        for cmd in cmds:
            if self._cancel:
                self.sig_done.emit("cancelled")
                return
            code = _stream(_privileged(cmd), self._line,
                           self.sig_progress.emit, lambda: self._cancel)
            if code == -99:
                self.sig_done.emit("cancelled")
                return

        self._line("→ Проверяю результат…", "run")
        state = flatpak_health(self._line)
        if state == "ok":
            self._line("✓ flatpak починился — можно устанавливать программы.", "ok")
            self.sig_done.emit("ok")
            return
        if state == "broken":
            self._line("✗ flatpak всё ещё сломан.", "err")
            if not check_stray_libcurl(self._line):
                self._line("   Посторонних библиотек не видно. Посмотрите, что "
                           "подхватывает flatpak: ldd $(which flatpak) | grep -i curl",
                           "info")
            self.sig_done.emit("broken")
            return
        self._line("○ Сам flatpak теперь исправен, но данные из репозитория не "
                   "приходят — похоже, сеть блокирует Flathub. Используйте бандл "
                   ".flatpak (см. заметку к программе).", "warn")
        self.sig_done.emit("network")


def explain_broken_flatpak(line):
    """Объясняет, как чинить сломанный flatpak."""
    line("✗ Сломан сам flatpak в этой системе, а не сеть и не репозиторий.", "err")
    line("   Ошибка flatpak_create_http_session ... CURLM (код 48) означает, что "
         "flatpak собран под одну версию libcurl, а в системе стоит другая. "
         "До сети дело даже не доходит — поэтому смена адресов и зеркал "
         "ничего не даст.", "warn")
    line("   Как чинить (по порядку):", "info")
    if PKG_FAMILY == "rpm":
        line("     sudo dnf reinstall flatpak libcurl", "info")
        line("     sudo dnf update flatpak libcurl", "info")
    else:
        line("     sudo apt-get install --reinstall flatpak libcurl4", "info")
        line("     sudo apt-get update && sudo apt-get install -y flatpak", "info")
    line("   Проверить, какую libcurl подхватывает flatpak:", "info")
    line("     ldd $(which flatpak) | grep -i curl", "info")
    line("   Если в системе есть посторонняя libcurl (часто в /usr/local/lib) — "
         "чаще всего дело в ней: уберите её из LD_LIBRARY_PATH или удалите.", "info")
    line("   Проверка после починки:  flatpak remote-ls flathub | head", "info")
    line("   Либо просто нажмите «🩹 Починить flatpak» в разделе "
         "«▸ Администрирование» — программа сделает всё это сама.", "warn")


def flatpak_search(query, remote="flathub", limit=8):
    """Ищет программу в подключённом репозитории flatpak.

    Идентификаторы (вроде edu.mit.Scratch) со временем меняются, а проверить
    их заранее нельзя — поэтому спрашиваем сам flatpak на машине техника.
    Возвращает список (название, идентификатор, описание)."""
    if not flatpak_available():
        return []
    try:
        # без метаданных поиск всегда пуст — сначала пробуем их обновить
        subprocess.run(["flatpak", "update", "--appstream", "-y"],
                       capture_output=True, timeout=300)
        r = subprocess.run(
            ["flatpak", "search", "--columns=name,application,description", query],
            capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return []
    out = []
    for ln in (r.stdout or "").splitlines():
        parts = [p.strip() for p in ln.split("\t")]
        if len(parts) >= 2 and "." in parts[1]:
            out.append((parts[0], parts[1], parts[2] if len(parts) > 2 else ""))
    return out[:limit]


def flatpak_resolve_ref(app, remote, line):
    """Проверяет идентификатор из courses.json, а если такого нет —
    подбирает подходящий поиском по названию программы."""
    ref = app.get("flatpak")
    if ref:
        try:
            r = subprocess.run(["flatpak", "remote-info", remote, ref],
                               capture_output=True, timeout=60)
            if r.returncode == 0:
                return ref
        except (OSError, subprocess.SubprocessError):
            return ref
        line(f"⚠ Идентификатора {ref} в репозитории «{remote}» нет — "
             "ищу программу по названию…", "warn")

    query = app.get("flatpak_search") or app["name"]
    found = flatpak_search(query, remote)
    if not found:
        line(f"✗ По запросу «{query}» в репозитории ничего не найдено.", "err")
        return None
    for name, appid, _desc in found:
        if _normalize(name) == _normalize(app["name"]) or \
                _normalize(app["name"]) in _normalize(appid):
            line(f"→ Подобран идентификатор: {appid} ({name})", "info")
            return appid
    line("○ Точного совпадения нет. Найдено в репозитории:", "warn")
    for name, appid, desc in found:
        line(f"   {appid}  —  {name}. {desc[:60]}", "info")
    line("   Впишите нужный идентификатор в поле \"flatpak\" в courses.json.", "warn")
    return None


def flatpak_is_installed(ref):
    if not flatpak_available():
        return False
    try:
        r = subprocess.run(["flatpak", "info", ref], capture_output=True)
        return r.returncode == 0
    except OSError:
        return False


# ---------------------------------------------------------------------------
# Маркеры (для программ без записи в пакетном менеджере)
# ---------------------------------------------------------------------------

def write_marker(app, extra=None):
    ensure_dirs()
    data = {"id": app["id"], "name": app["name"], "installed_at": datetime.now().isoformat()}
    # сохранённую рабочую конфигурацию не затираем: именно к ней
    # возвращается кнопка «↩ Вернуть настройки, при которых работало»
    previous = read_marker(app["id"]).get("working")
    if previous:
        data["working"] = previous
    if extra:
        data.update(extra)
    try:
        path = os.path.join(MARKERS_DIR, f"{app['id']}.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        _chown_to_user(path)
    except OSError:
        pass


def read_marker(app_id):
    p = os.path.join(MARKERS_DIR, f"{app_id}.json")
    if os.path.exists(p):
        try:
            with open(p, encoding="utf-8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return {}
    return {}


def remove_marker(app_id):
    p = os.path.join(MARKERS_DIR, f"{app_id}.json")
    if os.path.exists(p):
        try:
            os.remove(p)
            return True
        except OSError:
            pass
    return False


# ---------------------------------------------------------------------------
# Проверка «установлено ли»
# ---------------------------------------------------------------------------

def check_installed(app, cache=None):
    chk = app.get("check") or {}
    ctype = chk.get("type", "marker")
    if ctype == "package":
        names = chk.get("packages") or app_packages(app)
        return pkg_is_installed(names) if names else False
    if ctype == "command":
        names = chk.get("names") or ([chk["name"]] if chk.get("name") else [])
        return any(shutil.which(n) for n in names)
    if ctype == "path":
        path = os.path.expandvars(os.path.expanduser(chk.get("path", "")))
        return bool(path) and os.path.exists(path)
    if ctype == "glob":
        pattern = os.path.expandvars(os.path.expanduser(chk.get("pattern", "")))
        return bool(pattern) and bool(globmod.glob(pattern))
    if ctype == "flatpak":
        return flatpak_is_installed(chk.get("ref") or app.get("flatpak", ""))
    return os.path.exists(os.path.join(MARKERS_DIR, f"{app['id']}.json"))


def _resolve_installer_file(app):
    """(путь, использован_ли_запасной_вариант).

    Если файла с точным именем нет, но в папке лежит единственный файл с тем
    же расширением — берём его (сайты часто добавляют версию в имя файла)."""
    rel = app.get("file")
    if not rel:
        return None, False
    configured = rel if os.path.isabs(rel) else os.path.join(INSTALLERS_DIR, rel)
    if os.path.exists(configured):
        return configured, False
    d = os.path.dirname(configured)
    if not os.path.isdir(d):
        return None, False
    low = configured.lower()
    ext = None
    for e in ARCHIVE_EXTS:
        if low.endswith(e):
            ext = e
            break
    if ext is None:
        ext = os.path.splitext(configured)[1]
    if ext:
        candidates = sorted(globmod.glob(os.path.join(d, f"*{ext}")))
        # Если версий несколько, берём ту, что указана как проверенная.
        # Например у Algodoo 2.1.0 Win32 работает, а свежая 2.2.4 x64 — нет.
        prefer = app.get("file_prefer") or []
        if len(candidates) > 1 and prefer:
            for pattern in prefer:
                liked = [c for c in candidates
                         if re.search(pattern, os.path.basename(c), re.I)]
                if liked:
                    return sorted(liked)[0], True
        if len(candidates) == 1:
            return candidates[0], True
    # запасной вариант: единственный файл в папке вообще (кроме подсказки)
    files = [f for f in sorted(globmod.glob(os.path.join(d, "*")))
             if os.path.isfile(f) and not f.endswith(".txt")]
    if len(files) == 1:
        return files[0], True
    return None, False


# ---------------------------------------------------------------------------
# Ярлыки (.desktop в меню приложений)
# ---------------------------------------------------------------------------

def desktop_path(app_id):
    return os.path.join(DESKTOP_DIR, f"koderlab-{app_id}.desktop")


def _esc(s):
    return str(s).replace("\n", " ")


def create_desktop_entry(app_id, name, exec_cmd, icon=None, comment="", workdir=None,
                         categories="Education;"):
    ensure_dirs()
    path = desktop_path(app_id)
    lines = [
        "[Desktop Entry]",
        "Type=Application",
        f"Name={_esc(name)}",
        f"Exec={exec_cmd}",
        "Terminal=false",
        f"Categories={categories}",
        "X-KoderLab=true",
    ]
    if comment:
        lines.append(f"Comment={_esc(comment)[:160]}")
    if icon:
        lines.append(f"Icon={icon}")
    if workdir:
        lines.append(f"Path={workdir}")
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
        os.chmod(path, 0o755)
        _chown_to_user(path)
    except OSError:
        return None
    try:
        subprocess.run(["update-desktop-database", DESKTOP_DIR],
                       capture_output=True, timeout=20)
    except (OSError, subprocess.SubprocessError):
        pass
    return path


def remove_desktop_entry(app_id):
    path = desktop_path(app_id)
    if os.path.exists(path):
        try:
            os.remove(path)
            return True
        except OSError:
            pass
    return False


def shell_quote(s):
    return "'" + str(s).replace("'", "'\\''") + "'"


LAUNCHER_DESKTOP_NAME = "koderlab-launcher.desktop"


def _user_desktop_dir():
    """Папка «Рабочий стол» пользователя.

    Имя папки разное в зависимости от языка системы (Desktop, Рабочий
    стол…), поэтому сперва спрашиваем xdg-user-dir — он знает настоящее
    имя из ~/.config/user-dirs.dirs."""
    try:
        r = subprocess.run(["xdg-user-dir", "DESKTOP"], capture_output=True,
                           text=True, timeout=5)
        path = (r.stdout or "").strip()
        if r.returncode == 0 and path and os.path.isdir(path):
            return path
    except (OSError, subprocess.SubprocessError):
        pass
    for name in ("Desktop", "Рабочий стол"):
        cand = os.path.join(USER_HOME, name)
        if os.path.isdir(cand):
            return cand
    return None


KODERLAB_ICON = os.path.join(ICONS_DIR, "koderlab.png")
KODERLAB_TITLE = "ИТ ШКОЛА KoderLab - ПО"
KODERLAB_VERSION = "1.1.4"


def _koderlab_icon():
    """Значок программы для заголовка окна и панели задач: настоящий логотип
    из icons/koderlab.png, если он есть, иначе — цветной аватар с буквами."""
    if os.path.exists(KODERLAB_ICON):
        pix = QPixmap(KODERLAB_ICON)
        if not pix.isNull():
            return QIcon(pix)
    return QIcon(_avatar_pixmap(KODERLAB_TITLE, 64))


def ensure_launcher_shortcut():
    """Ярлык для самого установщика: в меню приложений и на рабочий стол.

    Чтобы открыть программу можно было двойным кликом, без терминала и
    без ./start.sh руками."""
    exec_cmd = shell_quote(os.path.join(BASE_DIR, "start.sh"))
    icon = KODERLAB_ICON if os.path.exists(KODERLAB_ICON) else "system-software-install"
    title = KODERLAB_TITLE
    try:
        with open(COURSES_FILE, encoding="utf-8") as f:
            title = json.load(f).get("title") or KODERLAB_TITLE
    except (OSError, ValueError):
        pass
    content = "\n".join([
        "[Desktop Entry]",
        "Type=Application",
        f"Name={_esc(title)}",
        "Comment=Установка и запуск учебных программ KoderLab",
        f"Exec={exec_cmd}",
        "Terminal=false",
        "Categories=Education;",
        f"Icon={icon}",
        "X-KoderLab=true",
        f"Path={BASE_DIR}",
    ]) + "\n"

    targets = [os.path.join(DESKTOP_DIR, LAUNCHER_DESKTOP_NAME)]
    desk_dir = _user_desktop_dir()
    if desk_dir:
        targets.append(os.path.join(desk_dir, LAUNCHER_DESKTOP_NAME))

    if desk_dir is None:
        print("KoderLab: не нашёл папку «Рабочий стол» (xdg-user-dir DESKTOP "
              "не ответил и ни ~/Desktop, ни ~/Рабочий стол не существуют) — "
              "ярлык на стол не создан, только в меню приложений.")

    for path in targets:
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
            os.chmod(path, 0o755)
            _chown_to_user(path)
            # Без этой пометки часть файловых менеджеров (Nautilus/GNOME)
            # показывает ярлык на рабочем столе как «недоверенный» и не
            # запускает его по двойному клику, пока не подтвердишь вручную
            # (правой кнопкой → «Разрешить запуск» / «Allow Launching»,
            # если после этой пометки предупреждение всё равно осталось).
            try:
                r = subprocess.run(["gio", "set", path, "metadata::trusted", "true"],
                                   capture_output=True, text=True, timeout=10)
                if r.returncode != 0:
                    print(f"KoderLab: gio set trusted для {path} вернул "
                          f"код {r.returncode}: {(r.stderr or '').strip()}")
            except FileNotFoundError:
                print("KoderLab: команда gio не найдена — ярлык создан, но "
                      "файловый менеджер может пометить его «недоверенным» "
                      "до ручного разрешения (правой кнопкой по ярлыку).")
            except (OSError, subprocess.SubprocessError) as e:
                print(f"KoderLab: gio set trusted для {path} не выполнился: {e}")
        except OSError as e:
            print(f"KoderLab: не удалось создать ярлык {path}: {e}")
            continue

    try:
        subprocess.run(["update-desktop-database", DESKTOP_DIR],
                       capture_output=True, timeout=20)
    except (OSError, subprocess.SubprocessError):
        pass


def cmd_for_log(cmd, env_extra=None):
    """Команда в виде, пригодном для копирования в терминал.

    Пути с пробелами и скобками (например «Program Files (x86)») без кавычек
    bash не принимает — техник копирует строку из журнала и получает
    «синтаксическая ошибка рядом с неожиданным маркером «(»»."""
    parts = []
    for k, v in sorted((env_extra or {}).items()):
        if k in ("DISPLAY", "PATH"):      # шум, и так есть в сеансе
            continue
        parts.append(f"{k}={shell_quote(v)}")
    for c in cmd:
        c = str(c)
        parts.append(c if re.fullmatch(r"[\w@%+=:,./-]+", c) else shell_quote(c))
    return " ".join(parts)


# ---------------------------------------------------------------------------
# Java (для .jar-программ вроде TLauncher)
# ---------------------------------------------------------------------------

# Минимальная версия Java. TLauncher со сборкой 11 не стартует — нужна 17+
# (проверено на практике).
JAVA_MIN_VERSION = 17


def java_version(java_path):
    """Основной номер версии Java (17, 21, …) или None."""
    if not java_path or not os.path.exists(java_path):
        return None
    try:
        r = subprocess.run([java_path, "-version"], capture_output=True,
                           text=True, timeout=30)
        text = (r.stderr or "") + (r.stdout or "")
    except (OSError, subprocess.SubprocessError):
        return None
    m = re.search(r'version\s+"?(\d+)(?:\.(\d+))?', text)
    if not m:
        return None
    major = int(m.group(1))
    if major == 1 and m.group(2):      # старый формат: 1.8.0 = Java 8
        return int(m.group(2))
    return major


def java_has_gui(java_path):
    """Умеет ли эта Java рисовать окна.

    В репозиториях есть «headless»-варианты без графики: команда java есть,
    версия печатается, но при запуске окна программа падает с
    UnsatisfiedLinkError ... libawt_xawt.so. Проверяем наличие этой
    библиотеки рядом с самой java."""
    try:
        real = os.path.realpath(java_path)
        jvm_home = os.path.dirname(os.path.dirname(real))
        return bool(globmod.glob(os.path.join(jvm_home, "lib", "**", "libawt_xawt.so"),
                                 recursive=True))
    except OSError:
        return False


def java_is_suitable(java_path):
    """Java годится, если умеет рисовать окна И не старее JAVA_MIN_VERSION."""
    if not java_has_gui(java_path):
        return False
    v = java_version(java_path)
    return v is None or v >= JAVA_MIN_VERSION


def all_javas():
    """Все найденные в системе java, сначала подходящие."""
    found = []
    seen = set()
    for cand in ([shutil.which("java")]
                 + ([os.path.join(os.environ["JAVA_HOME"], "bin", "java")]
                    if os.environ.get("JAVA_HOME") else [])
                 + sorted(globmod.glob("/usr/lib/jvm/*/bin/java"))
                 + sorted(globmod.glob("/usr/lib64/jvm/*/bin/java"))
                 + sorted(globmod.glob("/opt/*/bin/java"))):
        if cand and os.path.exists(cand):
            real = os.path.realpath(cand)
            if real not in seen:
                seen.add(real)
                found.append(cand)
    found.sort(key=lambda j: (not java_is_suitable(j), -(java_version(j) or 0), j))
    return found


def find_java(need_gui=True):
    """Java для запуска программ.

    По умолчанию возвращает только полностью подходящую: с графикой и не
    старее JAVA_MIN_VERSION. Java 11 формально рабочая, но TLauncher на ней
    не стартует, поэтому такой вариант не годится."""
    javas = all_javas()
    if not javas:
        return None
    if need_gui:
        for j in javas:
            if java_is_suitable(j):
                return j
        return None
    return javas[0]


# ---------------------------------------------------------------------------
# Запуск команд с живым выводом
# ---------------------------------------------------------------------------

def _run_env():
    env = dict(os.environ)
    env["DEBIAN_FRONTEND"] = "noninteractive"
    env.setdefault("LANG", "C.UTF-8")
    return env


# Предел на число показываемых строк вывода одной команды снят по просьбе:
# вывод показывается целиком. float("inf") означает, что условие «строк
# слишком много» не срабатывает никогда, а счётчик скрытых строк всегда
# остаётся нулевым.
MAX_LOG_LINES = float("inf")


def _stream(cmd, line, progress, cancel_check, cwd=None):
    shown_cmd = cmd_for_log(cmd) if isinstance(cmd, (list, tuple)) else str(cmd)
    line("$ " + shown_cmd, "cmd")
    try:
        proc = subprocess.Popen(
            cmd, cwd=cwd, env=_run_env(),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
            text=True, encoding="utf-8", errors="replace", bufsize=1,
        )
    except FileNotFoundError as e:
        line(f"✗ Команда не найдена: {e}", "err")
        return 127
    except OSError as e:
        line(f"✗ Не удалось запустить: {e}", "err")
        return 1

    q = queue.Queue()

    def reader():
        try:
            for raw in proc.stdout:
                q.put(raw)
        except (OSError, ValueError):
            pass
        q.put(None)

    threading.Thread(target=reader, daemon=True).start()

    last_text, repeats, shown, hidden = None, 0, 0, 0
    while True:
        if cancel_check():
            try:
                proc.terminate()
            except OSError:
                pass
            line("⚠ Отменено пользователем", "warn")
            return -99
        try:
            item = q.get(timeout=0.15)
        except queue.Empty:
            if proc.poll() is not None:
                break
            continue
        if item is None:
            break
        text = _clean(item.rstrip("\n"))
        if not text.strip():
            continue
        # одинаковые строки подряд не засоряют журнал
        if text == last_text:
            repeats += 1
            continue
        if repeats:
            line(f"   (предыдущая строка повторилась ещё {repeats} раз)", "info")
            repeats = 0
        last_text = text
        # предел на объём вывода: иначе окно съедает память
        if shown < MAX_LOG_LINES:
            line(text, "info")
            shown += 1
            if shown == MAX_LOG_LINES:
                line("   … дальше вывод этой команды не показываю: строк "
                     "слишком много. Команда продолжает работать.", "warn")
        else:
            hidden += 1
            if hidden % 2000 == 0:
                progress(f"Программа выдала уже {shown + hidden} строк…")

    if repeats:
        line(f"   (предыдущая строка повторилась ещё {repeats} раз)", "info")
    if hidden:
        line(f"   (скрыто ещё {hidden} строк вывода)", "info")
    proc.wait()
    return proc.returncode


def real_user():
    """Имя, домашняя папка и uid настоящего пользователя, даже если программа
    запущена через sudo/pkexec. (None, None), если мы и так не root."""
    info = real_user_info()
    return (info[0], info[1]) if info else (None, None)


def real_user_info():
    """(имя, домашняя папка, uid) или None."""
    if not is_root():
        return None
    import pwd
    uid = os.environ.get("PKEXEC_UID")
    name = os.environ.get("SUDO_USER")
    try:
        if uid:
            pw = pwd.getpwuid(int(uid))
        elif name:
            pw = pwd.getpwnam(name)
        else:
            return None
        if pw.pw_uid == 0 or not os.path.isdir(pw.pw_dir):
            return None
        return pw.pw_name, pw.pw_dir, pw.pw_uid
    except (KeyError, ValueError, TypeError):
        return None


def _already_as_user(cmd):
    """Команда уже обёрнута в runuser/sudo?"""
    if not cmd:
        return False
    first = os.path.basename(str(cmd[0]))
    return first in ("runuser", "sudo", "pkexec")


def user_session_env(uid):
    """Достаёт переменные графического сеанса пользователя из /proc.

    Когда установщик запущен через sudo, переменные DISPLAY, XAUTHORITY и
    DBUS_SESSION_BUS_ADDRESS в его окружении либо чужие, либо отсутствуют.
    Угадывать бесполезно: на Astra, например, файл авторизации X лежит не в
    ~/.Xauthority, а в /tmp/xauth_XXXXXX. Поэтому берём настоящие значения у
    любого уже работающего процесса этого пользователя.

    Без этого программы не могут ни открыть окно («no driver could be
    loaded»), ни подключиться к шине D-Bus — именно на этом падали Scratch
    и Roblox Studio."""
    wanted = ("DISPLAY", "XAUTHORITY", "DBUS_SESSION_BUS_ADDRESS",
              "WAYLAND_DISPLAY", "XDG_SESSION_TYPE", "XDG_CURRENT_DESKTOP")
    best = {}
    try:
        pids = [d for d in os.listdir("/proc") if d.isdigit()]
    except OSError:
        return best
    for pid in pids:
        path = f"/proc/{pid}"
        try:
            if os.stat(path).st_uid != uid:
                continue
            with open(f"{path}/environ", "rb") as f:
                raw = f.read()
        except (OSError, PermissionError):
            continue
        env = {}
        for part in raw.split(b"\0"):
            if b"=" in part:
                k, _, v = part.partition(b"=")
                try:
                    env[k.decode()] = v.decode()
                except UnicodeDecodeError:
                    continue
        if "DISPLAY" not in env and "WAYLAND_DISPLAY" not in env:
            continue
        cand = {k: env[k] for k in wanted if env.get(k)}
        # чем больше нужных переменных нашлось, тем правдоподобнее сеанс
        if len(cand) > len(best):
            best = cand
            if "DBUS_SESSION_BUS_ADDRESS" in cand and "XAUTHORITY" in cand:
                break
    return best


def _as_user(cmd, env_extra=None):
    """Запуск от имени настоящего пользователя, а не root.

    Это принципиально для Wine (он отказывается работать с чужим префиксом:
    «is not owned by you») и для браузеров на движке Chromium (они не
    запускаются под root без --no-sandbox). Заодно кэш winetricks попадает
    в домашнюю папку пользователя, а не в /root/.cache."""
    info = real_user_info()
    if not info or _already_as_user(cmd):
        return list(cmd)
    user, home, uid = info
    helper = shutil.which("runuser") or shutil.which("sudo")
    if not helper:
        return list(cmd)
    runtime = f"/run/user/{uid}"
    envs = [f"HOME={home}", f"USER={user}", f"LOGNAME={user}",
            f"XDG_RUNTIME_DIR={runtime}"]

    # настоящие переменные сеанса важнее того, что оказалось в нашем окружении
    session = user_session_env(uid)
    for var in ("DISPLAY", "WAYLAND_DISPLAY", "XAUTHORITY",
                "XDG_SESSION_TYPE", "XDG_CURRENT_DESKTOP",
                "DBUS_SESSION_BUS_ADDRESS"):
        val = session.get(var) or os.environ.get(var)
        if val:
            envs.append(f"{var}={val}")
    for var in ("LANG", "LC_ALL"):
        val = os.environ.get(var)
        if val:
            envs.append(f"{var}={val}")

    have = {e.split("=", 1)[0] for e in envs}
    if "XAUTHORITY" not in have and home:
        # запасные варианты: обычный файл и то, что кладёт дисплейный менеджер
        for cand in [os.path.join(home, ".Xauthority")] + \
                sorted(globmod.glob("/tmp/xauth_*")) + \
                sorted(globmod.glob(f"{runtime}/gdm/Xauthority")):
            try:
                if os.path.exists(cand) and os.stat(cand).st_uid == uid:
                    envs.append(f"XAUTHORITY={cand}")
                    break
            except OSError:
                continue
    # flatpak и Wine без шины D-Bus ведут себя непредсказуемо
    if "DBUS_SESSION_BUS_ADDRESS" not in have and os.path.exists(f"{runtime}/bus"):
        envs.append(f"DBUS_SESSION_BUS_ADDRESS=unix:path={runtime}/bus")
    # flatpak ищет программы пользователя здесь
    envs.append(f"XDG_DATA_DIRS={home}/.local/share/flatpak/exports/share:"
                "/var/lib/flatpak/exports/share:/usr/local/share:/usr/share")
    for k, v in (env_extra or {}).items():
        envs.append(f"{k}={v}")
    if helper.endswith("runuser"):
        return [helper, "-u", user, "--", "env"] + envs + list(cmd)
    return [helper, "-u", user, "env"] + envs + list(cmd)


def _launch_env(extra=None):
    env = dict(os.environ)
    env.pop("PKEXEC_UID", None)
    # чтобы в журнале были видны настоящие сообщения об ошибках, а не «Ошибка»
    env["LC_ALL"] = env.get("LC_ALL") or "C.UTF-8"
    if extra:
        # LC_ALL=C ломает пути с кириллицей («Рабочий стол»): Wine перестаёт
        # видеть файлы. Нужна английская локаль, но с кодировкой UTF-8.
        fixed = {}
        for k, v in extra.items():
            v = str(v)
            if k in ("LC_ALL", "LANG") and v.upper() in ("C", "POSIX"):
                v = "C.UTF-8"
            fixed[k] = v
        env.update(fixed)
    return env


# Подсказки по типичным ошибкам запуска — чтобы техник не гуглил текст ошибки.
LAUNCH_HINTS = [
    ("fusermount", "Нет FUSE — установите пакет fuse (ROSA: sudo dnf install fuse; "
                   "Альт: sudo apt-get install fuse). Или запустите AppImage с ключом "
                   "--appimage-extract-and-run."),
    ("libfuse.so.2", "Нет библиотеки libfuse2 — установите пакет fuse (или fuse-libs)."),
    ("libGL", "Нет графических библиотек OpenGL — установите mesa-libGL "
              "(ROSA: sudo dnf install mesa-libGL; Альт: sudo apt-get install libGL)."),
    ("libnss3", "Не хватает libnss3 — установите пакет libnss3 / nss."),
    ("error while loading shared libraries",
     "Не хватает системной библиотеки — её точное имя написано в строке выше, "
     "найдите пакет: ROSA — sudo dnf provides '*/имя.so*', Альт — apt-cache search имя."),
    ("Permission denied", "Нет прав на запуск файла: chmod +x путь_к_файлу."),
    ("No such file or directory",
     "Файл запуска не найден — возможно, программу удалили вручную. "
     "Нажмите «Удалить», затем «Установить» заново."),
    ("java: not found", "Не установлена Java — поставьте java-17-openjdk (ROSA/Альт) "
                        "или openjdk-17-jre (Astra/Debian)."),
    ("UnsupportedClassVersionError", "Версия Java слишком старая для этой программы — "
                                     "поставьте java-17-openjdk."),
    ("wine: cannot find", "Wine не нашёл файл программы внутри своего окружения — "
                          "переустановите программу кнопкой «Удалить» → «Установить»."),
    ("XNA", "Не установлен Microsoft XNA внутри Wine — нужен winetricks: "
            "WINEPREFIX=… winetricks -q xna40."),
    ("could not be started", "Программа не запустилась внутри Wine. Проверьте в "
                             "«🍷 Настройки Wine», что стоят нужные компоненты "
                             "(для Algodoo — corefonts и vcrun2008)."),
    ("page fault on read access to 0x00000000", "Программа на .NET упала на "
                                                "обращении к пустой ссылке. Для Kodu "
                                                "это обычно запрос сведений о "
                                                "железе через WMI, на который Wine "
                                                "отвечает не полностью. Попробуйте "
                                                "⚙ → «Kodu: режим winxp», затем "
                                                "«Kodu: сбросить настройки графики»."),
    ("in clr (", "Сбой внутри .NET. Проверьте, что компоненты установлены: "
                 "⚙ → «Kodu: что установлено в окружении». Если dotnet48 и xna40 "
                 "на месте — дело в самой программе под Wine, см. подсказки ниже."),
    ("Invalid range header", "Сервер (обычно веб-архив) не умеет отдавать файл "
                             "по частям. Установщик теперь качает такие файлы "
                             "сам, одним потоком. Если ошибка осталась — "
                             "положите нужный файл в installers/<программа>/."),
    ("cannot find the FreeType", "В системе нет 32-битных библиотек, которые "
                                 "нужны 32-битному Wine. Установщик ставит их "
                                 "сам; если сообщение осталось, выполните: "
                                 "sudo dpkg --add-architecture i386 && "
                                 "sudo apt-get update && sudo apt-get install "
                                 "libfreetype6:i386 libx11-6:i386 libgl1:i386"),
    ("returned status 67", "Установщик .NET отказался ставиться. Почти всегда "
                           "причина в том, что окружение Wine 64-битное: .NET "
                           "для Kodu ставится только в 32-битное. Нужна сборка "
                           "Wine без wow64 в названии."),
    ("neither on the path nor an executable", "winetricks не видит используемую "
                                              "сборку Wine. Исправлено передачей "
                                              "переменной WINE — если сообщение "
                                              "появилось снова, сбросьте окружение "
                                              "и установите программу заново."),
    ("not supported in wow64 mode", "Эта сборка Wine не умеет создавать "
                                    "32-битные окружения. Нужна сборка БЕЗ слова "
                                    "wow64 в названии, либо системный wine32. "
                                    "Установщик подберёт подходящую сам, если она "
                                    "есть в системе."),
    ("syswow64", "Окружение Wine собрано неправильно: 64-битная сборка без "
                 "32-битной части. Сбросьте окружение («🍷 Настройки Wine» → "
                 "«Сбросить») и установите программу заново — подходящая сборка "
                 "Wine будет выбрана автоматически."),
    ("Bad EXE format", "Разрядность окружения Wine не совпадает с программой: "
                       "64-битную программу нельзя запустить в 32-битном окружении. "
                       "Откройте «🍷 Настройки Wine», нажмите «Сбросить» для этой "
                       "программы и установите её заново — разрядность определится "
                       "автоматически."),
    ("NullReferenceException", "Программа на .NET использует встроенный Mono вместо "
                               "настоящего .NET. Для Kodu: winetricks dotnet48 и xna40 "
                               "(именно в таком порядке, ДО установки самой Kodu), "
                               "версия Windows win7 и Wine не ниже 9.2."),
    ("wine-mono", "Внутри Wine используется Mono вместо настоящего .NET — из-за этого "
                  "программа и падает. Установите dotnet48 («🍷 Настройки Wine» → "
                  "компоненты) и переустановите программу."),
    ("XnaNative", "Не найдена XnaNative.dll. На Wine старее 9.2 её приходится копировать "
                  "вручную в папку программы; правильнее обновить Wine — "
                  "«⬇ Скачать свежий Wine…»."),
    ("libawt_xawt", "Установлена «headless» Java без графики. Поставьте полный пакет: "
                    "sudo dnf install java-11-openjdk (или java-17-openjdk)."),
    ("UnsatisfiedLinkError", "Java не может загрузить графические библиотеки — "
                             "установлен вариант без GUI. Поставьте java-11-openjdk "
                             "или java-17-openjdk (не -headless)."),
    ("Cannot open display", "Нет доступа к графическому экрану — программу нельзя "
                            "запускать по SSH без графики."),
    ("суперпользовател", "Программа отказывается работать от имени root. "
                         "Закройте установщик и запустите его обычным пользователем: "
                         "./start.sh без sudo."),
    ("as root", "Программа отказывается работать от имени root. Запустите "
                "установщик обычным пользователем: ./start.sh без sudo."),
    ("run as superuser", "Программа отказывается работать от имени root. "
                         "Запустите установщик без sudo."),
    ("Running as root", "Программа отказывается работать от имени root. "
                        "Запустите установщик без sudo."),
    ("flatpak_create_http_session", "Сломан сам flatpak: несовпадение версий "
                                    "libcurl. Переустановите пакеты flatpak и "
                                    "libcurl, зеркала тут не помогут."),
    ("CURLM", "Сломан flatpak или libcurl — переустановите оба пакета."),
    ("Roblox was killed", "Studio был завершён другим запуском Vinegar. Так бывает, "
                          "если нажать «Запустить» второй раз, пока программа уже "
                          "работает: при входе в аккаунт это обрывает авторизацию. "
                          "Запускайте один раз, а зависшее закрывайте через "
                          "«⚙ → Остановить Roblox»."),
    ("Failed to register with GameMode", "GameMode не установлен — это не ошибка, "
                                         "программа работает и без него."),
    ("Failed to connect to session bus", "Программа не видит шину D-Bus сеанса. "
                                        "Это чинится само, если запускать установщик "
                                        "без sudo. Если запускаете через sudo — "
                                        "обновитесь: свежая версия сама подхватывает "
                                        "переменные сеанса пользователя."),
    ("no driver could be loaded", "Программа внутри Wine не смогла открыть окно: "
                                  "не дошли DISPLAY и XAUTHORITY. Запустите "
                                  "установщик обычным пользователем (без sudo)."),
    ("DRI3 error", "Нет аппаратного ускорения графики (DRI3). Программа будет "
                   "работать медленно. Проверьте драйверы видеокарты."),
    ("Failed to connect to bus", "Нет доступа к шине D-Bus сеанса. Так бывает, когда "
                                 "установщик запущен через sudo. Запустите ./start.sh "
                                 "обычным пользователем."),
    ("Permission denied (bus)", "Нет доступа к шине D-Bus — запустите установщик "
                                "без sudo."),
]


# Строки, которые засоряют журнал и ничего не говорят о работе программы.
_NOISE_PATTERNS = (
    "Vulnerability found: oval:",          # сканер уязвимостей Astra
    "Failed to set PDP label",             # мандатные метки Astra внутри flatpak
    "Failed to get PDP label",
    "fixme:",                              # заглушки Wine
    "winemenubuilder.exe",
    "ZwLoadDriver failed to create driver",
    "Unsupported style(s) 0x10",
    "for device L\"ROOT\\WINE\\WINEBTH\"",
    "WerRegisterCustomMetadata",
    "RecursiveDirectoryCreate",             # Vinegar сообщает о каждой папке
    "/tmp/flatpak-scanner/results/",        # сканер Astra и его битый XML
    "Failed to parse /tmp/flatpak-scanner",
    "Check that it is valid to prevent",
    "Theme parsing error",
    "D3D11DXGIDevice::QueryInterface",
    "MakeWindowAssociation: Ignoring flags",
    "wined3d_dll_init Using the Vulkan renderer",
    "CreateSwapChainForComposition",
    "не находятся по пути поиска",          # подсказка flatpak про XDG_DATA_DIRS
    "exports/share'",
)


def is_noise_line(text):
    return any(p in text for p in _NOISE_PATTERNS)


def hints_for(text):
    out = []
    for needle, hint in LAUNCH_HINTS:
        if needle.lower() in text.lower() and hint not in out:
            out.append(hint)
    return out


# ---------------------------------------------------------------------------
# Распаковка архивов
# ---------------------------------------------------------------------------

def extract_archive(src, dest_dir):
    low = src.lower()
    if low.endswith(".zip"):
        with zipfile.ZipFile(src) as z:
            z.extractall(dest_dir)
            # zipfile теряет права на запуск — возвращаем их из атрибутов архива,
            # иначе распакованную Linux-программу нельзя будет запустить
            for info in z.infolist():
                mode = info.external_attr >> 16
                if mode:
                    path = os.path.join(dest_dir, info.filename)
                    if os.path.exists(path):
                        try:
                            os.chmod(path, mode)
                        except OSError:
                            pass
        return
    with tarfile.open(src, "r:*") as t:
        t.extractall(dest_dir)


def _find_executable_in(dest_dir, app_id, app, hint=None):
    """Ищет исполняемый файл внутри распакованной папки."""
    if hint:
        matches = globmod.glob(os.path.join(dest_dir, "**", hint), recursive=True)
        if matches:
            return matches[0]
    cands = []
    for path in globmod.glob(os.path.join(dest_dir, "**", "*"), recursive=True):
        if not os.path.isfile(path):
            continue
        name = os.path.basename(path)
        if name.lower().endswith((".so", ".dll", ".txt", ".md", ".png", ".svg",
                                  ".json", ".dat", ".pak", ".xml", ".desktop",
                                  ".exe", ".bat", ".cmd", ".msi")):
            continue
        if os.access(path, os.X_OK) or name.lower().endswith(".appimage"):
            cands.append(path)
    if not cands:
        # права на запуск могли потеряться (архив собран на Windows) —
        # ищем по имени: файл без «данных» в расширении, похожий на программу
        keys0 = [_normalize(k) for k in _app_keywords(app_id, app)]
        for path in globmod.glob(os.path.join(dest_dir, "**", "*"), recursive=True):
            if not os.path.isfile(path):
                continue
            name = os.path.basename(path)
            if "." in name and not name.lower().endswith((".sh", ".x86_64", ".bin", ".run")):
                continue
            if any(k and k in _normalize(name) for k in keys0):
                return path
        return None
    keys = [_normalize(k) for k in _app_keywords(app_id, app)]
    for c in cands:
        norm = _normalize(os.path.basename(c))
        if any(k and k in norm for k in keys):
            return c
    # чем ближе к корню распакованной папки, тем вероятнее это главный файл
    cands.sort(key=lambda p: (p.count(os.sep), len(p)))
    return cands[0] if len(cands) == 1 or cands else None


# ---------------------------------------------------------------------------
# Установщики
# ---------------------------------------------------------------------------

class BaseInstaller:
    def is_installed(self, app, cache=None):
        return check_installed(app, cache)

    def launch_cmd(self, app):
        """Возвращает (команда, рабочая_папка, доп_переменные_окружения, ошибка).

        Запуском занимается LaunchWorker — он показывает весь вывод программы
        и её ошибки прямо в журнале окна."""
        m = read_marker(app["id"])
        cmd = m.get("exec")
        if cmd:
            cmd = cmd if isinstance(cmd, list) else [cmd]
            if not os.path.exists(cmd[0]) and not shutil.which(cmd[0]):
                return None, None, None, (
                    f"файл запуска не найден: {cmd[0]}. "
                    "Нажмите «Удалить», затем «Установить» заново.")
            return cmd, m.get("workdir"), m.get("env"), None
        for name in (app.get("run_bin"), app.get("id")):
            path = shutil.which(name) if name else None
            if path:
                return [path], None, None, None
        return None, None, None, (
            "не удалось определить команду запуска. Если программа установлена, "
            "запустите её из меню приложений (раздел «Образование»).")


def _file_missing(app, line):
    line(f"✗ Файл не найден: {app.get('file')}", "err")
    line(f"   Положите файл сюда: installers/{app['id']}/", "warn")


# ---------------------------------------------------------------------------
# Автоматическое скачивание файла (прямая ссылка или релиз с GitHub)
# ---------------------------------------------------------------------------

GH_LAST_ERROR = ""


def _gh_api(url, line=None):
    """Запрос к API GitHub. Возвращает разобранный JSON или None.
    Текст последней ошибки остаётся в GH_LAST_ERROR."""
    global GH_LAST_ERROR
    GH_LAST_ERROR = ""
    try:
        req = urllib.request.Request(url, headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": "KoderLab-Installer",
        })
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        remaining = e.headers.get("X-RateLimit-Remaining")
        reset = e.headers.get("X-RateLimit-Reset")
        if e.code in (403, 429) and remaining == "0":
            when = ""
            try:
                when = datetime.fromtimestamp(int(reset)).strftime(" (примерно в %H:%M)")
            except (TypeError, ValueError):
                pass
            GH_LAST_ERROR = (
                "GitHub временно ограничил обращения с этого адреса: без входа в "
                f"аккаунт разрешено 60 запросов в час, лимит исчерпан{when}. "
                "Учтите, что все компьютеры школы выходят в интернет под одним "
                "адресом, поэтому лимит общий на всех.\n\n"
                "Что делать: подождать, либо скачать файл вручную со страницы "
                "релизов, либо (самое надёжное) подготовить папку на одном "
                "компьютере и раздать её по локальной сети — тогда остальным "
                "ПК интернет вообще не нужен.")
        elif e.code == 404:
            GH_LAST_ERROR = ("Такого репозитория нет — проверьте написание "
                             "«владелец/репозиторий».")
        else:
            GH_LAST_ERROR = f"GitHub ответил ошибкой {e.code}: {e.reason}"
    except Exception as e:
        GH_LAST_ERROR = (f"Не удалось связаться с GitHub: {e}. "
                         "Проверьте интернет на этом компьютере.")
    if line:
        line("✗ " + GH_LAST_ERROR.split("\n")[0], "err")
    return None


def github_search_repos(query, limit=12):
    """Поиск репозиториев по названию программы."""
    q = urllib.parse.quote(query)
    data = _gh_api(f"https://api.github.com/search/repositories"
                   f"?q={q}&sort=stars&order=desc&per_page={limit}")
    if not data:
        return None
    out = []
    for item in data.get("items", []):
        out.append({
            "full_name": item.get("full_name", ""),
            "description": (item.get("description") or "").strip(),
            "stars": item.get("stargazers_count", 0),
            "archived": item.get("archived", False),
        })
    return out


_GH_RELEASE_CACHE = {}


def github_releases(repo, limit=10):
    """Последние релизы репозитория вместе с файлами.
    Ответы кэшируются на время сеанса: у GitHub всего 60 запросов в час на
    адрес, а вся школа выходит в интернет под одним адресом."""
    if repo in _GH_RELEASE_CACHE:
        return _GH_RELEASE_CACHE[repo]
    data = _gh_api(f"https://api.github.com/repos/{repo}/releases?per_page={limit}")
    if data is None:
        return None
    out = []
    for rel in data:
        assets = [{"name": a.get("name", ""),
                   "url": a.get("browser_download_url"),
                   "size": a.get("size", 0)} for a in rel.get("assets", [])]
        if assets:
            out.append({"tag": rel.get("tag_name", ""),
                        "prerelease": rel.get("prerelease", False),
                        "assets": assets})
    _GH_RELEASE_CACHE[repo] = out
    return out


# Что вообще имеет смысл ставить в Linux, и в каком порядке предпочтения.
_LINUX_EXTS = (".appimage", ".rpm", ".deb", ".tar.gz", ".tgz", ".tar.xz",
               ".tar.bz2", ".zip", ".jar", ".sh", ".run", ".flatpak")
_FOREIGN = (".exe", ".msi", ".dmg", ".pkg", ".blockmap", ".sig", ".sha256",
            ".asc", ".txt", ".yml", ".yaml", ".snap", ".apk", ".msix", ".ipa")


def _machine_arch():
    m = platform.machine().lower()
    if m in ("x86_64", "amd64"):
        return "x86_64"
    if m in ("aarch64", "arm64"):
        return "arm64"
    return m


def rank_asset(name):
    """Оценивает, насколько файл релиза подходит этой системе.
    Больше — лучше; None означает «не для Linux, показывать не нужно»."""
    low = name.lower()
    if any(low.endswith(e) for e in _FOREIGN):
        return None
    ext = next((e for e in _LINUX_EXTS if low.endswith(e)), None)
    if not ext:
        return None

    score = 0
    # родной формат пакетов этой системы — лучший вариант
    if ext == ".rpm":
        score += 60 if PKG_FAMILY == "rpm" else -40
    elif ext == ".deb":
        score += 60 if PKG_FAMILY == "deb" else -40
    elif ext == ".appimage":
        score += 50          # работает в любом дистрибутиве
    elif ext in (".tar.gz", ".tgz", ".tar.xz", ".tar.bz2", ".zip"):
        score += 20
    elif ext in (".sh", ".run"):
        score += 15
    elif ext == ".jar":
        score += 10

    arch = _machine_arch()
    if arch == "x86_64":
        if any(a in low for a in ("arm64", "aarch64", "armv7", "armhf", "i386", "i686")):
            score -= 70
        if any(a in low for a in ("x86_64", "amd64", "x64")):
            score += 15
    elif arch == "arm64":
        if any(a in low for a in ("arm64", "aarch64")):
            score += 15
        elif any(a in low for a in ("x86_64", "amd64", "x64", "i386")):
            score -= 70

    if "linux" in low:
        score += 10
    if any(w in low for w in ("mac", "darwin", "win", "android")):
        score -= 50
    if "portable" in low:
        score += 3
    return score


def _github_latest_asset(repo, pattern, line):
    """Находит файл в последнем релизе GitHub.

    Если шаблон задан — берёт первый подходящий под него. Если шаблона нет
    (или под него ничего не подошло) — выбирает файл, который лучше всего
    подходит этой системе: родной пакет .rpm/.deb, иначе AppImage, иначе
    архив; чужие архитектуры и файлы для Windows/macOS отбрасываются.
    Возвращает (ссылка, имя_файла, версия) или (None, None, None)."""
    line(f"→ Спрашиваю GitHub про последнюю версию ({repo})…", "run")
    data = _gh_api(f"https://api.github.com/repos/{repo}/releases/latest")
    if data is None:
        for part in (GH_LAST_ERROR or "GitHub недоступен").split("\n"):
            if part.strip():
                line("   " + part.strip(), "warn")
        return None, None, None
    tag = data.get("tag_name", "")
    assets = data.get("assets", [])

    if pattern:
        rx = re.compile(pattern, re.I)
        for a in assets:
            if rx.search(a.get("name", "")):
                line(f"→ Последняя версия: {tag}, файл {a['name']}", "info")
                return a.get("browser_download_url"), a["name"], tag
        line(f"⚠ В релизе {tag} нет файла по шаблону «{pattern}» — "
             "подбираю подходящий сам.", "warn")

    ranked = [(rank_asset(a.get("name", "")), a) for a in assets]
    ranked = [(sc, a) for sc, a in ranked if sc is not None and sc > 0]
    if ranked:
        ranked.sort(key=lambda t: -t[0])
        a = ranked[0][1]
        line(f"→ Последняя версия: {tag}, выбран файл {a['name']} "
             f"(подходит для .{PKG_FAMILY} / {_machine_arch()})", "info")
        return a.get("browser_download_url"), a["name"], tag

    names = ", ".join(a.get("name", "") for a in assets[:12])
    line(f"✗ В релизе {tag} нет файлов для Linux. Что есть: {names}", "err")
    return None, None, None


def download_file(url, dest, line, progress, cancel, reuse=True):
    """Качает файл с показом процента в журнале.

    Скачивает во временный файл и переименовывает только после успеха —
    чтобы обрыв связи не оставил битый «установщик». Если файл уже лежит на
    месте, повторно не качает."""
    if reuse and os.path.exists(dest) and os.path.getsize(dest) > 0:
        line(f"○ {os.path.basename(dest)} уже скачан "
             f"({os.path.getsize(dest) // 1048576} МБ) — качать заново не нужно", "ok")
        return dest
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    tmp = dest + ".part"
    line(f"→ Скачиваю {os.path.basename(dest)}…", "run")
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "KoderLab-Installer"})
        with urllib.request.urlopen(req, timeout=60) as r, open(tmp, "wb") as f:
            total = int(r.headers.get("Content-Length") or 0)
            done = 0
            last = -1
            while True:
                if cancel():
                    raise InterruptedError("отменено пользователем")
                chunk = r.read(262144)
                if not chunk:
                    break
                f.write(chunk)
                done += len(chunk)
                if total:
                    pct = int(done * 100 / total)
                    if pct != last:
                        last = pct
                        progress(f"Загрузка {os.path.basename(dest)}: {pct}% "
                                 f"({done // 1048576} из {total // 1048576} МБ)")
                else:
                    progress(f"Загрузка {os.path.basename(dest)}: {done // 1048576} МБ")
        os.replace(tmp, dest)
        _chown_to_user(os.path.dirname(dest))
        line(f"✓ Скачано: {os.path.basename(dest)} "
             f"({os.path.getsize(dest) // 1048576} МБ)", "ok")
        return dest
    except InterruptedError:
        line("⚠ Загрузка отменена", "warn")
    except Exception as e:
        line(f"✗ Не удалось скачать: {e}", "err")
        line(f"   Скачайте файл вручную и положите в installers/{os.path.basename(os.path.dirname(dest))}/",
             "warn")
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except OSError:
                pass
    return None


def ensure_local_file(app, line, progress, cancel):
    """Возвращает путь к файлу установщика. Если файла в installers/ нет,
    но у программы указана ссылка ("download") или репозиторий GitHub
    ("github"), файл скачивается автоматически — тогда заранее раскладывать
    ничего не нужно, достаточно интернета."""
    path, fb = _resolve_installer_file(app)
    if path:
        if fb:
            _fallback_note(app, path, line)
        return path

    dest_dir = os.path.join(INSTALLERS_DIR, app["id"])
    url = app.get("download")
    name = os.path.basename(app.get("file") or "")

    gh = app.get("github")
    if gh and not url:
        url, gh_name, _tag = _github_latest_asset(gh, app.get("github_asset"), line)
        if gh_name:
            name = gh_name

    if not url:
        _file_missing(app, line)
        if app.get("download_hint"):
            line("   " + app["download_hint"], "info")
        return None

    if not name:
        name = os.path.basename(url.split("?")[0]) or f"{app['id']}.bin"
    return download_file(url, os.path.join(dest_dir, name), line, progress, cancel)


def _fallback_note(app, path, line):
    line(f"↯ Файл {os.path.basename(app.get('file', ''))} не найден, "
         f"использую найденный: {os.path.basename(path)}", "warn")


class RepoInstaller(BaseInstaller):
    """Пакет из репозитория дистрибутива (dnf / urpmi / apt-get / zypper).
    Если репозиторий недоступен — пробует локальный файл из installers/."""

    def install(self, app, line, progress, cancel):
        packages = app_packages(app)
        if packages:
            cmd = pkg_install_repo_cmd(packages)
            if cmd:
                line(f"→ Устанавливаю {app['name']} из репозитория ({PKG_MANAGER}): "
                     f"{', '.join(packages)}", "run")
                code = _stream(_privileged(cmd), line, progress, cancel)
                if code == -99:
                    return "cancelled"
                if code == 0 or check_installed(app):
                    line(f"✓ {app['name']}: установлено", "ok")
                    write_marker(app, {"packages": packages})
                    return "success"
                line(f"⚠ Репозиторий не помог (код {code}) — пробую локальный файл…", "warn")
            else:
                line(f"⚠ Пакетный менеджер не определён — пробую локальный файл…", "warn")
        return _install_local(app, line, progress, cancel)

    def uninstall(self, app, line, progress, cancel):
        packages = app_packages(app) or read_marker(app["id"]).get("packages") or []
        if not (packages and pkg_is_installed(packages)):
            # имя пакета в этом дистрибутиве может отличаться от указанного —
            # находим владельца исполняемого файла
            owner = _owning_package(app, line)
            if owner:
                packages = [owner]
        if packages and pkg_is_installed(packages):
            cmd = pkg_remove_cmd(packages)
            if cmd:
                line(f"→ Удаляю пакеты: {', '.join(packages)}", "run")
                code = _stream(_privileged(cmd), line, progress, cancel)
                if code == -99:
                    return "cancelled"
        removed = remove_marker(app["id"])
        remove_desktop_entry(app["id"])
        _cleanup_local_dir(app["id"])
        if check_installed(app):
            line(f"⚠ {app['name']}: похоже, ещё установлено — проверьте вручную", "warn")
            return "error"
        line(f"✓ {app['name']}: удалено" if removed or packages else
             f"○ {app['name']}: нечего удалять", "ok")
        return "removed"


def _owning_package(app, line=None):
    """Какому пакету принадлежит исполняемый файл программы.
    Нужно, когда пакет в дистрибутиве называется не так, как в courses.json."""
    chk = app.get("check") or {}
    names = chk.get("names") or ([chk["name"]] if chk.get("name") else [])
    names = names or [app.get("run_bin") or app.get("id")]
    for name in names:
        path = shutil.which(name) if name else None
        if not path:
            continue
        try:
            if PKG_FAMILY == "rpm" and shutil.which("rpm"):
                r = subprocess.run(["rpm", "-qf", "--qf", "%{NAME}", path],
                                   capture_output=True, text=True, timeout=30)
                if r.returncode == 0 and r.stdout.strip():
                    if line:
                        line(f"→ Файл {path} принадлежит пакету {r.stdout.strip()}", "info")
                    return r.stdout.strip()
            elif shutil.which("dpkg"):
                r = subprocess.run(["dpkg", "-S", path],
                                   capture_output=True, text=True, timeout=30)
                if r.returncode == 0 and ":" in r.stdout:
                    pkg = r.stdout.split(":")[0].strip()
                    if line:
                        line(f"→ Файл {path} принадлежит пакету {pkg}", "info")
                    return pkg
        except (OSError, subprocess.SubprocessError):
            continue
    return None


def _cleanup_local_dir(app_id):
    d = os.path.join(LOCAL_APPS_DIR, app_id)
    if os.path.isdir(d):
        shutil.rmtree(d, ignore_errors=True)
        return True
    return False


def _install_local(app, line, progress, cancel):
    """Установка из локального файла — тип определяется по расширению.
    Если файла нет, но задана ссылка/GitHub — он сначала скачается."""
    path = ensure_local_file(app, line, progress, cancel)
    if not path:
        return "error"
    low = path.lower()
    if low.endswith(".rpm") or low.endswith(".deb"):
        return _install_pkg_file(app, path, line, progress, cancel)
    if low.endswith(".appimage"):
        return _install_appimage(app, path, line, progress, cancel)
    if low.endswith(ARCHIVE_EXTS):
        return _install_archive(app, path, line, progress, cancel)
    if low.endswith(".sh") or low.endswith(".run"):
        return _install_script(app, path, line, progress, cancel)
    if low.endswith(".jar"):
        return _install_jar(app, path, line, progress, cancel)
    if low.endswith(".flatpak"):
        return _install_flatpak_bundle(app, path, line, progress, cancel)
    line(f"✗ Неизвестный тип файла: {os.path.basename(path)}", "err")
    return "error"


def _install_pkg_file(app, path, line, progress, cancel):
    cmd = pkg_install_file_cmd(path)
    if not cmd:
        line(f"✗ Не удалось подобрать команду установки для {os.path.basename(path)} "
             f"(пакетный менеджер: {PKG_MANAGER or 'не найден'})", "err")
        return "error"
    ext = "rpm" if path.lower().endswith(".rpm") else "deb"
    if (ext == "rpm") != (PKG_FAMILY == "rpm"):
        line(f"⚠ Файл .{ext}, а система использует пакеты .{PKG_FAMILY} — "
             "скорее всего, нужен другой файл с сайта программы.", "warn")
    line(f"→ Устанавливаю {app['name']} из файла {os.path.basename(path)}…", "run")
    code = _stream(_privileged(cmd), line, progress, cancel)
    if code == -99:
        return "cancelled"
    if code == 0 or check_installed(app):
        line(f"✓ {app['name']}: установлено", "ok")
        write_marker(app, {"packages": app_packages(app)})
        return "success"
    line(f"✗ {app['name']}: ошибка установки (код {code})", "err")
    return "error"


def _install_flatpak_bundle(app, path, line, progress, cancel):
    """Установка из файла .flatpak (бандла).

    Нужна там, где сеть блокирует Flathub: бандл скачивают на другом
    компьютере, кладут в installers/<id>/ и раздают по сети класса."""
    if not flatpak_available():
        line("✗ В системе нет flatpak — бандл ставить нечем. "
             "Установите пакет flatpak.", "err")
        return "error"
    line(f"→ Устанавливаю {app['name']} из файла {os.path.basename(path)}…", "run")
    code = _stream(_privileged(["flatpak", "install", "-y", "--bundle", path]),
                   line, progress, cancel)
    if code == -99:
        return "cancelled"
    ref = app.get("flatpak")
    if code == 0 or (ref and flatpak_is_installed(ref)):
        write_marker(app, {"flatpak": ref} if ref else None)
        if ref:
            fargs = " ".join(shell_quote(a) for a in (app.get("flatpak_args") or []))
            create_desktop_entry(app["id"], app["name"],
                                 f"flatpak run {shell_quote(ref)}"
                                 + (f" {fargs}" if fargs else ""),
                                 comment=app.get("note", ""))
        line(f"✓ {app['name']}: установлено из бандла", "ok")
        return "success"
    line(f"✗ {app['name']}: не удалось установить бандл (код {code})", "err")
    return "error"


def _install_appimage(app, path, line, progress, cancel):
    dest_dir = os.path.join(LOCAL_APPS_DIR, app["id"])
    os.makedirs(dest_dir, exist_ok=True)
    dest = os.path.join(dest_dir, os.path.basename(path))
    try:
        shutil.copy2(path, dest)
        os.chmod(dest, 0o755)
    except OSError as e:
        line(f"✗ Не удалось скопировать AppImage: {e}", "err")
        return "error"
    _chown_to_user(dest_dir)
    args = app.get("run_args") or []
    exec_cmd = " ".join([shell_quote(dest)] + [shell_quote(a) for a in args])
    create_desktop_entry(app["id"], app["name"], exec_cmd,
                         comment=app.get("note", ""), workdir=dest_dir)
    write_marker(app, {"exec": [dest] + args, "workdir": dest_dir, "dir": dest_dir})
    line(f"✓ {app['name']}: установлено (AppImage), ярлык добавлен в меню приложений", "ok")
    if not shutil.which("fusermount") and not shutil.which("fusermount3"):
        line("⚠ В системе не найден fusermount (пакет fuse) — AppImage может не "
             "запуститься. Установите пакет fuse/fuse3, либо запускайте "
             "с ключом --appimage-extract-and-run.", "warn")
    return "success"


def _install_archive(app, path, line, progress, cancel):
    dest_dir = os.path.join(LOCAL_APPS_DIR, app["id"])
    if os.path.isdir(dest_dir):
        shutil.rmtree(dest_dir, ignore_errors=True)
    os.makedirs(dest_dir, exist_ok=True)
    line(f"→ Распаковываю {os.path.basename(path)}…", "run")
    try:
        extract_archive(path, dest_dir)
    except Exception as e:
        line(f"✗ Не удалось распаковать архив: {e}", "err")
        return "error"
    # если внутри одна папка — работаем с ней
    entries = [os.path.join(dest_dir, e) for e in os.listdir(dest_dir)]
    root = entries[0] if len(entries) == 1 and os.path.isdir(entries[0]) else dest_dir

    # некоторые архивы содержат собственный установщик
    for script in ("install.sh", "setup.sh", "install"):
        cand = os.path.join(root, script)
        if os.path.isfile(cand) and app.get("run_install_script"):
            os.chmod(cand, 0o755)
            line(f"→ Запускаю встроенный установщик {script}…", "run")
            _stream(_privileged(["bash", cand]), line, progress, cancel, cwd=root)
            break

    exe = _find_executable_in(root, app["id"], app, app.get("run_bin"))
    if not exe:
        # Возможно, это Windows-программа в архиве (так распространяется,
        # например, RoboCo) — тогда запускаем её через Wine.
        win = _find_windows_exe(root, app)
        if win:
            line("→ В архиве только Windows-программа (.exe) — настраиваю Wine…", "warn")
            return _setup_portable_wine(app, win, dest_dir, line, progress, cancel)
        line(f"⚠ {app['name']}: файлы распакованы, но не удалось найти файл запуска — "
             f"ярлык не создан. Откройте папку и создайте ярлык вручную: {root}", "warn")
        _chown_to_user(dest_dir)
        write_marker(app, {"dir": dest_dir})
        return "success"
    try:
        os.chmod(exe, 0o755)
    except OSError:
        pass
    _chown_to_user(dest_dir)
    line(f"→ Файл запуска: {os.path.relpath(exe, dest_dir)}", "info")
    create_desktop_entry(app["id"], app["name"], shell_quote(exe),
                         comment=app.get("note", ""), workdir=os.path.dirname(exe))
    write_marker(app, {"exec": [exe], "workdir": os.path.dirname(exe), "dir": dest_dir})
    line(f"✓ {app['name']}: установлено, ярлык добавлен в меню приложений", "ok")
    return "success"


# Программы, которые Wine создаёт в КАЖДОМ окружении сам. Их легко принять
# за установленную программу — например, Internet Explorer: он «запускается»,
# открывает сайт и показывает ошибку 403, хотя нужной программы вообще нет.
WINE_BUILTINS = (
    "iexplore.exe", "explorer.exe", "winemine.exe", "notepad.exe",
    "wordpad.exe", "winhlp32.exe", "control.exe", "regedit.exe",
    "msiexec.exe", "winecfg.exe", "winedbg.exe", "winefile.exe",
    "winver.exe", "cmd.exe", "conhost.exe", "rundll32.exe", "taskmgr.exe",
    "uninstaller.exe", "wusa.exe", "presentationhost.exe", "hh.exe",
    "oleview.exe", "dxdiag.exe", "services.exe", "plugplay.exe",
    "wmplayer.exe", "wineboot.exe", "wscript.exe", "cscript.exe",
    "spoolsv.exe", "svchost.exe", "rpcss.exe", "start.exe", "expand.exe",
    "net.exe", "reg.exe", "attrib.exe", "xcopy.exe", "icinfo.exe",
)

# Папки внутри Program Files, которые Wine создаёт сам.
WINE_BUILTIN_DIRS = (
    "/windows media player/", "/internet explorer/", "/common files/",
    "/windows nt/", "/microsoft.net/", "/windows mail/", "/uninstall ",
)

_EXE_SKIP_WORDS = ("uninst", "unins000", "setup", "install", "crashreport",
                   "crashhandler", "vcredist", "dotnet", "helper", "updater",
                   "redist", "report", "launcher_helper")


def _is_wine_builtin(path):
    return os.path.basename(path).lower() in WINE_BUILTINS


# winetricks — это один shell-скрипт, поэтому свежую версию можно просто
# положить в домашнюю папку, не трогая системный пакет и не требуя root.
LOCAL_WINETRICKS = os.path.join(DATA_DIR, "bin", "winetricks")
WINETRICKS_URLS = [
    "https://raw.githubusercontent.com/Winetricks/winetricks/master/src/winetricks",
    "https://github.com/Winetricks/winetricks/raw/master/src/winetricks",
]
WINETRICKS_MIN = 20250000      # версии — это даты вида 20260125


def winetricks_version(path):
    """Версия winetricks числом-датой (20260125) или None."""
    if not path or not os.path.exists(path):
        return None
    try:
        r = subprocess.run([path, "--version"], capture_output=True,
                           text=True, timeout=30)
        m = re.search(r"(20\d{6})", (r.stdout or "") + (r.stderr or ""))
        return int(m.group(1)) if m else None
    except (OSError, subprocess.SubprocessError, ValueError):
        return None


def find_winetricks():
    """Свежая локальная копия важнее системной: в старых версиях рецепты
    (в частности dotnet48) уже не работают."""
    system = shutil.which("winetricks")
    if os.path.exists(LOCAL_WINETRICKS):
        local_v = winetricks_version(LOCAL_WINETRICKS) or 0
        system_v = winetricks_version(system) or 0 if system else 0
        if local_v >= system_v:
            return LOCAL_WINETRICKS
    return system


def update_winetricks(line, progress, cancel):
    """Скачивает последнюю версию winetricks в домашнюю папку.

    Системный пакет не трогаем: во-первых, нужны права root, во-вторых
    у пакетной версии --self-update часто просто отказывается работать."""
    line("→ Скачиваю свежий winetricks…", "run")
    dest = None
    for url in WINETRICKS_URLS:
        dest = download_file(url, LOCAL_WINETRICKS, line, progress, cancel,
                             reuse=False)
        if dest:
            break
    if not dest:
        line("✗ Скачать не удалось. Попробуйте вручную:", "err")
        line(f"   mkdir -p {os.path.dirname(LOCAL_WINETRICKS)} && "
             f"wget -O {LOCAL_WINETRICKS} {WINETRICKS_URLS[0]} && "
             f"chmod +x {LOCAL_WINETRICKS}", "info")
        return None
    try:
        os.chmod(dest, 0o755)
    except OSError:
        pass
    _chown_to_user(os.path.dirname(dest))
    ver = winetricks_version(dest)
    if not ver:
        line("✗ Скачанный файл не похож на winetricks.", "err")
        try:
            os.remove(dest)
        except OSError:
            pass
        return None
    line(f"✓ winetricks обновлён: версия {ver} ({dest})", "ok")
    line("   Системный winetricks не изменён — используется эта копия.", "info")
    return dest


def ensure_winetricks(line, progress, cancel, auto_update=True):
    """Возвращает путь к пригодному winetricks, при необходимости обновив его."""
    wt = find_winetricks()
    ver = winetricks_version(wt) if wt else None

    if wt and ver and ver >= WINETRICKS_MIN:
        line(f"→ winetricks {ver} — версия свежая", "info")
        return wt

    if wt:
        line(f"○ winetricks {ver or 'неизвестной версии'} устарел: рецепты "
             "установки компонентов в нём уже не работают (особенно dotnet48).", "warn")
    else:
        line("○ winetricks не найден.", "warn")

    if auto_update:
        new = update_winetricks(line, progress, cancel)
        if new:
            return new
    return wt


def _find_exe_in_prefix(app, prefix, line=None, exclude=None):
    """Ищет .exe установленной программы внутри окружения Wine.

    Никогда не возвращает встроенные программы Wine: лучше честно сказать
    «не нашёл», чем сделать ярлык на Internet Explorer."""
    drive_c = os.path.join(prefix, "drive_c")
    skip_name = os.path.basename(exclude).lower() if exclude else None
    hint = app.get("wine_run")
    if hint:
        cand = os.path.join(drive_c, hint.replace("\\", "/"))
        if os.path.exists(cand):
            return cand
        m = [p for p in globmod.glob(
            os.path.join(drive_c, "**", os.path.basename(hint)), recursive=True)
            if not _is_wine_builtin(p)]
        if m:
            return m[0]

    if hint:
        # Путь задан явно и не найден — значит программа не установилась.
        # Угадывать дальше нельзя: в Program Files лежат встроенные
        # программы Wine, и в прошлый раз так был выбран Windows Media Player.
        if line:
            line(f"   Ожидаемый файл не найден: {hint}", "warn")
        return None

    found = []
    # ВАЖНО: только Program Files. Папка drive_c/users — это ссылки на
    # настоящую домашнюю папку пользователя (Рабочий стол, Загрузки), и
    # оттуда легко подхватить сам установщик вместо установленной
    # программы — ровно это и случилось с Algodoo.
    for pattern in ("Program Files/**/*.exe", "Program Files (x86)/**/*.exe"):
        found += globmod.glob(os.path.join(drive_c, pattern), recursive=True)

    real_prefix = os.path.realpath(prefix)
    cands = []
    for e in found:
        if _is_wine_builtin(e):
            continue
        if any(w in os.path.basename(e).lower() for w in _EXE_SKIP_WORDS):
            continue
        if skip_name and os.path.basename(e).lower() == skip_name:
            continue          # это файл установщика, а не программа
        # файл должен физически лежать внутри окружения, а не быть ссылкой
        # наружу (в домашнюю папку, на флешку и т.п.)
        if not os.path.realpath(e).startswith(real_prefix):
            continue
        if any(d in e.lower().replace("\\", "/") for d in WINE_BUILTIN_DIRS):
            continue          # встроенные программы самого Wine
        cands.append(e)

    keys = [_normalize(k) for k in _app_keywords(app["id"], app)]
    for e in cands:
        if any(k and k in _normalize(os.path.basename(e)) for k in keys):
            return e
    for e in cands:
        if any(k and k in _normalize(e) for k in keys):
            return e
    # без совпадения по имени берём единственный кандидат, но только если
    # он один — иначе высок шанс выбрать не ту программу
    if len(cands) == 1:
        return cands[0]
    if line and cands:
        line(f"   Внутри окружения найдено {len(cands)} программ, "
             "но ни одна не похожа на нужную по названию.", "info")
    return None


def tool_is_editor(tool):
    return bool(tool.get("edit_file"))


def tool_is_action(tool):
    return bool(tool.get("action"))


def tool_is_command(tool):
    """Инструмент задан готовой командой (например, flatpak run …),
    а не путём к файлу внутри окружения."""
    return bool(tool.get("cmd"))


def find_app_tool(app, tool):
    """Ищет вспомогательную программу (конфигуратор, настройщик) там, где она
    установлена. Шаблоны берутся из поля "exe" — можно указать несколько,
    потому что в разных версиях файл называется по-разному."""
    patterns = tool.get("exe") or []
    if isinstance(patterns, str):
        patterns = [patterns]

    roots = []
    if (app.get("installer") or "").lower() == "wine" or app.get("wine_arch"):
        roots.append(os.path.join(wine_prefix(app["id"]), "drive_c"))
    marker_dir = read_marker(app["id"]).get("dir")
    if marker_dir:
        roots.append(marker_dir)
    roots.append(os.path.join(LOCAL_APPS_DIR, app["id"]))

    for root in roots:
        if not os.path.isdir(root):
            continue
        for pat in patterns:
            for cand in sorted(globmod.glob(os.path.join(root, pat), recursive=True)):
                if os.path.isfile(cand) and not _is_wine_builtin(cand):
                    return cand
    return None


def app_tool_command(app, path):
    """Команда запуска вспомогательной программы: через Wine, если это .exe."""
    if path.lower().endswith(".exe"):
        wine = find_wine(app["id"])
        if not wine:
            return None, None, None
        marker = read_marker(app["id"])
        arch = marker.get("wine_arch") or app.get("wine_arch") or "win64"
        wine = wine_exe_for_arch(wine, arch)
        env = marker.get("env") or wine_env(wine_prefix(app["id"]), arch, wine)
        return [wine, path], os.path.dirname(path), env
    return [path], os.path.dirname(path), None


def _find_windows_exe(root, app):
    """Ищет главный .exe в распакованном Windows-архиве (портативная сборка)."""
    hint = app.get("run_exe") or app.get("run_bin")
    if hint:
        if not hint.lower().endswith(".exe"):
            hint += ".exe"
        m = globmod.glob(os.path.join(root, "**", hint), recursive=True)
        if m:
            return m[0]
    exes = [e for e in globmod.glob(os.path.join(root, "**", "*.exe"), recursive=True)
            if not _is_wine_builtin(e)
            and not any(s in os.path.basename(e).lower() for s in _EXE_SKIP_WORDS)]
    if not exes:
        return None
    keys = [_normalize(k) for k in _app_keywords(app["id"], app)]
    for e in exes:
        if any(k and k in _normalize(os.path.basename(e)) for k in keys):
            return e
    # у игр главный .exe обычно лежит в корне, рядом с папкой *_Data
    exes.sort(key=lambda p: (p.count(os.sep), len(p)))
    return exes[0]


def _setup_portable_wine(app, exe, dest_dir, line, progress, cancel):
    """Портативная Windows-программа из архива: своё окружение Wine,
    ярлык и запись для кнопки «Запустить»."""
    wine = find_wine()
    if not wine:
        line("○ Wine в системе не найден — без него Windows-программа "
             "из архива не запустится.", "warn")
        install_dependency(_pick_packages(WINE_PACKAGES), "Wine", line, progress, cancel)
        wine = find_wine()
    if not wine:
        line("✗ Wine поставить не удалось. Файлы распакованы, но запустить их "
             "нельзя. Поставьте Wine и переустановите программу:", "err")
        line("   ROSA: sudo dnf install wine   •   Альт/Astra: sudo apt-get install wine", "info")
        line(f"   Файлы лежат здесь: {dest_dir}", "info")
        # маркер НЕ пишем: программа не установлена по-настоящему, и в списке
        # она должна остаться «не установлено», а не вводить техника в заблуждение
        return "error"

    prefix = _user_makedirs(wine_prefix(app["id"]))
    arch = choose_wine_arch(app, exe, line)
    wine = wine_exe_for_arch(wine, arch)
    env = wine_env(prefix, arch, wine, app.get("wine_env_extra"))
    line(f"→ Готовлю окружение Wine ({env['WINEARCH']}). Первый раз это "
         "занимает 1–3 минуты…", "run")
    code = _stream_env([wine, "wineboot", "-u"], env, line, progress, cancel)
    if code == -99:
        return "cancelled"
    if code != 0 or not os.path.isdir(os.path.join(prefix, "drive_c")):
        line(f"✗ Окружение Wine не создалось (код {code}).", "err")
        line(f"   Проверьте владельца: ls -ld {prefix}; при необходимости "
             f"sudo chown -R $USER: {os.path.dirname(prefix)}", "warn")
        return "error"

    tricks = app.get("wine_tricks") or []
    if tricks:
        if not find_winetricks():
            install_dependency(_pick_packages(WINETRICKS_PACKAGES), "winetricks",
                               line, progress, cancel)
        wt = ensure_winetricks(line, progress, cancel)
        if wt:
            line(f"→ Доустанавливаю компоненты Windows: {', '.join(tricks)}…", "run")
            if _stream_env([wt, "-q"] + list(tricks), env, line, progress, cancel) == -99:
                return "cancelled"
        else:
            line(f"⚠ Нет winetricks, а нужны компоненты {', '.join(tricks)} — "
                 "программа может не запуститься.", "warn")

    exec_cmd = (f"env WINEPREFIX={shell_quote(prefix)} WINEARCH={env['WINEARCH']} "
                f"WINEDEBUG=-all {shell_quote(wine)} {shell_quote(exe)}")
    create_desktop_entry(app["id"], app["name"], exec_cmd,
                         comment=app.get("note", ""), workdir=os.path.dirname(exe))
    _chown_to_user(dest_dir)
    write_marker(app, {"exec": [wine, exe], "workdir": os.path.dirname(exe),
                       "env": env, "prefix": prefix, "dir": dest_dir})
    line(f"→ Файл запуска: {os.path.basename(exe)}", "info")
    line(f"✓ {app['name']}: установлено (Windows-версия через Wine), "
         "ярлык добавлен в меню приложений", "ok")
    line("   Проверьте программу на одном ПК до раскатки: Wine — это "
         "совместимость, а не гарантия.", "warn")
    return "success"


def _is_elf(path):
    """Многие Linux-установщики с расширением .run — это обычные бинарные
    файлы (например, Qt Installer Framework у TRIK Studio). Их нельзя
    запускать через bash: получится «не удаётся запустить бинарный файл»."""
    try:
        with open(path, "rb") as f:
            return f.read(4) == b"\x7fELF"
    except OSError:
        return False


def _install_script(app, path, line, progress, cancel):
    try:
        os.chmod(path, 0o755)
    except OSError:
        pass
    args = app.get("silent_args") or []
    line(f"→ Запускаю установщик {app['name']} ({os.path.basename(path)})…", "run")

    if _is_elf(path):
        # бинарный установщик: запускаем напрямую и от имени пользователя —
        # такие мастера ставят программу в домашнюю папку
        line("   Это графический мастер установки — пройдите шаги в открывшемся "
             "окне. Путь установки по умолчанию менять не нужно.", "info")
        cmd = _as_user([path] + list(args))
        code = _stream(cmd, line, progress, cancel, cwd=os.path.dirname(path))
    else:
        needs_root = app.get("script_needs_root", True)
        cmd = ["bash", path] + list(args)
        code = _stream(_privileged(cmd) if needs_root else cmd, line, progress, cancel,
                       cwd=os.path.dirname(path))
    if code == -99:
        return "cancelled"

    exe = _find_after_install(app, line)
    if exe:
        create_desktop_entry(app["id"], app["name"], shell_quote(exe),
                             comment=app.get("note", ""), workdir=os.path.dirname(exe))
        write_marker(app, {"exec": [exe], "workdir": os.path.dirname(exe)})
        line(f"✓ {app['name']}: установлено ({exe}), ярлык добавлен в меню", "ok")
        return "success"

    if code == 0 or check_installed(app):
        line(f"✓ {app['name']}: мастер установки завершился без ошибок", "ok")
        line("   Файл запуска найти не удалось — запускайте программу из меню "
             "приложений или ярлыком, который создал сам мастер. Чтобы работала "
             "кнопка «Запустить», впишите путь к нему в поле \"find_after_install\" "
             "в courses.json.", "warn")
        write_marker(app)
        return "success"
    line(f"✗ {app['name']}: ошибка установки (код {code})", "err")
    return "error"


def _find_after_install(app, line):
    """Ищет файл запуска после графического мастера установки.
    Список мест задаётся полем "find_after_install" в courses.json."""
    user, home = real_user()
    home = home or USER_HOME
    patterns = app.get("find_after_install") or []
    if isinstance(patterns, str):
        patterns = [patterns]
    for pat in patterns:
        pat = pat.replace("~", home) if pat.startswith("~") else pat
        for cand in sorted(globmod.glob(os.path.expandvars(pat))):
            if os.path.isfile(cand) and os.access(cand, os.X_OK):
                return cand
    name = app.get("run_bin")
    if name:
        found = shutil.which(name)
        if found:
            return found
    return None


def _install_jar(app, path, line, progress, cancel, copy=True):
    line("→ Проверяю Java (обязательно для этой программы)…", "run")
    java = ensure_java(line, progress, cancel)
    # запоминаем именно ту java, которая умеет окна: в системе их бывает
    # несколько, и «первая по PATH» может оказаться headless
    if not java:
        line("✗ Установка остановлена: без Java с поддержкой окон программа "
             "всё равно не запустится.", "err")
        line("   Поставьте вручную и повторите установку:", "warn")
        line("   ROSA:            sudo dnf install java-17-openjdk", "info")
        line("   Альт / М ОС:     sudo apt-get install java-17-openjdk", "info")
        line("   Astra / Debian:  sudo apt-get install openjdk-17-jre", "info")
        return "error"
    line(f"✓ Java подходит: {java}", "ok")
    dest_dir = os.path.join(LOCAL_APPS_DIR, app["id"])
    os.makedirs(dest_dir, exist_ok=True)
    if copy:
        dest = os.path.join(dest_dir, os.path.basename(path))
        try:
            shutil.copy2(path, dest)
        except OSError as e:
            line(f"✗ Не удалось скопировать файл: {e}", "err")
            return "error"
    else:
        dest = path
    _chown_to_user(dest_dir)
    workdir = os.path.dirname(dest)
    exec_cmd = f"{shell_quote(java)} -jar {shell_quote(dest)}"
    create_desktop_entry(app["id"], app["name"], exec_cmd,
                         comment=app.get("note", ""), workdir=workdir)
    write_marker(app, {"exec": [java, "-jar", dest], "workdir": workdir,
                       "dir": dest_dir})
    line(f"✓ {app['name']}: установлено (запуск через Java), ярлык в меню приложений", "ok")
    line(f"   Ручной запуск: cd {workdir} && java -jar {os.path.basename(dest)}", "info")
    return "success"


class LocalFileInstaller(BaseInstaller):
    """Локальный файл: .rpm/.deb/AppImage/архив/.sh — тип по расширению."""

    def install(self, app, line, progress, cancel):
        return _install_local(app, line, progress, cancel)

    def uninstall(self, app, line, progress, cancel):
        packages = app_packages(app) or read_marker(app["id"]).get("packages") or []
        removed = False
        if packages and pkg_is_installed(packages):
            cmd = pkg_remove_cmd(packages)
            if cmd:
                line(f"→ Удаляю пакеты: {', '.join(packages)}", "run")
                code = _stream(_privileged(cmd), line, progress, cancel)
                if code == -99:
                    return "cancelled"
                removed = True
        if _cleanup_local_dir(app["id"]):
            removed = True
        # архив мог оказаться Windows-программой — тогда есть и окружение Wine
        pfx = wine_prefix(app["id"])
        if os.path.isdir(pfx):
            line(f"→ Удаляю окружение Wine: {pfx}", "run")
            remove_prefix(pfx, find_wine(app["id"]), line)
            removed = True
        if remove_desktop_entry(app["id"]):
            removed = True
        if remove_marker(app["id"]):
            removed = True
        line(f"✓ {app['name']}: удалено" if removed else f"○ {app['name']}: нечего удалять",
             "ok" if removed else "info")
        return "removed"


# Репозитории, для которых уже обновляли appstream-метаданные в этом
# запуске программы — чтобы не качать их заново для каждой следующей
# flatpak-программы в пачке ("Установить всё").
_APPSTREAM_UPDATED = set()


class FlatpakInstaller(BaseInstaller):
    """Установка из flatpak.

    Порядок важен: сначала пробуем поставить программу напрямую по
    идентификатору. Это самая надёжная проверка — а вот `flatpak search`
    и `remote-info` работают только когда скачаны метаданные репозитория
    (appstream), которых после свежего remote-add ещё нет. Раньше из-за
    этого установка отваливалась на верном идентификаторе с сообщением
    «в репозитории ничего не найдено»."""

    def install(self, app, line, progress, cancel):
        # Если файл (AppImage или .flatpak-бандл) уже лежит в installers/<id>/
        # — ставим сразу из него: не тратим трафик и время на Flathub, это
        # особенно важно при медленном интернете класса. Тот же файл, если
        # его положить на все компьютеры (или раздать по сети — см.
        # «📡 Раздать по сети»), избавляет от скачивания на каждом ПК заново.
        local_path, _ = _resolve_installer_file(app)
        if local_path:
            line(f"→ Нашёл файл рядом: {os.path.basename(local_path)} — "
                 "ставлю без обращения к Flathub…", "run")
            result = _install_local(app, line, progress, cancel)
            if result in ("success", "cancelled"):
                return result
            line("○ Не получилось поставить из локального файла — "
                 "пробую обычным способом через flatpak.", "warn")

        if not flatpak_available():
            line("✗ flatpak не установлен в системе. Установите пакет flatpak "
                 "и подключите Flathub, либо используйте другой способ установки.", "err")
            return self._fallback(app, line, progress, cancel,
                                  "flatpak не установлен")
        ref = app.get("flatpak")
        if not ref:
            line("✗ Не указан идентификатор flatpak (поле \"flatpak\")", "err")
            return "error"
        remote = app.get("flatpak_remote", "flathub")
        urls = app.get("flatpak_repo_urls") or FLATHUB_URLS
        if not ensure_flatpak_remote(remote, urls, line, progress, cancel):
            return self._fallback(app, line, progress, cancel,
                                  "репозиторий flatpak подключить не удалось")

        # если сломан сам flatpak — не тратим время на пять попыток подряд
        if flatpak_health(line) == "broken":
            explain_broken_flatpak(line)
            return self._fallback(app, line, progress, cancel,
                                  "flatpak в системе неисправен")

        # попытка 1: установка напрямую по идентификатору из courses.json
        line(f"→ Устанавливаю {app['name']} через flatpak ({ref})…", "run")
        code = _stream(_privileged(["flatpak", "install", "-y", remote, ref]),
                       line, progress, cancel)
        if code == -99:
            return "cancelled"
        if code == 0 or flatpak_is_installed(ref):
            return self._done(app, ref, line)

        # попытка 2: докачать метаданные репозитория и повторить. Метаданные
        # общие для всех программ репозитория — если их уже обновляли для
        # предыдущей программы в этом же запуске (например, при «Установить
        # всё»), второй раз через минуту не качаем.
        if remote in _APPSTREAM_UPDATED:
            line("○ Не вышло. Метаданные репозитория уже обновлялись только что — "
                 "пробую install ещё раз как есть.", "warn")
        else:
            line("○ Не вышло. Обновляю список программ репозитория "
                 "(скачиваются метаданные, это небыстро)…", "warn")
            _stream(_privileged(["flatpak", "update", "--appstream", "-y", remote]),
                    line, progress, cancel)
            _APPSTREAM_UPDATED.add(remote)
        code = _stream(_privileged(["flatpak", "install", "-y", remote, ref]),
                       line, progress, cancel)
        if code == -99:
            return "cancelled"
        if code == 0 or flatpak_is_installed(ref):
            return self._done(app, ref, line)

        # попытка 3: установка по прямой ссылке .flatpakref —
        # работает даже без метаданных репозитория
        for base in ("https://dl.flathub.org/repo/appstream/",
                     "https://flathub.org/repo/appstream/"):
            url = f"{base}{ref}.flatpakref"
            line(f"○ Пробую поставить по прямой ссылке: {url}", "warn")
            code = _stream(_privileged(["flatpak", "install", "-y", url]),
                           line, progress, cancel)
            if code == -99:
                return "cancelled"
            if code == 0 or flatpak_is_installed(ref):
                return self._done(app, ref, line)

        # попытка 4: вдруг идентификатор действительно сменился
        found = flatpak_resolve_ref(app, remote, line)
        if found and found != ref:
            line(f"→ Пробую найденный идентификатор: {found}", "run")
            code = _stream(_privileged(["flatpak", "install", "-y", remote, found]),
                           line, progress, cancel)
            if code == 0 or flatpak_is_installed(found):
                return self._done(app, found, line)

        self._diagnose(remote, line)
        return self._fallback(app, line, progress, cancel,
                              "установить через flatpak не удалось")

    @staticmethod
    def _done(app, ref, line):
        write_marker(app, {"flatpak": ref})
        fargs = " ".join(shell_quote(a) for a in (app.get("flatpak_args") or []))
        create_desktop_entry(app["id"], app["name"],
                             f"flatpak run {shell_quote(ref)}"
                             + (f" {fargs}" if fargs else ""),
                             comment=app.get("note", ""))
        line(f"✓ {app['name']}: установлено ({ref})", "ok")
        return "success"

    @staticmethod
    def _diagnose(remote, line):
        """Короткая проверка: виден ли репозиторий вообще. Чаще всего
        оказывается, что сеть школы блокирует адреса Flathub."""
        line("── Проверяю доступность репозитория ──", "run")
        try:
            r = subprocess.run(["flatpak", "remotes", "--columns=name,url"],
                               capture_output=True, text=True, timeout=60)
            for ln in (r.stdout or "").splitlines():
                if ln.strip():
                    line("   " + ln.strip(), "info")
            r = subprocess.run(["flatpak", "remote-ls", remote, "--columns=application"],
                               capture_output=True, text=True, timeout=180)
            out = (r.stdout or "") + (r.stderr or "")
            names = [x for x in (r.stdout or "").splitlines() if x.strip()]
            if any(mark in out for mark in _FLATPAK_BROKEN_MARKS):
                explain_broken_flatpak(line)
            elif names:
                line(f"   В репозитории видно программ: {len(names)} — "
                     "связь есть, дело в идентификаторе.", "warn")
            else:
                line("   Репозиторий не отдал ни одной программы, но и явной "
                     "поломки flatpak не видно — похоже, сеть блокирует адреса "
                     "Flathub. Проверьте вручную: flatpak remote-ls flathub", "err")
                line("   Обходные пути: другой канал интернета на время установки "
                     "либо бандл .flatpak в installers/ (см. заметку к программе).",
                     "info")
        except (OSError, subprocess.SubprocessError) as e:
            line(f"   Не удалось опросить flatpak: {e}", "warn")

    @staticmethod
    def _fallback(app, line, progress, cancel, reason):
        """Если flatpak не сработал — пробуем обычный путь: пакет из
        репозитория дистрибутива или файл из installers/<id>/."""
        if not (app.get("packages") or app.get("file") or app.get("github")):
            line(f"✗ {app['name']}: {reason}, запасного варианта нет.", "err")
            return "error"
        line(f"↯ {reason} — перехожу к запасному варианту "
             "(пакет дистрибутива или файл из installers/).", "warn")
        if app.get("packages"):
            return RepoInstaller().install(app, line, progress, cancel)
        return _install_local(app, line, progress, cancel)

    def is_installed(self, app, cache=None):
        if check_installed(app, cache):
            return True
        # программа могла встать запасным путём — тогда есть отметка
        return os.path.exists(os.path.join(MARKERS_DIR, f"{app['id']}.json"))

    def uninstall(self, app, line, progress, cancel):
        ref = read_marker(app["id"]).get("flatpak") or app.get("flatpak")
        if ref and flatpak_is_installed(ref):
            _stream(_privileged(["flatpak", "uninstall", "-y", ref]), line, progress, cancel)
        else:
            # ставилось запасным путём — убираем пакет/файлы
            LocalFileInstaller().uninstall(app, lambda t, k="info": None,
                                           progress, cancel)
        remove_marker(app["id"])
        remove_desktop_entry(app["id"])
        line(f"✓ {app['name']}: удалено", "ok")
        return "removed"

    def launch_cmd(self, app):
        marker = read_marker(app["id"])
        ref = marker.get("flatpak") or app.get("flatpak")
        if marker and not marker.get("flatpak"):
            # установлено запасным путём — запускаем как обычную программу
            return BaseInstaller().launch_cmd(app)
        if not ref:
            return None, None, None, "не указан идентификатор flatpak."
        if not flatpak_is_installed(ref):
            return None, None, None, "не установлено. Сначала нажмите «Установить»."
        # ВАЖНО: здесь НЕ оборачиваем в _as_user — это делает LaunchWorker.
        # Двойная обёртка даёт вложенный runuser, который падает с ошибкой
        # «не может быть использовано не суперпользователями».
        return (["flatpak", "run", ref] + list(app.get("flatpak_args") or []),
                None, None, None)


class JarInstaller(LocalFileInstaller):
    """Программа на Java. Принимает и сам .jar, и архив с ним внутри
    (как TLauncher_v17.zip: .jar + пакет JDK + инструкции)."""

    def launch_cmd(self, app):
        """Перед запуском обязательно проверяем Java.

        Без этого лаунчер падает с UnsatisfiedLinkError ... libawt_xawt.so,
        и по одной этой строке техник причину не понимает. Лучше не
        запускать вовсе и сразу сказать, что делать."""
        java = find_java(need_gui=True)
        if not java:
            headless = find_java(need_gui=False)
            if headless:
                ver = java_version(headless)
                if java_has_gui(headless) and ver and ver < JAVA_MIN_VERSION:
                    return None, None, None, (
                        f"установлена Java {ver} ({headless}) — она слишком старая, "
                        f"лаунчер на ней не запускается. Нужна {JAVA_MIN_VERSION} "
                        "или новее.\n"
                        "   Нажмите ⚙ → «Java: установить/починить», либо вручную:\n"
                        "   sudo dnf install java-17-openjdk        (ROSA)\n"
                        "   sudo apt-get install java-17-openjdk    (Альт / М ОС)\n"
                        "   sudo apt-get install openjdk-17-jre     (Astra / Debian)")
                return None, None, None, (
                    f"установленная Java ({headless}) не умеет открывать окна "
                    "(вариант headless). Программа не запустится — будет ошибка "
                    "UnsatisfiedLinkError ... libawt_xawt.so.\n"
                    "   Нажмите кнопку ⚙ в строке программы → «Java: "
                    "установить/починить», либо выполните вручную:\n"
                    "   sudo dnf install java-17-openjdk        (ROSA)\n"
                    "   sudo apt-get install java-17-openjdk    (Альт / М ОС)\n"
                    "   sudo apt-get install openjdk-17-jre     (Astra / Debian)")
            return None, None, None, (
                "в системе нет Java, а без неё лаунчер не запустится.\n"
                "   Нажмите ⚙ → «Java: установить/починить», либо вручную:\n"
                "   sudo dnf install java-17-openjdk        (ROSA)\n"
                "   sudo apt-get install openjdk-17-jre     (Astra / Debian)")

        # В отметке могла остаться java, которую с тех пор удалили или
        # заменили на headless. Подставляем проверенную ДО того, как
        # проверять существование файлов, иначе получим бесполезное
        # «файл запуска не найден» вместо запуска.
        marker = read_marker(app["id"])
        exec_cmd = marker.get("exec")
        if isinstance(exec_cmd, list) and len(exec_cmd) >= 3 and exec_cmd[1] == "-jar":
            jar = exec_cmd[2]
            if not os.path.exists(jar):
                return None, None, None, (
                    f"файл лаунчера не найден: {jar}. "
                    "Нажмите «Удалить», затем «Установить» заново.")
            return [java, "-jar", jar], marker.get("workdir"), marker.get("env"), None
        return BaseInstaller().launch_cmd(app)

    def install(self, app, line, progress, cancel):
        path = ensure_local_file(app, line, progress, cancel)
        if not path:
            return "error"

        if path.lower().endswith(ARCHIVE_EXTS):
            dest_dir = os.path.join(LOCAL_APPS_DIR, app["id"])
            if os.path.isdir(dest_dir):
                shutil.rmtree(dest_dir, ignore_errors=True)
            os.makedirs(dest_dir, exist_ok=True)
            line(f"→ Распаковываю {os.path.basename(path)}…", "run")
            try:
                extract_archive(path, dest_dir)
            except Exception as e:
                line(f"✗ Не удалось распаковать архив: {e}", "err")
                return "error"
            _chown_to_user(dest_dir)

            jars = globmod.glob(os.path.join(dest_dir, "**", "*.jar"), recursive=True)
            if not jars:
                line("✗ В архиве нет ни одного .jar — проверьте, что это "
                     "архив с лаунчером.", "err")
                return "error"
            keys = [_normalize(k) for k in _app_keywords(app["id"], app)]
            jar = next((j for j in jars
                        if any(k and k in _normalize(os.path.basename(j))
                               for k in keys)), jars[0])
            line(f"→ Файл лаунчера: {os.path.relpath(jar, dest_dir)}", "info")

            # в архиве может лежать пакет с Java — используем его, если
            # в системе Java нет и репозиторий недоступен
            self._java_from_archive(dest_dir, line, progress, cancel)

            for txt in sorted(globmod.glob(os.path.join(dest_dir, "**", "*.txt"),
                                           recursive=True)):
                line(f"   В архиве есть инструкция: {os.path.basename(txt)}", "info")
            return _install_jar(app, jar, line, progress, cancel, copy=False)

        return _install_jar(app, path, line, progress, cancel)

    @staticmethod
    def _java_from_archive(dest_dir, line, progress, cancel):
        if find_java():
            return
        pkgs = [f for f in globmod.glob(os.path.join(dest_dir, "**", "*"), recursive=True)
                if f.lower().endswith((".rpm", ".deb"))]
        if not pkgs:
            return
        ext = ".rpm" if PKG_FAMILY == "rpm" else ".deb"
        fit = [f for f in pkgs if f.lower().endswith(ext)]
        if not fit:
            line(f"○ В архиве есть Java ({os.path.basename(pkgs[0])}), но это пакет "
                 f"не для вашей системы (нужен {ext}). Поставлю Java из "
                 "репозитория.", "warn")
            return
        line(f"→ В архиве найдена Java: {os.path.basename(fit[0])} — ставлю её.", "run")
        cmd = pkg_install_file_cmd(fit[0])
        if cmd:
            _stream(_privileged(cmd), line, progress, cancel)


class WebInstaller(BaseInstaller):
    """Веб-инструмент: ярлык в меню приложений. Открывает сайт ("url")
    либо локальный html-файл офлайн ("file")."""

    @staticmethod
    def _target(app):
        """Куда ведёт ярлык.

        По умолчанию офлайн-файл важнее ссылки: в школе без интернета
        локальная копия откроется всегда. Если офлайн-файла нет — берётся
        адрес сайта. Поле "prefer": "url" меняет приоритет на обратный."""
        url = app.get("url")
        local = None
        if app.get("file"):
            path, _ = _resolve_installer_file(app)
            if path:
                local = "file://" + os.path.abspath(path)
        if app.get("prefer") == "url":
            return url or local
        return local or url

    def install(self, app, line, progress, cancel):
        target = self._target(app)
        if not target:
            line("✗ Не задан ни адрес сайта (url), ни локальный файл (file)", "err")
            return "error"
        create_desktop_entry(app["id"], app["name"],
                             f"xdg-open {shell_quote(target)}",
                             comment=app.get("note", ""),
                             categories="Education;Network;")
        write_marker(app, {"target": target})
        line(f"✓ {app['name']}: ярлык добавлен в меню приложений ({target})", "ok")
        if target.startswith("file://"):
            line("   Открывается локальный файл — интернет не нужен.", "info")
        elif app.get("file"):
            line(f"   Открывается сайт. Чтобы работало без интернета, положите "
                 f"файл в installers/{app['id']}/", "info")
        return "success"

    def uninstall(self, app, line, progress, cancel):
        removed = remove_desktop_entry(app["id"])
        removed = remove_marker(app["id"]) or removed
        line(f"✓ {app['name']}: ярлык удалён" if removed else f"○ {app['name']}: ярлыка нет",
             "ok" if removed else "info")
        return "removed"

    def launch_cmd(self, app):
        target = self._target(app)
        if not target:
            return None, None, None, "не задан ни адрес сайта (url), ни локальный файл (file)."
        return ["xdg-open", target], None, None, None


class ModInstaller(BaseInstaller):
    """Мод для Minecraft — копируется в ~/.minecraft/mods."""

    def install(self, app, line, progress, cancel):
        src = ensure_local_file(app, line, progress, cancel)
        if not src:
            return "error"
        try:
            os.makedirs(MINECRAFT_MODS_DIR, exist_ok=True)
        except OSError as e:
            line(f"✗ Не удалось создать папку модов: {e}", "err")
            return "error"
        dest = os.path.join(MINECRAFT_MODS_DIR, os.path.basename(src))
        try:
            shutil.copy2(src, dest)
        except OSError as e:
            line(f"✗ Не удалось скопировать мод: {e}", "err")
            return "error"
        _chown_to_user(MINECRAFT_MODS_DIR)
        write_marker(app, {"path": dest})
        line(f"✓ {app['name']}: скопирован в {MINECRAFT_MODS_DIR}", "ok")
        line("   Убедитесь, что в лаунчере выбран и хотя бы раз запущен профиль "
             "Minecraft Forge подходящей версии — иначе мод не подхватится.", "warn")
        return "success"

    def uninstall(self, app, line, progress, cancel):
        m = read_marker(app["id"])
        removed = False
        path = m.get("path")
        if path and os.path.exists(path):
            try:
                os.remove(path)
                removed = True
            except OSError:
                pass
        if remove_marker(app["id"]):
            removed = True
        line(f"✓ {app['name']}: мод удалён" if removed else f"○ {app['name']}: нечего удалять",
             "ok" if removed else "info")
        return "removed"

    def launch_cmd(self, app):
        return None, None, None, (
            "это мод — он запускается вместе с Minecraft (профиль Forge нужной "
            "версии), отдельного запуска у него нет. Запустите лаунчер Minecraft.")


class UnsupportedInstaller(BaseInstaller):
    """Программы, у которых нет версии для Linux. Не ставим — показываем,
    что делать вместо этого (см. поле "note" в courses.json)."""

    def is_installed(self, app, cache=None):
        return False

    def install(self, app, line, progress, cancel):
        line(f"✗ {app['name']}: версии для Linux не существует.", "err")
        if app.get("note"):
            line("   " + app["note"], "warn")
        if app.get("alternative"):
            line("   Замена для Linux: " + app["alternative"], "info")
        return "skipped"

    def uninstall(self, app, line, progress, cancel):
        line(f"○ {app['name']}: нечего удалять (не поддерживается в Linux).", "info")
        return "removed"

    def launch_cmd(self, app):
        return None, None, None, "не поддерживается в Linux."


# ---------------------------------------------------------------------------
# Зависимости (Java для .jar, Wine для Windows-программ)
# ---------------------------------------------------------------------------

def _pick_packages(spec):
    """Выбирает имена пакетов под текущий дистрибутив из словаря или списка."""
    return app_packages({"packages": spec})


def install_dependency(packages, human_name, line, progress, cancel):
    """Ставит системные пакеты-зависимости из репозитория."""
    if not packages:
        return False
    cmd = pkg_install_repo_cmd(packages)
    if not cmd:
        line(f"✗ Не удалось подобрать команду установки для {human_name} "
             f"(менеджер пакетов: {PKG_MANAGER or 'не найден'})", "err")
        return False
    line(f"→ Сначала ставлю {human_name}: {', '.join(packages)}", "run")
    code = _stream(_privileged(cmd), line, progress, cancel)
    return code == 0


JAVA_PACKAGES = {
    # на ROSA рабочим оказался именно -devel (проверено на практике)
    "rosa": ["java-17-openjdk-devel"],
    "alt": ["java-17-openjdk"],
    "rpm": ["java-17-openjdk-devel"],
    "deb": ["openjdk-17-jre"],
    "default": ["java-17-openjdk"],
}

WINE_PACKAGES = {
    "rosa": ["wine"],
    "alt": ["wine"],
    "rpm": ["wine"],
    "deb": ["wine"],
    "default": ["wine"],
}

WINETRICKS_PACKAGES = {"default": ["winetricks"], "deb": ["winetricks"]}


def ensure_java(line, progress, cancel):
    java = find_java(need_gui=True)
    if java:
        return java

    headless = find_java(need_gui=False)
    ver = java_version(headless) if headless else None
    if headless and java_has_gui(headless) and ver and ver < JAVA_MIN_VERSION:
        line(f"⚠ Java найдена ({headless}), версия {ver} — слишком старая. "
             f"Нужна {JAVA_MIN_VERSION} или новее: на 11-й лаунчер не "
             "запускается.", "warn")
        line("→ Ставлю подходящую версию…", "run")
    elif headless:
        line(f"⚠ Java найдена ({headless}), но это вариант БЕЗ ГРАФИКИ (headless): "
             "в ней нет libawt_xawt.so, поэтому окно лаунчера не откроется "
             "(ошибка UnsatisfiedLinkError).", "warn")
        line("→ Ставлю полноценную Java с поддержкой окон…", "run")
    else:
        line("○ Java в системе не найдена — она нужна и для лаунчера Minecraft, "
             "и для модов.", "warn")
    # пробуем по очереди: сначала предпочтительный пакет, затем запасные —
    # в разных дистрибутивах графическая Java называется по-разному
    for packages in _java_package_variants():
        if install_dependency(packages, "Java (" + packages[0] + ")",
                              line, progress, cancel):
            java = find_java(need_gui=True)
            if java:
                line(f"✓ Java готова: {java}", "ok")
                return java
    line(f"✗ Подходящую Java (версия {JAVA_MIN_VERSION}+, с поддержкой окон) "
         "поставить не удалось. Поставьте вручную и повторите:", "err")
    line("   ROSA:            sudo dnf install java-17-openjdk", "info")
    line("                    (НЕ java-11 — на ней лаунчер не стартует, "
         "и НЕ *-headless)", "info")
    line("   Альт / М ОС:     sudo apt-get install java-17-openjdk", "info")
    line("   Astra / Debian:  sudo apt-get install openjdk-17-jre", "info")
    line("   ВАЖНО: .deb-пакет Java на ROSA/Альт не встанет — нужен .rpm "
         "или пакет из штатного репозитория.", "warn")
    return None


def _java_package_variants():
    """Названия пакетов Java по убыванию предпочтительности.

    На ROSA рабочим оказался java-11-openjdk: у java-17 в некоторых сборках
    ставится headless-вариант без libawt_xawt.so."""
    if PKG_FAMILY == "rpm":
        return [["java-17-openjdk"], ["java-17-openjdk-devel"],
                ["java-21-openjdk"], ["java-latest-openjdk"]]
    return [["openjdk-17-jre"], ["openjdk-17-jdk"], ["openjdk-21-jre"],
            ["default-jre"]]


# ---------------------------------------------------------------------------
# Wine: Windows-программы, у которых нет Linux-версии (Kodu, Algodoo, Pivot)
# ---------------------------------------------------------------------------

WINE_ROOT = os.path.join(DATA_DIR, "wine")


def wine_prefix(app_id):
    return os.path.join(WINE_ROOT, app_id)


# --- собственные настройки установщика (свой Wine и т.п.) ------------------

SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")


def load_settings():
    try:
        with open(SETTINGS_FILE, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_settings(data):
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        _chown_to_user(DATA_DIR)
        return True
    except OSError:
        return False


WINE_BUILDS_DIR = os.path.join(DATA_DIR, "wine-builds")


def wine_candidates():
    """Все сборки Wine, которые есть на этом компьютере.
    Возвращает список (путь, откуда взялась)."""
    out = []
    seen = set()

    def add(path, origin):
        if path and os.path.exists(path) and os.path.realpath(path) not in seen:
            seen.add(os.path.realpath(path))
            out.append((path, origin))

    chosen = load_settings().get("wine_binary")
    add(chosen, "выбрана вручную")
    add(shutil.which("wine"), "системная")
    add(shutil.which("wine-staging"), "системная (staging)")
    for pat in (os.path.join(WINE_BUILDS_DIR, "*", "bin", "wine"),
                "/opt/wine*/bin/wine",
                os.path.expanduser("~/.local/share/lutris/runners/wine/*/bin/wine"),
                os.path.expanduser("~/.var/app/net.lutris.Lutris/data/lutris/"
                                   "runners/wine/*/bin/wine")):
        for cand in sorted(globmod.glob(pat)):
            add(cand, "скачанная сборка" if WINE_BUILDS_DIR in cand else "найдена в системе")
    return out


# Библиотеки, без которых 32-битный Wine не работает: шрифты, X11, звук,
# графика. Их отсутствие даёт «Wine cannot find the FreeType font library».
# Без этих библиотек 32-битный Wine не запускается вовсе.
# libc.so.6 — САМАЯ первая: без 32-битной glibc не загрузится вообще ни один
# 32-битный файл, и Wine падает сразу на «could not load kernel32.dll,
# status c0000135» ещё до того, как дело доходит до шрифтов или X11. Раньше
# этой проверки не было — missing_lib32() мог сказать «всё в порядке» (если
# в системе случайно нашлись freetype/X11/GL нужной разрядности), хотя базовая
# 32-битная glibc не стояла вовсе, и реальная установка тут же падала.
LIB32_CRITICAL = ("libc.so.6", "libfreetype.so.6", "libX11.so.6", "libGL.so.1")
# Эти влияют на качество: без XComposite бывают артефакты, без gnutls —
# ругань про шифрование.Программа при этом работает, поэтому установку
# из-за них не останавливаем.
LIB32_OPTIONAL = ("libasound.so.2", "libXcomposite.so.1", "libgnutls.so.30")
LIB32_CHECK = LIB32_CRITICAL + LIB32_OPTIONAL

# У одной и той же библиотеки имя пакета отличается между дистрибутивами:
# в ROSA 32-битные пакеты называются без префикса lib64, в Debian — с :i386,
# в Fedora-подобных — с .i686. Пробуем варианты по очереди.
LIB32_PACKAGE_NAMES = {
    "ld-linux.so.2": ["glibc.i686", "libc6:i386", "glibc"],
    "libc.so.6": ["libc6:i386", "glibc.i686", "glibc-devel.i686", "libc6"],
    "libfreetype.so.6": ["libfreetype6:i386", "freetype.i686", "libfreetype6",
                         "libfreetype.i686"],
    "libX11.so.6": ["libx11-6:i386", "libX11.i686", "libx11_6", "libx11-6"],
    "libGL.so.1": ["libgl1:i386", "libgl1-mesa-glx:i386", "mesa-libGL.i686",
                   "libmesagl1", "libglx-mesa0:i386"],
    "libasound.so.2": ["libasound2:i386", "alsa-lib.i686", "libalsa2"],
    "libXcomposite.so.1": ["libxcomposite1:i386", "libXcomposite.i686",
                           "libxcomposite1", "libxcomposite.i686"],
    "libgnutls.so.30": ["libgnutls30:i386", "gnutls.i686", "libgnutls30"],
}


def _is_elf32(path):
    """32-битная ли это библиотека. Пятый байт ELF-заголовка: 1 = 32 бита."""
    try:
        with open(path, "rb") as f:
            head = f.read(5)
        return head[:4] == b"\x7fELF" and head[4] == 1
    except (OSError, IndexError):
        return False

# Где в разных дистрибутивах лежат 32-битные библиотеки.
# Debian/Astra/Альт — в /usr/lib/i386-linux-gnu; Fedora-подобные — в /usr/lib;
# ROSA и М ОС — в /lib (64-битные при этом в /lib64). Без /lib проверка
# 32-битных библиотек на М ОС всегда возвращала «нет», хотя они стоят, —
# и наоборот, могла не заметить, что их нет.
LIB32_DIRS = ("/usr/lib/i386-linux-gnu", "/usr/lib32", "/lib/i386-linux-gnu",
              "/usr/lib/i686-linux-gnu", "/lib", "/lib32", "/usr/lib")


def _have_lib32(name):
    """Есть ли в системе именно 32-битный вариант библиотеки."""
    places = [os.path.join(d, name + "*") for d in LIB32_DIRS]
    for pattern in places:
        for path in globmod.glob(pattern):
            if _is_elf32(path):
                return True
    return False


def missing_lib32(only_critical=False):
    """Каких 32-битных библиотек не хватает.

    Проверяется не просто наличие файла, а его разрядность: на 64-битной
    системе одноимённый файл легко оказывается 64-битным, и тогда проверка
    врала бы в обе стороны."""
    names = LIB32_CRITICAL if only_critical else LIB32_CHECK
    return [n for n in names if not _have_lib32(n)]


def lib32_packages():
    """Пакеты с 32-битными библиотеками под текущий дистрибутив."""
    if PKG_FAMILY == "deb":
        return ["libc6:i386", "libfreetype6:i386", "libx11-6:i386", "libxext6:i386",
                "libgl1:i386", "libglx-mesa0:i386", "libgl1-mesa-dri:i386",
                "libasound2:i386", "libfontconfig1:i386", "libxrender1:i386",
                "libxcursor1:i386", "libxi6:i386",
                # XComposite: без него Wine рисует через GLXPixmap-заглушку,
                # и это одна из частых причин артефактов
                "libxcomposite1:i386", "libxrandr2:i386", "libxinerama1:i386",
                # gnutls: без него сыплются ошибки про шифрование
                "libgnutls30:i386", "libvulkan1:i386"]

    # На rpm-системах имена пакетов заранее не угадать: в Fedora это
    # freetype.i686, а в ROSA / М ОС того же пакета просто нет под таким
    # именем — dnf отвечает «Нет соответствия аргументу» и отменяет ВСЮ
    # установку целиком, включая те пакеты, которые существуют. Поэтому
    # спрашиваем у самого dnf, какой пакет даёт нужную библиотеку, и
    # подставляем только реально существующие имена.
    want = ["ld-linux.so.2", "libc.so.6", "libfreetype.so.6", "libX11.so.6",
            "libXext.so.6", "libGL.so.1", "libasound.so.2",
            "libfontconfig.so.1", "libXrender.so.1", "libXcursor.so.1",
            "libXi.so.6", "libXcomposite.so.1", "libXrandr.so.2",
            "libXinerama.so.1", "libgnutls.so.30", "libvulkan.so.1"]
    pkgs = []
    for soname in want:
        pkg = _pkg_from_provides(soname)
        if pkg and pkg not in pkgs:
            pkgs.append(pkg)
    return pkgs


def install_lib32_one(name, line, progress, cancel):
    """Ставит конкретную библиотеку, перебирая варианты имени пакета."""
    for pkg in LIB32_PACKAGE_NAMES.get(name, []):
        cmd = pkg_install_repo_cmd([pkg])
        if not cmd:
            continue
        if _stream(_privileged(cmd), lambda t, k="info": None,
                   progress, cancel) == 0 and _have_lib32(name):
            line(f"   ✓ {name} — поставлен пакет {pkg}", "ok")
            return True
    return _have_lib32(name)


def install_lib32(line, progress, cancel):
    """Ставит 32-битные библиотеки. На deb-системах сначала включает
    архитектуру i386 — без неё пакеты :i386 просто не найдутся."""
    if PKG_FAMILY == "deb":
        try:
            r = subprocess.run(["dpkg", "--print-foreign-architectures"],
                               capture_output=True, text=True, timeout=30)
            if "i386" not in (r.stdout or ""):
                line("→ Включаю поддержку 32-битных пакетов (i386)…", "run")
                if _stream(_privileged(["dpkg", "--add-architecture", "i386"]),
                           line, progress, cancel) != 0:
                    return False
                line("→ Обновляю списки пакетов (это займёт минуту)…", "run")
                _stream(_privileged(["apt-get", "update"]), line, progress, cancel)
        except (OSError, subprocess.SubprocessError):
            pass

    pkgs = lib32_packages()
    line(f"→ Ставлю 32-битные библиотеки ({len(pkgs)} пакетов): шрифты, X11, "
         "звук, графика…", "run")
    cmd = pkg_install_repo_cmd(pkgs)
    if not cmd:
        return False
    code = _stream(_privileged(cmd), line, progress, cancel)

    still = missing_lib32()
    if still:
        # Имена пакетов в дистрибутивах различаются: в ROSA 32-битные идут
        # без префикса lib64, в Debian с :i386, в Fedora с .i686.
        # Добираем поштучно, перебирая варианты имени.
        line(f"○ Не хватает: {', '.join(still)} — добираю по одному…", "warn")
        for name in still:
            if cancel():
                break
            if not install_lib32_one(name, line, progress, cancel):
                line(f"   ✗ {name}: подходящий пакет не найден", "warn")

    left = missing_lib32(only_critical=True)
    extra = [n for n in missing_lib32() if n not in left]
    if extra:
        line(f"○ Не установлены необязательные библиотеки: {', '.join(extra)}. "
             "Программа будет работать; возможны артефакты графики или "
             "сообщения про шифрование.", "warn")
    return not left


# Переменные, управляющие графикой. На этапе создания окружения (wineboot)
# они не нужны и опасны: программный растеризатор способен подвесить машину.
GRAPHICS_ENV_KEYS = ("LIBGL_ALWAYS_SOFTWARE", "LIBGL_ALWAYS_INDIRECT",
                     "mesa_glthread", "MESA_GL_VERSION_OVERRIDE",
                     "MESA_GLSL_VERSION_OVERRIDE", "MESA_LOADER_DRIVER_OVERRIDE",
                     "GALLIUM_DRIVER", "__GLX_VENDOR_LIBRARY_NAME",
                     "VK_ICD_FILENAMES", "WINEDLLOVERRIDES_GFX")

def _wine_busy_pids(prefix):
    """Процессы Wine, работающие в этом окружении.

    Ищем по переменной WINEPREFIX в окружении процесса: так находятся и
    winetricks, и сами windows-программы, запущенные в этом префиксе.
    Возвращает короткие описания вида '4937 dotNetFx40_Full_x86_x64.exe'."""
    out = []
    target = os.path.realpath(prefix)
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            with open(f"/proc/{pid}/environ", "rb") as f:
                env = f.read().decode("utf-8", "replace")
        except OSError:
            continue
        for part in env.split("\0"):
            if not part.startswith("WINEPREFIX="):
                continue
            if os.path.realpath(part.split("=", 1)[1]) != target:
                break
            try:
                with open(f"/proc/{pid}/comm", encoding="utf-8") as f:
                    name = f.read().strip()
            except OSError:
                name = "?"
            out.append(f"{pid} {name}")
            break
    return out


LOADER32 = "ld-linux.so.2"
LOADER32_DIRS = ("/lib", "/usr/lib", "/lib32", "/usr/lib32",
                 "/usr/lib/i386-linux-gnu", "/lib/i386-linux-gnu")


def have_loader32():
    """Есть ли 32-битный динамический загрузчик.

    Это самое первое, что нужно для запуска ЛЮБОГО 32-битного файла.
    Без него ядро не может запустить 32-битную часть Wine, и он падает
    с «could not load kernel32.dll, status c0000135». Коварство в том,
    что ldd в этом случае молчит («not a dynamic executable») и не
    показывает ни одной недостающей библиотеки — поэтому проверять
    загрузчик нужно отдельно, по файлу."""
    for d in LOADER32_DIRS:
        if os.path.exists(os.path.join(d, LOADER32)):
            return True
    return bool(globmod.glob("/lib*/" + LOADER32)
                or globmod.glob("/usr/lib*/" + LOADER32))


def _needed_sonames(path):
    """Список библиотек, нужных файлу, прочитанный прямо из ELF.

    readelf читает заголовок файла и не пытается его запускать, поэтому
    работает даже когда 32-битного загрузчика в системе ещё нет — в
    отличие от ldd, который в этом случае не выдаёт ничего."""
    for tool in (["readelf", "-d", path], ["objdump", "-p", path]):
        try:
            r = subprocess.run(tool, capture_output=True, text=True,
                               timeout=30, env=dict(os.environ, LC_ALL="C"))
        except (OSError, subprocess.SubprocessError):
            continue
        out = []
        for ln in (r.stdout or "").splitlines():
            if "NEEDED" not in ln:
                continue
            if "[" in ln and "]" in ln:
                name = ln.split("[", 1)[1].split("]", 1)[0].strip()
            else:
                name = ln.split()[-1].strip()
            if name and ".so" in name and name not in out:
                out.append(name)
        if out:
            return out
    return []


def wine32_missing_sonames(wine):
    """Каких 32-битных библиотек не хватает КОНКРЕТНОЙ сборке Wine.

    Список LIB32_CHECK — это наши догадки о том, что обычно нужно. Здесь же
    спрашиваем саму сборку: берём её 32-битные части (lib/wine/i386-unix/*.so)
    и смотрим через ldd, какие зависимости система не может разрешить. Именно
    это и даёт «could not load kernel32.dll, status c0000135» — Wine не может
    загрузить свою 32-битную половину, а не файл kernel32 как таковой.

    Возвращает список sonames вида ['libfreetype.so.6', ...]."""
    if not wine:
        return []
    root = os.path.dirname(os.path.dirname(os.path.realpath(wine)))
    targets = []
    for pat in (os.path.join(root, "lib*", "wine", "i386-unix", "ntdll.so"),
                os.path.join(root, "lib", "*", "wine", "i386-unix", "ntdll.so"),
                os.path.join(root, "lib*", "wine", "i386-unix", "win32u.so"),
                os.path.join(root, "lib*", "wine", "i386-unix", "winex11.so")):
        targets.extend(globmod.glob(pat))
    if not targets:
        return []

    # Загрузчик проверяем ПЕРВЫМ и отдельно: без него ldd ничего не покажет,
    # и выглядит это так, будто всё в порядке.
    missing = [] if have_loader32() else [LOADER32]

    # имена самих проверяемых файлов — чтобы не принять их за недостающие
    own = {os.path.basename(t) for t in targets}
    for path in targets[:4]:
        found_any = False
        try:
            # LC_ALL=C обязателен: в русской локали ldd пишет «не найдено»,
            # и проверка на «not found» ничего не находит.
            r = subprocess.run(["ldd", path], capture_output=True, text=True,
                               timeout=30, env=dict(os.environ, LC_ALL="C"))
        except (OSError, subprocess.SubprocessError):
            r = None
        for ln in ((r.stdout if r else "") or "").splitlines():
            if "=>" not in ln:
                continue
            found_any = True
            if "not found" not in ln:
                continue
            # строка вида «\tlibfreetype.so.6 => not found»
            name = ln.split("=>", 1)[0].strip()
            # берём только настоящие sonames и никогда — сами файлы Wine
            if not name or name in own or ".so" not in name:
                continue
            if name not in missing:
                missing.append(name)

        if found_any:
            continue
        # ldd промолчал (нет 32-битного загрузчика или файл он запускать
        # отказался) — читаем зависимости из самого файла и проверяем их
        # наличие по каталогам 32-битных библиотек.
        for name in _needed_sonames(path):
            if name in own or name in missing:
                continue
            if not _have_lib32(name):
                missing.append(name)
    return missing


def _pkg_guesses_for_soname(name):
    """Возможные имена пакета для библиотеки, если её нет в нашей таблице.

    Из 'libfoo.so.6' получаем 'libfoo6:i386', 'libfoo.i686' и т. п. —
    перебор дешевле, чем заставлять техника искать пакет вручную."""
    known = LIB32_PACKAGE_NAMES.get(name)
    if known:
        return list(known)
    base = name.split(".so")[0]                      # libfoo
    ver = name.split(".so.")[-1] if ".so." in name else ""
    out = []
    if PKG_FAMILY == "deb":
        # в Debian/Astra имена пакетов всегда в нижнем регистре:
        # libGL.so.1 → libgl1:i386, а не libGL1:i386
        low = base.lower()
        out += [f"{low}{ver}:i386", f"{low}:i386", f"{low}-{ver}:i386",
                f"{base}{ver}:i386", f"{base}:i386"]
    else:
        out += [f"{base}.i686", f"{base}{ver}.i686",
                f"{base.replace('lib', '', 1)}.i686"]
    # дубликаты ни к чему: каждая попытка — это запуск пакетного менеджера
    seen, uniq = set(), []
    for p in out:
        if p and p not in seen:
            seen.add(p)
            uniq.append(p)
    return uniq


def _pkg_from_provides(soname):
    """Спрашивает у пакетного менеджера, какой пакет даёт эту 32-битную
    библиотеку. Догадки по имени на ROSA/М ОС не работают: там 32-битная
    glibc называется просто glibc.i686 и ставит файл в /lib, а 64-битная
    зовётся так же — различает только суффикс архитектуры. Точный ответ
    даёт сам dnf:

        dnf provides */libc.so.6  →  glibc-6:2.33-...i686

    Возвращает имя пакета с архитектурой (glibc.i686) или None."""
    tool = PKG_MANAGER or ""
    if "dnf" in tool or "yum" in tool:
        cmd = [tool.split("/")[-1], "provides", f"*/{soname}"]
    elif "zypper" in tool:
        cmd = ["zypper", "--non-interactive", "what-provides", soname]
    else:
        return None
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                           env=dict(os.environ, LC_ALL="C"))
    except (OSError, subprocess.SubprocessError):
        return None

    for raw in (r.stdout or "").splitlines():
        token = raw.strip().split()[0] if raw.strip() else ""
        if not token.endswith((".i686", ".i586", ".i386")):
            continue
        arch = token.rsplit(".", 1)[1]
        nevra = token.rsplit(".", 1)[0]          # glibc-6:2.33-11.git5f08d1.7
        # имя пакета — всё до куска, который начинается с версии
        # (цифра либо эпоха вида «6:»)
        parts = nevra.split("-")
        name_parts = []
        for part in parts:
            if part and (part[0].isdigit() or ":" in part):
                break
            name_parts.append(part)
        name = "-".join(name_parts) or parts[0]
        return f"{name}.{arch}"
    return None


def repair_wine32(wine, line, progress, cancel):
    """Доставляет то, чего не хватает 32-битной части этой сборки Wine.

    Сначала общий набор (install_lib32), затем — точечно по выводу ldd:
    так закрываются и те библиотеки, которых нет в нашем списке, но без
    которых конкретно эта сборка не стартует."""
    gap = wine32_missing_sonames(wine)
    if not gap:
        return False
    line(f"⚠ 32-битной части Wine не хватает библиотек: {', '.join(gap)}", "warn")
    line("→ Доставляю их…", "run")
    install_lib32(line, progress, cancel)

    gap = wine32_missing_sonames(wine)
    for name in list(gap):
        if cancel():
            break
        # сначала — точный ответ пакетного менеджера, потом наши догадки
        exact = _pkg_from_provides(name)
        candidates = ([exact] if exact else []) + _pkg_guesses_for_soname(name)
        for pkg in candidates:
            cmd = pkg_install_repo_cmd([pkg])
            if not cmd:
                continue
            _stream(_privileged(cmd), lambda t, k="info": None, progress, cancel)
            if name not in wine32_missing_sonames(wine):
                line(f"   ✓ {name} — поставлен пакет {pkg}", "ok")
                break

    left = wine32_missing_sonames(wine)
    if left:
        line(f"○ Всё ещё не хватает: {', '.join(left)}", "warn")
        return False
    line("✓ Все зависимости 32-битной части Wine на месте", "ok")
    return True


WINETRICKS_CACHE = os.path.join(USER_HOME, ".cache", "winetricks")


def _cache_file_ok(path, size=None):
    """Файл на месте, нужного размера и это действительно установочный
    пакет Windows (MSI/EXE), а не HTML-страница с ошибкой."""
    if not os.path.exists(path):
        return False
    try:
        actual = os.path.getsize(path)
    except OSError:
        return False
    if size and actual != size:
        return False
    if actual < 100000:
        return False
    try:
        with open(path, "rb") as f:
            head = f.read(8)
    except OSError:
        return False
    return head.startswith(b"\xd0\xcf\x11\xe0") or head.startswith(b"MZ")


def seed_winetricks_cache(app, line, progress, cancel):
    """Заранее кладёт нужные файлы в кэш winetricks.

    Зачем: winetricks берёт часть компонентов (XNA) из веб-архива, а тот
    неправильно отвечает на многопоточные запросы — «Invalid range header»,
    и файл не докачивается никогда. Качаем сами, одним потоком, по цепочке
    источников, с проверкой результата."""
    for item in (app.get("winetricks_cache") or []):
        verb, name = item.get("verb", ""), item.get("file", "")
        size = item.get("size")
        if not verb or not name:
            continue
        target_dir = os.path.join(WINETRICKS_CACHE, verb)
        target = os.path.join(target_dir, name)

        # мусор от прерванных загрузок мешает проверке контрольной суммы
        for junk in globmod.glob(target + ".aria2") + globmod.glob(target + ".part"):
            try:
                os.remove(junk)
            except OSError:
                pass

        if _cache_file_ok(target, size):
            line(f"   Компонент {verb}: файл {name} уже готов", "info")
            continue
        if os.path.exists(target):
            line(f"   Компонент {verb}: файл в кэше битый, удаляю", "warn")
            try:
                os.remove(target)
            except OSError:
                pass

        # 1) файл могли положить рядом с установщиком — самый надёжный путь
        local = None
        for d in (os.path.join(INSTALLERS_DIR, app["id"]), INSTALLERS_DIR):
            cand = os.path.join(d, name)
            if os.path.exists(cand) and _cache_file_ok(cand, size):
                local = cand
                break
        if local:
            _user_makedirs(target_dir)
            try:
                shutil.copy2(local, target)
                _chown_to_user(target_dir)
                line(f"✓ Компонент {verb}: взят готовый файл из installers/", "ok")
                continue
            except OSError as e:
                line(f"   Не удалось скопировать {local}: {e}", "warn")

        # 2) качаем сами, по очереди из нескольких источников
        line(f"→ Компонент {verb}: скачиваю {name} заранее "
             "(winetricks берёт его из веб-архива и часто не может)", "run")
        got = False
        for url in item.get("urls", []):
            _user_makedirs(target_dir)
            if download_file(url, target, line, progress, cancel, reuse=False):
                if _cache_file_ok(target, size):
                    line(f"✓ Компонент {verb}: файл получен", "ok")
                    got = True
                    break
                line("   Скачалось что-то не то — пробую следующий источник", "warn")
                try:
                    os.remove(target)
                except OSError:
                    pass
        if not got:
            line(f"⚠ Компонент {verb}: скачать {name} не удалось.", "warn")
            line(f"   Надёжное решение для класса: найдите {name} один раз и "
                 f"положите в installers/{app['id']}/ — установщик возьмёт его "
                 "оттуда и в интернет больше не полезет.", "info")
        _chown_to_user(WINETRICKS_CACHE)


def wine_kill(prefix, wine=None, line=None, wait=6):
    """Гасит wineserver конкретного окружения.

    Обязательно делать перед удалением папки окружения: пока сервер жив, он
    держит файлы и пересоздаёт их, а следующий wineboot пытается достучаться
    до сервера уже удалённого окружения и виснет."""
    wine = wine or find_wine()
    if not wine:
        return
    server = os.path.join(os.path.dirname(os.path.realpath(wine)), "wineserver")
    if not os.path.exists(server):
        server = shutil.which("wineserver")
    if not server:
        return
    env = dict(os.environ)
    env["WINEPREFIX"] = prefix
    env.pop("PKEXEC_UID", None)
    if line:
        line("→ Останавливаю процессы Wine в этом окружении…", "run")
    for args in (["-k"], ["-k9"]):
        try:
            subprocess.run(_as_user([server] + args), env=env,
                           capture_output=True, timeout=30)
        except (OSError, subprocess.SubprocessError):
            pass
    # даём процессам действительно завершиться
    for _ in range(wait):
        try:
            r = subprocess.run(["pgrep", "-f", f"wineserver.*{os.path.basename(prefix)}"],
                               capture_output=True, timeout=5)
            if r.returncode != 0:
                break
        except (OSError, subprocess.SubprocessError):
            break
        time.sleep(1)


def remove_prefix(prefix, wine=None, line=None):
    """Безопасно удаляет окружение Wine.

    Раньше здесь сначала вызывался wine_kill. От этого пришлось отказаться:
    обращение к wineserver сборки, отличной от той, что создала окружение,
    на части машин (М ОС со встроенной графикой Intel) подвешивало систему
    целиком. Удаления файлов достаточно — процессы Wine, оставшиеся без
    своего префикса, завершаются сами."""
    if not os.path.isdir(prefix):
        return True
    shutil.rmtree(prefix, ignore_errors=True)
    if os.path.isdir(prefix):
        # что-то всё ещё держит файлы — пробуем ещё раз после паузы
        time.sleep(2)
        shutil.rmtree(prefix, ignore_errors=True)
    ok = not os.path.isdir(prefix)
    if line and not ok:
        line(f"⚠ Не удалось удалить {prefix} — закройте программы Wine "
             "и попробуйте снова.", "warn")
    return ok


def wine_env(prefix, arch, wine, extra=None):
    """Переменные окружения для Wine и winetricks.

    Критично передать WINE и WINESERVER: winetricks ищет команду wine в PATH
    и, если используется отдельно скачанная сборка, не находит её —
    «WINE is wine, which is neither on the path nor an executable file», и
    молча не ставит ни один компонент."""
    env = {
        "WINEPREFIX": prefix,
        "WINEARCH": arch,
        "WINEDEBUG": "-all",
        "DISPLAY": os.environ.get("DISPLAY", ":0"),
        # Отключаем попытку Wine самому скачать и поставить Gecko/Mono при
        # первом wineboot нового окружения — если сеть класса их не пускает,
        # wineboot не падает с ошибкой, а зависает в ожидании ответа сервера
        # или окна «установить компонент?», которое никто не видит.
        "WINEDLLOVERRIDES": "mscoree=,mshtml=",
    }
    # winetricks по умолчанию качает через aria2 в несколько потоков с
    # заголовком Range. Веб-архив, откуда берётся XNA, такие запросы
    # обрабатывает неправильно — «Invalid range header», и файл никогда не
    # докачивается. Однопоточный wget/curl эту проблему снимает.
    for downloader in ("wget", "curl"):
        if shutil.which(downloader):
            env["WINETRICKS_DOWNLOADER"] = downloader
            break

    if extra:
        # LC_ALL=C ломает пути с кириллицей («Рабочий стол»): Wine перестаёт
        # видеть файлы. Нужна английская локаль, но с кодировкой UTF-8.
        fixed = {}
        for k, v in extra.items():
            v = str(v)
            if k in ("LC_ALL", "LANG") and v.upper() in ("C", "POSIX"):
                v = "C.UTF-8"
            if k == "WINEDLLOVERRIDES":
                # не затираем базовое отключение mscoree/mshtml, а
                # дополняем его (например, переопределениями DirectX
                # из wine_env_profiles у Kodu)
                base = env.get("WINEDLLOVERRIDES", "")
                v = base + ("," if base and v else "") + v
            fixed[k] = v
        env.update(fixed)

    if wine:
        env["WINE"] = wine
        wine_bin = os.path.dirname(os.path.realpath(wine))
        server = os.path.join(wine_bin, "wineserver")
        if os.path.exists(server):
            env["WINESERVER"] = server
        # winetricks для части проверок зовёт wine64 отдельно. Если не указать
        # его явно, берётся СИСТЕМНЫЙ /usr/bin/wine64 — другая сборка, другое
        # представление об окружении, и получаем
        # «failed to open C:\windows\syswow64\regedit.exe c0000135».
        for name in ("wine64", "wine"):
            cand = os.path.join(wine_bin, name)
            if os.path.exists(cand):
                env["WINE64"] = cand
                break
        # и на всякий случай — чтобы вложенные вызовы тоже брали нашу сборку
        env["WINELOADER"] = wine
        # чтобы winetricks и вспомогательные утилиты брали ту же сборку
        env["PATH"] = wine_bin + os.pathsep + os.environ.get(
            "PATH", "/usr/local/bin:/usr/bin:/bin")
    return env


def wine_exe_for_arch(wine, arch):
    """Двоичный файл, который реально запускаем.

    В сборке рядом с 32-битным загрузчиком bin/wine лежит 64-битный
    bin/wine64. Для win64-окружения (оно умеет запускать и 32-битные
    Windows-программы через wow64) 32-битный загрузчик не нужен вовсе —
    а на хосте без 32-битных библиотек (нет /lib/ld-linux.so.2) он даже
    не стартует, хотя само окружение в них не нуждается. Поэтому для
    win64 предпочитаем wine64, когда он лежит рядом."""
    if not wine or arch != "win64":
        return wine
    cand = os.path.join(os.path.dirname(os.path.realpath(wine)), "wine64")
    return cand if os.path.exists(cand) else wine


def prefix_arch(prefix):
    """Разрядность существующего окружения Wine: win32, win64 или None.

    Wine записывает её в system.reg строкой #arch=. Если окружение уже
    создано другой разрядности, повторный wineboot падает с
    «could not load kernel32.dll, status c0000135»."""
    reg = os.path.join(prefix, "system.reg")
    try:
        with open(reg, encoding="utf-8", errors="replace") as f:
            for _ in range(20):
                line = f.readline()
                if not line:
                    break
                if line.startswith("#arch="):
                    return line.strip().split("=", 1)[1]
    except OSError:
        pass
    if os.path.isdir(os.path.join(prefix, "drive_c", "Program Files (x86)")):
        return "win64"
    if os.path.isdir(os.path.join(prefix, "drive_c")):
        return "win32"
    return None


def wine_supports_win32(wine):
    """Умеет ли эта сборка Wine создавать 32-битные окружения.

    Современные сборки «wow64» собраны без 32-битной части: они запускают
    32-битные программы внутри 64-битного окружения, но WINEARCH=win32
    отвергают — «WINEARCH is set to 'win32' but this is not supported in
    wow64 mode». Проверяем по наличию каталога i386-unix рядом со сборкой."""
    if not wine:
        return False
    real = os.path.realpath(wine)
    root = os.path.dirname(os.path.dirname(real))
    # Искать нужно именно i386-UNIX. Папка i386-windows есть и в сборках
    # wow64 (это PE-файлы 32-битных программ Windows), а вот 32-битная
    # часть самого Wine лежит в i386-unix — её у wow64 нет.
    # Нужны обе половины: i386-unix (сама 32-битная часть Wine) и
    # i386-windows (32-битные kernel32.dll и прочие). Без второй окружение
    # создаётся, но падает с «could not load kernel32.dll».
    roots = [os.path.join(root, "lib*", "wine"),
             os.path.join(root, "lib", "*", "wine")]
    # Общесистемные пути /usr/lib*/wine добавляем ТОЛЬКО когда проверяем
    # именно системный Wine (сам бинарник лежит под /usr). Раньше эти два
    # пути стояли здесь безусловно — и тогда, если в системе стоит
    # ПОЛНОЦЕННЫЙ системный Wine, проверка скачанной отдельно сборки
    # (например, wine-9.2 для Kodu) находила 32-битные файлы СИСТЕМНОГО
    # Wine и считала скачанную сборку рабочей, хотя проверялись чужие
    # файлы. В логе это выглядело как «32-битные окружения: поддерживаются»
    # при реальной ошибке «could not load kernel32.dll, status c0000135» —
    # скачанная сборка была не при чём, отвечал системный Wine.
    if real.startswith("/usr/"):
        roots += ["/usr/lib*/wine", "/usr/lib/*/wine"]
    for pat in roots:
        for base in globmod.glob(pat):
            has_unix = os.path.isdir(os.path.join(base, "i386-unix"))
            has_pe = (os.path.exists(os.path.join(base, "i386-windows",
                                                  "kernel32.dll"))
                      or os.path.isdir(os.path.join(base, "i386-windows")))
            if has_unix and has_pe:
                return True
    return False


def wine_can_run_win32(wine):
    """Может ли эта сборка запускать 32-битные программы.

    Важно не только для окружений win32: почти любой установщик компонентов
    (vcrun2008, dotnet и подобные) содержит 32-битные части, и в 64-битном
    окружении они живут в папке syswow64. Отдельный загрузчик wine64 их
    запустить не может, и получается ошибка c0000135.
    """
    if not wine:
        return False
    if wine_supports_win32(wine):
        return True
    # современные сборки wow64 (один загрузчик wine, версия 9+) умеют
    # 32-битные программы внутри 64-битного окружения
    if os.path.basename(os.path.realpath(wine)) == "wine64":
        return False
    ver = wine_version_tuple(wine)
    return bool(ver and ver >= (9, 0))


WINE_BAD_MAJOR = 11
# Версии, на которых 32-битные окружения собираются надёжно. Берём их по
# очереди вместо «последнего релиза»: в свежих ветках (11.x) на части машин
# подготовка окружения вешает систему целиком.
WINE_WIN32_VERSIONS = ("9.2", "10.0", "9.0", "8.0")


def wine_with_win32(line=None):
    """Ищет среди доступных сборок ту, что умеет 32-битные окружения.

    Сборки ветки 11.x пропускаем: на ряде машин (в частности на М ОС с
    встроенной графикой Intel) wineboot в них подвешивает не программу,
    а весь компьютер. Берём их только если совсем ничего другого нет."""
    risky = []
    for path, origin in wine_candidates():
        if not wine_supports_win32(path):
            continue
        ver = wine_version_tuple(path)
        if ver and ver[0] >= WINE_BAD_MAJOR:
            risky.append((path, origin, ver))
            continue
        if line:
            line(f"→ Для 32-битного окружения беру {path} "
                 f"({wine_version(path) or ''}, {origin})", "info")
        return path
    if risky:
        path, origin, ver = risky[0]
        if line:
            line(f"○ Других сборок с 32-битной частью нет — беру "
                 f"{wine_version(path) or path} ({origin}). На этой ветке Wine "
                 "подготовка окружения иногда подвисает; если это повторится, "
                 "скачайте сборку 9.2 или 10.0 через «🍷 Настройки Wine».",
                 "warn")
        return path
    return None


WINE_BUILDS_REPO = "Kron4ek/Wine-Builds"


def download_wine_with_win32(line, progress, cancel):
    """Скачивает сборку Wine, умеющую 32-битные окружения.

    Нужна там, где программе обязателен win32 (например .NET для Kodu):
    в 64-битном окружении winetricks не может поставить dotnet48 —
    установщик Microsoft завершается со статусом 67.

    Берём не «последний релиз», а проверенные версии по очереди: в свежих
    ветках (11.x) подготовка 32-битного окружения на части машин вешает
    систему. Внутри версии предпочитаем чисто 32-битную сборку (x86):
    в ней 32-битная часть есть всегда, тогда как в amd64-сборках её
    может не быть вовсе."""
    for want in WINE_WIN32_VERSIONS:
        if cancel and cancel():
            return None
        line(f"→ Ищу сборку Wine {want} с 32-битной частью…", "run")
        item = find_wine_build_version(want, line, want_x86=True)
        if not item:
            continue
        path = install_wine_build(item, line, progress, cancel)
        if not path:
            continue
        if not wine_supports_win32(path):
            line(f"   В сборке {item['name']} 32-битной части нет — "
                 "пробую следующую версию.", "warn")
            continue
        line(f"✓ Подходит: {wine_version(path) or want}", "ok")
        return path
    line("✗ Не удалось получить сборку Wine с 32-битной частью.", "err")
    return None


def _download_wine_latest_win32(line, progress, cancel):
    """Последний релиз — крайний случай, когда проверенных версий нет."""
    line("→ Скачиваю сборку Wine с 32-битной поддержкой "
         f"({WINE_BUILDS_REPO})…", "run")
    data = _gh_api(f"https://api.github.com/repos/{WINE_BUILDS_REPO}/releases/latest")
    if data is None:
        for part in (GH_LAST_ERROR or "GitHub недоступен").split("\n"):
            if part.strip():
                line("   " + part.strip(), "warn")
        return None

    best = None
    for a in data.get("assets", []):
        name = a.get("name", "")
        low = name.lower()
        if "wow64" in low or not low.endswith((".tar.xz", ".tar.gz")):
            continue
        if "amd64" not in low or "arm" in low:
            continue
        # обычная сборка предпочтительнее staging: она стабильнее
        score = 10 - (3 if "staging" in low else 0) - (5 if "tkg" in low else 0)
        if best is None or score > best[0]:
            best = (score, a)
    if not best:
        line("✗ В последнем релизе нет сборки без wow64.", "err")
        return None

    asset = best[1]
    line(f"→ Выбрана сборка: {asset['name']} "
         f"({asset.get('size', 0) // 1048576} МБ)", "info")
    dest = download_file(asset["browser_download_url"],
                         os.path.join(WINE_BUILDS_DIR, asset["name"]),
                         line, progress, cancel)
    if not dest:
        return None

    target = os.path.join(WINE_BUILDS_DIR, _strip_ext(asset["name"]))
    if os.path.isdir(target):
        shutil.rmtree(target, ignore_errors=True)
    _user_makedirs(target)
    line("→ Распаковываю…", "run")
    try:
        extract_archive(dest, target)
    except Exception as e:
        line(f"✗ Не удалось распаковать: {e}", "err")
        return None

    found = sorted(globmod.glob(os.path.join(target, "**", "bin", "wine"),
                                recursive=True))
    for path in found:
        try:
            for f in globmod.glob(os.path.join(os.path.dirname(path), "*")):
                os.chmod(f, 0o755)
        except OSError:
            pass
        if wine_supports_win32(path):
            _chown_to_user(WINE_BUILDS_DIR)
            st = load_settings()
            st["wine_binary"] = path
            save_settings(st)
            line(f"✓ Установлена сборка с 32-битной поддержкой: "
                 f"{wine_version(path) or path}", "ok")
            return path
    line("✗ В скачанной сборке всё равно нет 32-битной части.", "err")
    return None


def wine_version_tuple(path):
    """Версия Wine числами, например (9, 2). Нужна, чтобы предупредить, когда
    в системе слишком старый Wine: часть исправлений появляется только в
    конкретных версиях (например, поддержка Kodu — начиная с wine-9.2)."""
    text = wine_version(path)
    m = re.search(r"(\d+)\.(\d+)", text or "")
    if not m:
        return None
    return (int(m.group(1)), int(m.group(2)))


def check_wine_version(app, wine, line):
    """Предупреждает, если Wine старее, чем нужно программе."""
    need = app.get("wine_min_version")
    if not need:
        return True
    parts = str(need).split(".")
    try:
        need_t = (int(parts[0]), int(parts[1]) if len(parts) > 1 else 0)
    except ValueError:
        return True
    have = wine_version_tuple(wine)
    if not have:
        return True
    if have >= need_t:
        line(f"→ Версия Wine: {have[0]}.{have[1]} — подходит "
             f"(нужна не ниже {need}).", "info")
        return True
    line(f"⚠ В системе Wine {have[0]}.{have[1]}, а этой программе нужен "
         f"не ниже {need}.", "warn")
    if app.get("wine_version_reason"):
        line("   " + app["wine_version_reason"], "warn")
    line("   Установка продолжится, но программа, скорее всего, не запустится. "
         "Надёжное решение: «🍷 Настройки Wine» → «⬇ Скачать свежий Wine…» — "
         "отдельная сборка в домашнюю папку, системный Wine не трогается.", "warn")
    return False


def wine_version(path):
    """Строка версии. Если 32-битный загрузчик не может стартовать (нет
    32-битных библиотек хоста — «No such file or directory» на самом
    исполнении, а не на отсутствии файла), пробуем соседний wine64: версия
    у обоих загрузчиков одной сборки одинаковая."""
    candidates = [path]
    if path:
        cand64 = os.path.join(os.path.dirname(os.path.realpath(path)), "wine64")
        if os.path.exists(cand64) and cand64 != path:
            candidates.append(cand64)
    for exe in candidates:
        try:
            r = subprocess.run([exe, "--version"], capture_output=True, text=True, timeout=20)
            if r.returncode == 0:
                lines = (r.stdout or r.stderr or "").strip().splitlines()
                if lines:
                    return lines[0]
        except (OSError, subprocess.SubprocessError, IndexError):
            continue
    return ""


def pe_arch(path):
    """Разрядность Windows-программы по заголовку PE: 'win32', 'win64' или None.

    Нужно, чтобы не создать 32-битное окружение под 64-битную программу —
    Wine тогда говорит «Bad EXE format» и ничего не запускает."""
    try:
        with open(path, "rb") as f:
            if f.read(2) != b"MZ":
                return None
            f.seek(0x3C)
            off = int.from_bytes(f.read(4), "little")
            f.seek(off)
            if f.read(4) != b"PE\0\0":
                return None
            machine = int.from_bytes(f.read(2), "little")
    except (OSError, ValueError):
        return None
    if machine == 0x014C:
        return "win32"
    if machine in (0x8664, 0xAA64):
        return "win64"
    return None


def choose_wine_arch(app, exe_path, line=None):
    """Разрядность окружения.

    По умолчанию win64: такое окружение запускает и 64-битные, и 32-битные
    программы, поэтому подходит сразу для всех версий (например, и для
    Algodoo 2.1.0 32-бит, и для 2.2.4 64-бит). win32 нужен только там, где
    этого требуют компоненты — .NET 4.8 и XNA ставятся именно в 32-битное
    окружение, поэтому у Kodu разрядность задана явно."""
    if app.get("wine_arch"):
        return app["wine_arch"]
    detected = pe_arch(exe_path) if exe_path else None
    if detected == "win32":
        # Для 32-битной программы родное окружение — win32: именно так
        # собраны проверенные рецепты (PlayOnLinux, AUR). win64 такую
        # программу тоже запустит, но только если сборка Wine умеет
        # 32-битный режим, поэтому проверяем.
        if wine_with_win32():
            if line:
                line("→ Программа 32-битная — окружение win32 "
                     "(так собраны проверенные рецепты)", "info")
            return "win32"
        if line:
            line("→ Программа 32-битная, но сборка Wine не умеет 32-битные "
                 "окружения — создам win64, он их тоже запускает", "warn")
        return "win64"
    if detected == "win64" and line:
        line("→ Программа 64-битная — окружение win64", "info")
    return "win64"


def find_wine(app_id=None):
    """Wine для работы.

    Сначала — сборка, закреплённая за конкретной программой (у Kodu, например,
    работает только старая версия), затем выбранная техником в настройках,
    затем системная."""
    st = load_settings()
    if app_id:
        per_app = (st.get("wine_by_app") or {}).get(app_id)
        if per_app and os.path.exists(per_app):
            return per_app
    chosen = st.get("wine_binary")
    if chosen and os.path.exists(chosen):
        return chosen
    # сначала скачанные сборки: системный wine64 без 32-битной части
    # не умеет ставить компоненты и запускать половину программ
    for path, _origin in wine_candidates():
        if wine_can_run_win32(path):
            return path
    return shutil.which("wine") or shutil.which("wine64")


def set_wine_for_app(app_id, path):
    """Закрепляет сборку Wine за программой."""
    st = load_settings()
    by_app = st.setdefault("wine_by_app", {})
    if path:
        by_app[app_id] = path
    else:
        by_app.pop(app_id, None)
    save_settings(st)


def find_component_file(app, item, line, progress, cancel):
    """Ищет файл компонента: рядом с установщиком, в кэше winetricks,
    иначе качает по списку источников."""
    name = item.get("file", "")
    size = item.get("size")
    if not name:
        return None

    places = [os.path.join(INSTALLERS_DIR, app["id"], name),
              os.path.join(INSTALLERS_DIR, name),
              os.path.join(WINETRICKS_CACHE, item.get("verb", ""), name)]
    for cand in places:
        if _cache_file_ok(cand, size):
            line(f"   {name}: беру готовый файл ({cand})", "info")
            return cand

    for url in item.get("urls", []):
        dest = os.path.join(INSTALLERS_DIR, app["id"], name)
        if download_file(url, dest, line, progress, cancel, reuse=False):
            if _cache_file_ok(dest, size):
                return dest
            line("   Скачалось что-то не то — пробую следующий источник", "warn")
            try:
                os.remove(dest)
            except OSError:
                pass
    return None


def install_wine_msi(app, item, env, wine, line, progress, cancel):
    """Ставит .msi прямо через msiexec внутри Wine.

    Так надёжнее, чем через winetricks: тот тянет файл из веб-архива и
    часто не может. Рецепт из ветки WineHQ по Kodu: сначала dotnet48,
    затем xnaredist.msi, и только потом сама программа."""
    path = find_component_file(app, item, line, progress, cancel)
    if not path:
        line(f"✗ Файл {item.get('file')} не найден и скачать его не удалось.", "err")
        line(f"   Положите его в installers/{app['id']}/ и повторите установку.",
             "warn")
        return False

    path = _ascii_copy(path, line)
    title = item.get("name", os.path.basename(path))
    line(f"→ Ставлю {title} внутри Wine (msiexec)…", "run")
    args = item.get("args") or ["/quiet", "/norestart"]
    code = _stream_env([wine, "msiexec", "/i", path] + list(args),
                       env, line, progress, cancel)
    if code == -99:
        return None

    # Проверка по файлам: их может быть несколько вариантов размещения.
    # Например XNA кладёт библиотеки и в Program Files\Common Files, и в GAC —
    # в зависимости от версии Windows в окружении.
    checks = item.get("check_glob") or []
    if isinstance(checks, str):
        checks = [checks]
    found = []
    for pattern in checks:
        found += globmod.glob(os.path.join(env["WINEPREFIX"], "drive_c", pattern),
                              recursive=True)
    if found:
        line(f"✓ {title}: установлено ({len(found)} файлов)", "ok")
        return True

    # Главный признак — код возврата msiexec. Отсутствие файлов по нашим
    # шаблонам ещё не значит, что установка не прошла: раскладка отличается
    # между версиями Windows и самих пакетов.
    if code == 0:
        line(f"✓ {title}: установщик завершился успешно", "ok")
        if checks:
            line("   (файлы лежат не там, где мы их искали — это нормально)",
                 "info")
        return True

    line(f"✗ {title}: msiexec вернул код {code}, файлов тоже нет", "err")
    return False


def _ascii_copy(path, line=None):
    """Если в пути есть нелатинские символы, копирует файл во временную
    папку с латинским путём.

    Wine и часть установщиков Windows не умеют работать с путями вроде
    /home/admin/Рабочий стол/… — файл просто «не найден»."""
    try:
        path.encode("ascii")
        return path
    except UnicodeEncodeError:
        pass
    safe_dir = os.path.join(DATA_DIR, "tmp")
    try:
        _user_makedirs(safe_dir)
        safe = os.path.join(safe_dir, re.sub(r"[^\w.+-]", "_",
                                             os.path.basename(path)))
        if not (os.path.exists(safe)
                and os.path.getsize(safe) == os.path.getsize(path)):
            shutil.copy2(path, safe)
            _chown_to_user(safe_dir)
        if line:
            line("   В пути к файлу есть кириллица — Wine с такими путями не "
                 f"работает, копирую во временную папку: {safe}", "info")
        return safe
    except OSError as e:
        if line:
            line(f"   Не удалось скопировать файл в латинский путь: {e}", "warn")
        return path


def apply_file_profile(app, src, line=None):
    """Подбирает настройки под конкретный файл установщика.

    У одной программы разные сборки ведут себя по-разному: у Algodoo
    проверенная 2.1.0 Win32 требует 32-битного окружения, а свежая 2.2.4 —
    64-битного. Профиль выбирается по имени файла."""
    profiles = app.get("file_profiles") or []
    if not profiles or not src:
        return app
    name = os.path.basename(src)
    for prof in profiles:
        pattern = prof.get("match")
        if not pattern or not re.search(pattern, name, re.I):
            continue
        tuned = dict(app)
        for key, value in prof.items():
            if key in ("match", "name"):
                continue
            if key == "wine_env_extra":
                merged = dict(app.get("wine_env_extra") or {})
                merged.update(value)
                tuned[key] = merged
            else:
                tuned[key] = value
        if line:
            line(f"→ Файл опознан: {prof.get('name', name)} — применяю "
                 "проверенные настройки для него", "ok")
        return tuned
    return app


def wine_preflight(app, wine, arch, line, progress=None, cancel=None):
    """Проверка окружения ПЕРЕД установкой Windows-программы.

    Смысл: выявить причину заранее и сказать, что делать, а не ловить
    непонятную ошибку в середине долгой установки.

    Возвращает (список критичных проблем, какой Wine использовать,
    какую разрядность окружения создавать). Сборка и разрядность могут быть
    заменены автоматически, чтобы не требовать ручных действий."""
    fatal = []
    line("→ Проверяю готовность Wine…", "run")

    if not wine:
        fatal.append("Wine не установлен")
        return fatal, wine, arch

    ver = wine_version_tuple(wine)
    line(f"   Wine: {wine_version(wine) or wine}", "info")
    if ver and ver < (6, 0):
        line("⚠ Wine очень старый — многие программы на нём не работают. "
             "Возьмите свежую сборку: «🍷 Настройки Wine» → «⬇ Скачать свежий "
             "Wine…»", "warn")

    # wineserver обязателен; без него wine «запускается» и молча ничего не делает
    wineserver = shutil.which("wineserver") or os.path.join(
        os.path.dirname(wine), "wineserver")
    if not os.path.exists(wineserver):
        fatal.append("не найден wineserver — пакет wine установлен не полностью")

    # 32-битные программы нужны почти всегда: установщики компонентов
    # (vcrun2008, dotnet) содержат 32-битные части даже в 64-битном
    # окружении. Отдельный загрузчик wine64 их не запускает.
    if not wine_can_run_win32(wine):
        line("⚠ Эта сборка Wine не умеет запускать 32-битные программы "
             f"({os.path.basename(os.path.realpath(wine))}). Компоненты вроде "
             "vcrun2008 в ней не поставятся.", "warn")
        better = None
        for path, origin in wine_candidates():
            if wine_can_run_win32(path):
                better = path
                line(f"✓ Беру сборку с поддержкой 32-битных программ: "
                     f"{wine_version(path) or path} ({origin})", "ok")
                break
        if not better and progress and cancel:
            better = download_wine_with_win32(line, progress, cancel)
        if better:
            wine = better
            set_wine_for_app(app["id"], wine)
        else:
            fatal.append("нет сборки Wine, способной запускать 32-битные "
                         "программы")
            line("   Поставьте 32-битную часть Wine вручную:", "warn")
            if PKG_FAMILY == "deb":
                line("     sudo dpkg --add-architecture i386 && "
                     "sudo apt-get update && sudo apt-get install wine32", "info")
            else:
                line("     sudo dnf install wine-core-32bit", "info")
            return fatal, wine, arch

    # 32-битная поддержка. Проверяем по файлам самой сборки: у отдельно
    # скачанного Wine они свои, а сборки «wow64» 32-битных окружений
    # не поддерживают вовсе.
    if wine_supports_win32(wine):
        # Эта проверка нужна не только для win32-окружений: сборки со
        # своей 32-битной частью (i386-unix) используют её и внутри
        # win64-окружения, чтобы запускать 32-битные Windows-программы
        # (компоненты winetricks, msiexec, сам .exe). Без 32-битных
        # библиотек хоста эта часть тихо не создаётся — например,
        # syswow64 остаётся пустым, а regedit/msiexec падают с c0000135,
        # хотя сам wineboot отрабатывает без ошибок.
        if arch == "win32":
            line("   32-битные окружения: поддерживаются", "info")
        # Проверяем не только наш список библиотек, но и реальные
        # зависимости самой сборки: именно их нехватка даёт
        # «could not load kernel32.dll, status c0000135».
        deps = wine32_missing_sonames(wine)
        if deps:
            line(f"⚠ 32-битной части Wine не хватает: {', '.join(deps)} — "
                 "без них окружение не создастся.", "warn")
            if progress and cancel:
                repair_wine32(wine, line, progress, cancel)
        gap = missing_lib32()
        if gap:
            line(f"⚠ Нет 32-битных библиотек: {', '.join(gap)}. "
                 "Без них Wine не найдёт шрифты и графику — будет "
                 "«Wine cannot find the FreeType font library».", "warn")
            if progress and cancel and install_lib32(line, progress, cancel):
                line("✓ 32-битные библиотеки установлены", "ok")
            else:
                gap = missing_lib32(only_critical=True)
                if gap:
                    fatal.append("не хватает 32-битных библиотек: "
                                 + ", ".join(gap))
                    line("   Поставьте вручную:", "warn")
                    if PKG_FAMILY == "deb":
                        line("     sudo dpkg --add-architecture i386", "info")
                        line("     sudo apt-get update", "info")
                        line("     sudo apt-get install "
                             + " ".join(lib32_packages()), "info")
                    else:
                        line("     sudo dnf install "
                             + " ".join(lib32_packages()), "info")
    else:
        if arch == "win32":
            line("⚠ Эта сборка Wine не умеет создавать 32-битные окружения "
                 "(вариант wow64).", "warn")
            other = wine_with_win32(line)
            if other:
                line("✓ Нашлась другая сборка с 32-битной поддержкой — "
                     "беру её.", "ok")
                return fatal, other, arch

            # Программам с .NET 64-битное окружение не подходит: winetricks
            # не может поставить туда dotnet48 (установщик Microsoft
            # завершается со статусом 67). Поэтому для них не подменяем
            # разрядность, а сами качаем правильную сборку Wine.
            needs32 = app.get("wine_needs_win32") or any(
                t.startswith("dotnet") for t in (app.get("wine_tricks") or []))
            if needs32:
                line("   Этой программе нужен именно 32-битный вариант: в "
                     "64-битное окружение .NET не устанавливается.", "warn")
                fresh = download_wine_with_win32(line, progress, cancel)
                if fresh:
                    gap = missing_lib32()
                    if gap:
                        line(f"⚠ Для 32-битного Wine не хватает библиотек: "
                             f"{', '.join(gap)} — доставляю…", "warn")
                        if not install_lib32(line, progress, cancel):
                            gap = missing_lib32(only_critical=True)
                            if gap:
                                fatal.append("не хватает 32-битных библиотек: "
                                             + ", ".join(gap))
                                line("   Поставьте вручную:", "warn")
                                if PKG_FAMILY == "deb":
                                    line("     sudo dpkg --add-architecture i386 "
                                         "&& sudo apt-get update", "info")
                                    line("     sudo apt-get install "
                                         + " ".join(lib32_packages()), "info")
                                else:
                                    line("     sudo dnf install "
                                         + " ".join(lib32_packages()), "info")
                                return fatal, fresh, arch
                        else:
                            line("✓ 32-битные библиотеки установлены", "ok")
                    return fatal, fresh, arch
                fatal.append("нужна сборка Wine с 32-битной частью, а скачать "
                             "её не удалось")
                line("   Поставьте вручную любой из вариантов:", "warn")
                if PKG_FAMILY == "deb":
                    line("     sudo dpkg --add-architecture i386 && "
                         "sudo apt-get update && sudo apt-get install wine32", "info")
                else:
                    line("     sudo dnf install wine-core-32bit  "
                         "(или wine-32bit / wine-i386)", "info")
                line("   Либо «🍷 Настройки Wine» → «⬇ Скачать свежий Wine…» и "
                     "выбрать файл БЕЗ wow64 в названии.", "info")
                return fatal, wine, arch

            # Остальным программам 64-битное окружение подходит: wow64-сборки
            # запускают в нём и 32-битные программы.
            line("✓ Создам 64-битное окружение: wow64-сборки запускают в нём "
                 "и 32-битные программы.", "ok")
            arch = "win64"
    # место на диске: окружение с .NET и XNA занимает около 2 ГБ
    try:
        free = shutil.disk_usage(os.path.dirname(WINE_ROOT) or "/").free // (1024 ** 3)
        line(f"   Свободно на диске: {free} ГБ", "info")
        if free < 3:
            line("⚠ Меньше 3 ГБ свободного места. Окружению Wine с компонентами "
                 "нужно около 2 ГБ, установка может оборваться на середине.", "warn")
    except OSError:
        pass

    # графика: без неё установщик покажет пустой экран
    if not (os.environ.get("DISPLAY") or os.environ.get("WAYLAND_DISPLAY")
            or user_session_env(os.getuid()).get("DISPLAY")):
        fatal.append("нет доступа к графическому экрану (DISPLAY) — "
                     "мастер установки показать негде")

    if app.get("wine_tricks") and not find_winetricks():
        line("⚠ winetricks не найден — программа попробует скачать его сама "
             "при установке компонентов.", "warn")

    if not fatal:
        line("   Готовность Wine: всё в порядке", "ok")
    return fatal, wine, arch


class WineInstaller(BaseInstaller):
    """Windows-программа под Wine. У каждой программы своё отдельное
    окружение (префикс) в ~/.local/share/KoderLab/wine/<id> — если одна
    сломается, остальные это не заденет."""

    def _boot_env(self, app, arch=None, wine=None):
        """Окружение для wineboot — без настроек графики.

        wineboot только создаёт структуру папок и реестр, рисовать ему
        нечего. А переданный сюда LIBGL_ALWAYS_SOFTWARE включает
        программный растеризатор llvmpipe, и на машинах со встроенной
        графикой Intel подготовка окружения вешает не программу, а всю
        систему. Настройки графики нужны при ЗАПУСКЕ программы и
        подставляются там (wine_env_profiles)."""
        extra = dict(app.get("wine_env_extra") or {})
        for key in list(extra):
            if key in GRAPHICS_ENV_KEYS or key.startswith(("MESA_", "LIBGL_",
                                                           "VK_", "GALLIUM_")):
                extra.pop(key, None)
        return wine_env(wine_prefix(app["id"]),
                        arch or read_marker(app["id"]).get("wine_arch")
                        or app.get("wine_arch") or "win64",
                        wine or find_wine(app["id"]),
                        extra)

    def _env(self, app, arch=None, wine=None):
        return wine_env(wine_prefix(app["id"]),
                        arch or read_marker(app["id"]).get("wine_arch")
                        or app.get("wine_arch") or "win64",
                        wine or find_wine(app["id"]),
                        app.get("wine_env_extra"))

    def install(self, app, line, progress, cancel):
        src = ensure_local_file(app, line, progress, cancel)
        if not src:
            line("   Нужен обычный Windows-установщик (.exe) с сайта программы — "
                 "он будет запущен внутри Wine.", "info")
            return "error"
        app = apply_file_profile(app, src, line)

        wine = find_wine(app["id"])
        if not wine:
            line("○ Wine в системе не найден — без него Windows-программы "
                 "не запускаются.", "warn")
            install_dependency(_pick_packages(WINE_PACKAGES), "Wine", line, progress, cancel)
            wine = find_wine(app["id"])
        if not wine:
            line("✗ Wine поставить не удалось. Поставьте вручную и повторите:", "err")
            line("   ROSA:            sudo dnf install wine", "info")
            line("   Альт / М ОС:     sudo apt-get install wine", "info")
            line("   Astra / Debian:  sudo apt-get install wine", "info")
            return "error"

        # нужная программе версия Wine (для Kodu — 9.2)
        preferred = ensure_wine_version(app, line, progress, cancel or (lambda: False))
        if preferred:
            wine = preferred

        check_wine_version(app, wine, line)

        arch = choose_wine_arch(app, src, line)
        problems, wine, arch = wine_preflight(
            app, wine, arch, line, progress, cancel or (lambda: False))
        if problems:
            line(f"✗ {app['name']}: установка не начата — сначала нужно "
                 "устранить:", "err")
            for pr in problems:
                line(f"   • {pr}", "err")
            line("   Команды для исправления показаны выше. После этого "
                 "нажмите «Установить» снова.", "warn")
            return "error"

        wine = wine_exe_for_arch(wine, arch)
        prefix = wine_prefix(app["id"])
        existing_arch = prefix_arch(prefix)
        if existing_arch and existing_arch != arch:
            line(f"○ Существующее окружение — {existing_arch}, а сейчас нужно "
                 f"{arch}. Пересоздаю его под нужную разрядность…", "warn")
            shutil.rmtree(prefix, ignore_errors=True)
        prefix = _user_makedirs(prefix)
        env = self._boot_env(app, arch, wine)
        line(f"→ Готовлю окружение Wine ({env['WINEARCH']}) в {prefix}…", "run")
        line("   Первый раз это занимает 1–3 минуты и может показать окно "
             "«установить Mono/Gecko» — соглашайтесь.", "info")
        out = []
        code = _stream_env([wine, "wineboot", "-u"], env, line, progress, cancel,
                           collect=out)
        if code == -99:
            return "cancelled"

        # Страховка на случай, если проверка чего-то не увидела: Wine сам
        # сказал, что win32 не поддерживается — пересоздаём как win64 и
        # продолжаем, не требуя ничего от техника.
        if code != 0 and env["WINEARCH"] == "win32" and \
                any("wow64 mode" in t for t in out):
            line("↯ Wine отказался создавать 32-битное окружение (сборка "
                 "wow64). Пересоздаю как 64-битное и продолжаю — в нём "
                 "32-битные программы тоже работают.", "warn")
            shutil.rmtree(prefix, ignore_errors=True)
            prefix = _user_makedirs(wine_prefix(app["id"]))
            arch = "win64"
            wine = wine_exe_for_arch(wine, arch)
            env = self._boot_env(app, arch, wine)
            code = _stream_env([wine, "wineboot", "-u"], env, line, progress, cancel)
            if code == -99:
                return "cancelled"

        if code != 0 or not os.path.isdir(os.path.join(prefix, "drive_c")):
            line(f"✗ Окружение Wine не создалось (код {code}) — установка "
                 "остановлена, чтобы не наделать мусора.", "err")
            line(f"   Проверьте владельца папки: ls -ld {prefix}", "warn")
            line(f"   Если она принадлежит root, исправьте: "
                 f"sudo chown -R $USER: {os.path.dirname(prefix)}", "warn")
            line("   И запускайте установщик без sudo: ./start.sh", "warn")
            return "error"

        # окружение создано — дальше работаем с полным набором переменных
        env = self._env(app, arch, wine)

        winver = app.get("wine_winver")
        if winver:
            line(f"→ Ставлю версию Windows: {winver}", "run")
            _stream_env([wine, "winecfg", "-v", winver], env, line, progress, cancel)

        tricks = app.get("wine_tricks") or []
        if tricks:
            wt = find_winetricks()
            if not wt:
                install_dependency(_pick_packages(WINETRICKS_PACKAGES), "winetricks",
                                   line, progress, cancel)
            # старый winetricks обновляем молча и сами — кнопку нажимать не нужно
            wt = ensure_winetricks(line, progress, cancel)
            if wt:
                # Wine ставит в новое окружение собственный Mono. Программы на
                # .NET цепляются именно за него и падают с NullReferenceException,
                # поэтому перед установкой настоящего .NET Mono надо убрать.
                if any(t.startswith("dotnet") for t in tricks):
                    line("→ Убираю встроенный Mono из окружения "
                         "(иначе .NET-программа подхватит его вместо настоящего "
                         ".NET и упадёт)…", "run")
                    _stream_env([wt, "-q", "remove_mono"], env, line, progress, cancel)

                seed_winetricks_cache(app, line, progress, cancel)

                line(f"→ Доставляю компоненты Windows внутрь Wine: {', '.join(tricks)}. "
                     "Это долго (качается из интернета) — не закрывайте окно.", "run")
                # по одному: так видно, какой именно компонент не встал
                c = 0
                failed = []
                server = env.get("WINESERVER")
                for trick in tricks:
                    line(f"   … {trick}", "run")
                    c = _stream_env([wt, "-q", trick], env, line, progress, cancel)
                    if c == -99:
                        return "cancelled"
                    if c != 0:
                        # Частая причина — зависшие процессы предыдущего
                        # компонента. Гасим окружение и пробуем ещё раз,
                        # прежде чем считать компонент непоставленным.
                        line(f"   ○ {trick}: не вышло с первого раза, "
                             "перезапускаю окружение и пробую ещё…", "warn")
                        if server and os.path.exists(server):
                            _stream_env([server, "-k"], env,
                                        lambda t, k="info": None,
                                        progress, cancel)
                        time.sleep(3)
                        c = _stream_env([wt, "-q", trick], env, line,
                                        progress, cancel)
                        if c == -99:
                            return "cancelled"
                    if c != 0:
                        failed.append(trick)
                        line(f"   ✗ {trick} не установился (код {c}). Остальные "
                             "компоненты всё равно попробую поставить.", "err")

                # Часть компонентов желательна, но не критична (например
                # d3dx9 влияет только на качество картинки). Их провал
                # установку не останавливает.
                optional = set(app.get("wine_tricks_optional") or [])
                if optional and failed:
                    skipped = [t for t in failed if t in optional]
                    if skipped:
                        line(f"○ Не установились необязательные компоненты: "
                             f"{', '.join(skipped)}. Программа будет работать, "
                             "но возможны проблемы с графикой.", "warn")
                    failed = [t for t in failed if t not in optional]

                # Без обязательных компонентов программа не заработает —
                # не делаем вид, что установка удалась.
                if failed and app.get("wine_tricks_required", True):
                    line(f"✗ {app['name']}: не установлены обязательные "
                         f"компоненты: {', '.join(failed)}. Установка "
                         "прекращена — без них программа всё равно не "
                         "запустится.", "err")
                    line("   Что попробовать:", "warn")
                    line("     • «🍷 Настройки Wine» → выбрать программу → "
                         "«🗑 Сбросить», затем установить заново", "info")
                    if any(t.startswith("dotnet") for t in failed):
                        line("     • убедиться, что окружение 32-битное: .NET в "
                             "64-битное не ставится", "info")
                    else:
                        line("     • ⚙ → «🧪 Подобрать рабочую версию Wine»: "
                             "часть компонентов ставится не на всех сборках", "info")
                    line("     • поставить компоненты вручную и повторить: "
                         f"WINEPREFIX={prefix} WINE={wine} "
                         f"winetricks -q {' '.join(failed)}", "info")
                    return "error"
                if c == -99:
                    return "cancelled"
                if c != 0 and failed:
                    line(f"   Повторить вручную: WINEPREFIX={prefix} "
                         f"WINE={wine} winetricks -q {' '.join(failed)}", "info")
            else:
                line("⚠ winetricks не установлен, а этой программе нужны компоненты "
                     f"{', '.join(tricks)}. Без них она, скорее всего, не запустится. "
                     "Поставьте пакет winetricks и переустановите программу.", "warn")

        # Отдельные .msi ставим напрямую, без winetricks
        for item in (app.get("wine_msi") or []):
            res = install_wine_msi(app, item, env, wine, line, progress, cancel)
            if res is None:
                return "cancelled"
            if not res and item.get("required", True):
                line(f"✗ {app['name']}: без этого компонента программа не "
                     "заработает, установка прекращена.", "err")
                return "error"

        src = _ascii_copy(src, line)
        line(f"→ Запускаю Windows-установщик {os.path.basename(src)} внутри Wine. "
             "Пройдите шаги мастера в открывшемся окне…", "run")
        code = _stream_env([wine, src] + list(app.get("silent_args") or []),
                           env, line, progress, cancel, cwd=os.path.dirname(src))
        if code == -99:
            return "cancelled"

        exe = _find_exe_in_prefix(app, prefix, line, exclude=src)
        if not exe:
            line(f"✗ {app['name']}: установщик отработал, но программы внутри "
                 "окружения нет — скорее всего, мастер установки был закрыт "
                 "или прерван.", "err")
            line("   Нажмите «Установить» ещё раз и пройдите мастер до конца "
                 "(кнопка Finish). Если программа всё же установлена, посмотрите "
                 f"её путь в {os.path.join(prefix, 'drive_c')} и впишите его "
                 "в поле \"wine_run\" в courses.json.", "warn")
            return "error"

        line(f"→ Найден файл запуска: {os.path.relpath(exe, prefix)}", "info")

        # установщик мог быть 32-битным, а поставить 64-битную программу
        exe_arch = pe_arch(exe)
        # Ломается только один случай: 64-битная программа в 32-битном
        # окружении. Обратное сочетание рабочее — win64 запускает и win32.
        if exe_arch == "win64" and env["WINEARCH"] == "win32":
            line("⚠ Программа 64-битная, а окружение 32-битное — Wine выдаст "
                 "«Bad EXE format».", "warn")
            line("→ Пересоздаю окружение с правильной разрядностью…", "run")
            shutil.rmtree(prefix, ignore_errors=True)
            prefix = _user_makedirs(wine_prefix(app["id"]))
            wine = wine_exe_for_arch(wine, exe_arch)
            env = self._env(app, exe_arch, wine)
            if _stream_env([wine, "wineboot", "-u"], env, line, progress, cancel) != 0:
                line("✗ Не удалось пересоздать окружение.", "err")
                return "error"
            if winver:
                _stream_env([wine, "winecfg", "-v", winver], env, line, progress, cancel)
            wt_again = find_winetricks()
            if tricks and wt_again:
                for trick in tricks:
                    _stream_env([wt_again, "-q", trick], env, line, progress, cancel)
            line(f"→ Повторяю установку в окружении {exe_arch}…", "run")
            if _stream_env([wine, src] + list(app.get("silent_args") or []),
                           env, line, progress, cancel, cwd=os.path.dirname(src)) == -99:
                return "cancelled"
            exe = _find_exe_in_prefix(app, prefix, line)
            if not exe:
                line("✗ После пересоздания программа не найдена — пройдите мастер "
                     "установки до конца.", "err")
                return "error"
        # Дополнительные файлы поверх установки — например языковой пакет:
        # архив .phi/.zip с готовым путём внутри (data/language/...),
        # который просто распаковывается в папку программы.
        for item in (app.get("wine_extra_zips") or []):
            name = item.get("file")
            if not name:
                continue
            zsrc = os.path.join(INSTALLERS_DIR, app["id"], name)
            if not os.path.exists(zsrc):
                line(f"○ {name}: файл не найден в installers/{app['id']}/ — пропускаю",
                     "info")
                continue
            zdest = os.path.join(os.path.dirname(exe), item.get("dest") or "")
            try:
                with zipfile.ZipFile(zsrc) as z:
                    z.extractall(zdest)
                line(f"✓ Распакован дополнительный файл: {name}", "ok")
            except (OSError, zipfile.BadZipFile) as e:
                line(f"⚠ Не удалось распаковать {name}: {e}", "warn")

        exec_cmd = (f"env WINEPREFIX={shell_quote(prefix)} "
                    f"WINEARCH={env['WINEARCH']} WINEDEBUG=-all "
                    f"{shell_quote(wine)} {shell_quote(exe)}")
        create_desktop_entry(app["id"], app["name"], exec_cmd,
                             comment=app.get("note", ""), workdir=os.path.dirname(exe))
        _chown_to_user(prefix)
        write_marker(app, {"exec": [wine, exe], "workdir": os.path.dirname(exe),
                           "env": env, "prefix": prefix,
                           "wine_arch": env["WINEARCH"]})
        line(f"✓ {app['name']}: установлено через Wine, ярлык добавлен в меню приложений", "ok")

        # Автопроверка и автоподбор сборки: техник не должен заниматься
        # этим руками. Если программа не запускается на текущем Wine,
        # перебираем другие и при необходимости качаем версии постарше.
        if app.get("wine_verify_launch"):
            # сперва пробуем режимы графики на текущей сборке
            if app.get("wine_env_profiles"):
                picked = auto_pick_graphics(app, exe, wine, line, cancel)
                if picked:
                    app = dict(app)
                    app["wine_env_extra"] = picked
                    env = self._env(app, env["WINEARCH"], wine)
                    write_marker(app, {"exec": [wine, exe],
                                       "workdir": os.path.dirname(exe),
                                       "env": env, "prefix": prefix,
                                       "wine_arch": env["WINEARCH"]})
            good = auto_pick_wine(app, exe, wine, line, progress, cancel)
            if good and os.path.realpath(good) != os.path.realpath(wine):
                env = self._env(app, env["WINEARCH"], good)
                exec_cmd = (f"env WINEPREFIX={shell_quote(prefix)} "
                            f"WINEARCH={env['WINEARCH']} WINEDEBUG=-all "
                            f"{shell_quote(good)} {shell_quote(exe)}")
                create_desktop_entry(app["id"], app["name"], exec_cmd,
                                     comment=app.get("note", ""),
                                     workdir=os.path.dirname(exe))
                write_marker(app, {"exec": [good, exe],
                                   "workdir": os.path.dirname(exe),
                                   "env": env, "prefix": prefix,
                                   "wine_arch": env["WINEARCH"]})
                line(f"✓ За программой закреплена сборка "
                     f"{wine_version(good) or good}", "ok")
            elif good:
                save_working_config(app["id"], read_marker(app["id"]))
            else:
                line("⚠ Программа установлена, но ни на одной сборке Wine не "
                     "запустилась. Подробности выше; можно попробовать "
                     "⚙ → «🧪 Подобрать рабочую версию Wine» с другой версией.",
                     "warn")

        line("   Учтите: Wine — это совместимость, а не гарантия. Проверьте программу "
             "на одном ПК до раскатки на класс.", "warn")
        return "success"

    @staticmethod
    def _find_installed_exe(app, prefix):
        return _find_exe_in_prefix(app, prefix)

    def uninstall(self, app, line, progress, cancel):
        prefix = wine_prefix(app["id"])
        removed = False
        if os.path.isdir(prefix):
            line(f"→ Удаляю окружение Wine целиком: {prefix}", "run")
            shutil.rmtree(prefix, ignore_errors=True)
            removed = True
        if remove_desktop_entry(app["id"]):
            removed = True
        if remove_marker(app["id"]):
            removed = True
        line(f"✓ {app['name']}: удалено" if removed else f"○ {app['name']}: нечего удалять",
             "ok" if removed else "info")
        return "removed"

    def launch_cmd(self, app):
        marker = read_marker(app["id"])
        cmd = marker.get("exec")
        if not cmd:
            return None, None, None, ("не установлено (или установщик не нашёл .exe). "
                                      "Нажмите «Установить».")
        if not os.path.exists(cmd[1]):
            return None, None, None, (f"файл {cmd[1]} исчез — переустановите программу.")

        # Настройки из courses.json применяются к уже установленным
        # программам без переустановки: если мы нашли рабочий режим графики
        # и прописали его в конфиг, он подхватится при следующем запуске.
        arch = marker.get("wine_arch") or app.get("wine_arch") or "win64"
        wine = cmd[0] if os.path.exists(cmd[0]) else find_wine(app["id"])
        wine = wine_exe_for_arch(wine, arch)
        env = wine_env(wine_prefix(app["id"]), arch, wine,
                       app.get("wine_env_extra"))
        # то, что было записано при установке, но не задано в конфиге,
        # сохраняем (например подобранный автоматически режим)
        for key, val in (marker.get("env") or {}).items():
            env.setdefault(key, val)
        return [wine, cmd[1]], marker.get("workdir"), env, None


def _stream_env(cmd, env_extra, line, progress, cancel_check, cwd=None,
                collect=None, timeout=None):
    """То же, что _stream, но с дополнительными переменными окружения
    (нужно для Wine: WINEPREFIX/WINEARCH).

    Если установщик запущен под root, команда выполняется от имени
    настоящего пользователя: Wine не работает с чужим префиксом."""
    line("$ " + cmd_for_log(cmd, env_extra), "cmd")
    env = _launch_env(env_extra)
    # Wine ругается «could not open working directory», если текущая папка
    # содержит кириллицу. Работаем из папки окружения — там только латиница.
    if cwd is None:
        cwd = env_extra.get("WINEPREFIX") if isinstance(env_extra, dict) else None
        if cwd and not os.path.isdir(cwd):
            cwd = None
    user, _home = real_user()
    if user:
        cmd = _as_user(cmd, env_extra)
        line(f"   (выполняется от имени пользователя {user}, не от root)", "info")
    try:
        proc = subprocess.Popen(cmd, cwd=cwd, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, text=True,
                                encoding="utf-8", errors="replace", bufsize=1)
    except OSError as e:
        line(f"✗ Не удалось запустить: {e}", "err")
        return 1
    q = queue.Queue()

    def reader():
        try:
            for raw in proc.stdout:
                q.put(raw)
        except (OSError, ValueError):
            pass
        q.put(None)

    threading.Thread(target=reader, daemon=True).start()
    last_text, repeats, shown, hidden = None, 0, 0, 0
    started = time.time()
    while True:
        if cancel_check():
            try:
                proc.terminate()
            except OSError:
                pass
            line("⚠ Отменено пользователем", "warn")
            return -99
        # Ограничение по времени: Wine умеет зависать намертво, ожидая
        # процессы прежнего окружения. Лучше прервать и сказать об этом,
        # чем оставить программу молча висеть.
        if timeout and time.time() - started > timeout:
            line(f"⚠ Команда выполняется дольше {int(timeout)} с — "
                 "прерываю, похоже Wine завис.", "warn")
            try:
                proc.terminate()
                proc.wait(timeout=10)
            except (OSError, subprocess.SubprocessError):
                try:
                    proc.kill()
                except OSError:
                    pass
            return -98
        try:
            item = q.get(timeout=0.15)
        except queue.Empty:
            if proc.poll() is not None:
                break
            continue
        if item is None:
            break
        text = _clean(item.rstrip("\n"))
        if not text.strip():
            continue
        if collect is not None:
            collect.append(text)
        # Wine повторяет одно и то же сообщение десятки раз (например про
        # FreeType) — печатаем один раз и считаем повторы
        if text == last_text:
            repeats += 1
            continue
        if repeats:
            line(f"   (предыдущая строка повторилась ещё {repeats} раз)", "info")
            repeats = 0
        last_text = text
        if shown < MAX_LOG_LINES:
            line(text, "info")
            shown += 1
            if shown == MAX_LOG_LINES:
                line(f"   … дальше вывод этой команды не показываю: строк "
                     "слишком много. Команда продолжает работать.", "warn")
        else:
            hidden += 1
            if hidden % 2000 == 0:
                progress(f"Программа выдала уже {shown + hidden} строк…")
    if repeats:
        line(f"   (предыдущая строка повторилась ещё {repeats} раз)", "info")
    if hidden:
        line(f"   (скрыто ещё {hidden} строк вывода)", "info")
    proc.wait()
    return proc.returncode


def get_installer(app):
    t = (app.get("installer") or "").lower()
    if t == "wine":
        return WineInstaller()
    if t == "repo":
        return RepoInstaller()
    if t == "flatpak":
        return FlatpakInstaller()
    if t == "jar":
        return JarInstaller()
    if t == "web":
        return WebInstaller()
    if t == "mod":
        return ModInstaller()
    if t in ("unsupported", "none"):
        return UnsupportedInstaller()
    # rpm / deb / appimage / archive / script — всё через локальный файл
    return LocalFileInstaller()


def is_app_installed(app, cache=None):
    try:
        return get_installer(app).is_installed(app, cache)
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Поток операции (установка / удаление / запуск)
# ---------------------------------------------------------------------------

class OpWorker(QThread):
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_step = pyqtSignal(int, int, str)
    sig_done = pyqtSignal(dict)

    def __init__(self, apps, action="install", force=False):
        super().__init__()
        self.apps = apps
        self.action = action
        # force=True — ставить заново даже то, что уже установлено
        self.force = force
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def _cancelled(self):
        return self._cancel

    def _line(self, text, kind="info"):
        self.sig_line.emit(text, kind)

    def _prog(self, text):
        self.sig_progress.emit(text)

    def run(self):
        report = {}

        total = len(self.apps)
        for i, app in enumerate(self.apps, start=1):
            if self._cancelled():
                report["cancelled"] = report.get("cancelled", 0) + 1
                break
            self.sig_step.emit(i, total, app["name"])
            inst = get_installer(app)

            # Уже установленное не трогаем: не качаем файлы заново, не гоняем
            # пакетный менеджер и не пересоздаём окружения Wine.
            if self.action == "install" and not self.force:
                try:
                    if inst.is_installed(app):
                        self._line(f"○ [{i}/{total}] {app['name']}: уже установлено — "
                                   "пропускаю", "ok")
                        report["skipped"] = report.get("skipped", 0) + 1
                        continue
                except Exception:
                    pass

            self._line("", "info")
            verb = "Установка" if self.action == "install" else "Удаление"
            if self.force and self.action == "install":
                verb = "Переустановка"
            self._line(f"───── [{i}/{total}] {verb}: {app['name']} ─────", "run")
            try:
                if self.action == "install":
                    status = inst.install(app, self._line, self._prog, self._cancelled)
                else:
                    status = inst.uninstall(app, self._line, self._prog, self._cancelled)
            except Exception as e:  # чтобы одна программа не роняла всю пачку
                self._line(f"✗ Внутренняя ошибка: {e}", "err")
                status = "error"
            report[status] = report.get(status, 0) + 1

        self.sig_done.emit(report)



class LaunchWorker(QThread):
    """Запускает уже установленную программу и показывает ВЕСЬ её вывод
    (в том числе ошибки) прямо в журнале окна — не нужно открывать терминал.

    Программа живёт в отдельном потоке, поэтому окно установщика не
    подвисает и можно запустить несколько программ одновременно."""

    sig_line = pyqtSignal(str, str)
    sig_started = pyqtSignal(str)
    sig_done = pyqtSignal(str, int)

    def __init__(self, app, cmd=None, cwd=None, env=None):
        super().__init__()
        self.app = app
        # если команда задана явно — это дополнительный инструмент программы
        # (например, конфигуратор Kodu), а не она сама
        self.forced = (cmd, cwd, env) if cmd else None
        self.proc = None
        self._stop = False

    def stop(self):
        self._stop = True
        if self.proc and self.proc.poll() is None:
            try:
                self.proc.terminate()
            except OSError:
                pass

    def _line(self, text, kind="info"):
        self.sig_line.emit(text, kind)

    def run(self):
        app = self.app
        name = app["name"]
        try:
            if self.forced:
                cmd, cwd, env_extra, err = self.forced[0], self.forced[1], \
                    self.forced[2], None
            else:
                cmd, cwd, env_extra, err = get_installer(app).launch_cmd(app)
        except Exception as e:
            self._line(f"✗ {name}: внутренняя ошибка при подготовке запуска: {e}", "err")
            self.sig_done.emit(app["id"], -1)
            return
        if err:
            self._line(f"✗ {name}: {err}", "err")
            self.sig_done.emit(app["id"], -1)
            return

        if is_root():
            user, _home = real_user()
            if not user:
                self._line(f"✗ {name}: программу нельзя запускать от имени root.", "err")
                self._line("   Wine и flatpak отказываются работать под "
                           "суперпользователем — это их защита, а не сбой.", "warn")
                self._line("   Закройте установщик и запустите его обычным "
                           "пользователем: ./start.sh (без sudo).", "warn")
                self.sig_done.emit(app["id"], -1)
                return
            if not (shutil.which("runuser") or shutil.which("sudo")):
                self._line(f"✗ {name}: установщик работает под root, а перейти "
                           f"к пользователю {user} нечем — нет ни runuser, ни sudo.", "err")
                self._line("   Запустите установщик обычным пользователем: ./start.sh", "warn")
                self.sig_done.emit(app["id"], -1)
                return

        cmd = _as_user(cmd)
        self._line(f"→ Запускаю {name}…", "run")
        self._line("$ " + cmd_for_log(cmd, env_extra), "cmd")
        try:
            self.proc = subprocess.Popen(
                cmd, cwd=cwd, env=_launch_env(env_extra),
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                stdin=subprocess.DEVNULL, text=True,
                encoding="utf-8", errors="replace", bufsize=1,
                start_new_session=True)
        except FileNotFoundError:
            self._line(f"✗ {name}: команда {cmd[0]} не найдена в системе.", "err")
            self.sig_done.emit(app["id"], -1)
            return
        except OSError as e:
            self._line(f"✗ {name}: не удалось запустить — {e}", "err")
            self.sig_done.emit(app["id"], -1)
            return

        self.sig_started.emit(app["id"])
        started = time.time()
        # Если программа проживёт достаточно долго, запомним настройки как
        # рабочие: тогда после неудачного подбора к ним можно вернуться.
        remember_after = 15
        collected = []
        noise = 0
        for raw in self.proc.stdout:
            text = _clean(raw.rstrip("\n"))
            if not text.strip():
                continue
            collected.append(text)
            if is_noise_line(text):
                noise += 1
                continue
            low = text.lower()
            kind = "err" if any(w in low for w in
                                ("error", "ошибк", "cannot", "failed", "not found",
                                 "no such file", "permission denied")) else "info"
            self._line(f"[{name}] {text}", kind)
        self.proc.wait()
        code = self.proc.returncode
        elapsed = time.time() - started
        if noise:
            self._line(f"   (скрыто {noise} служебных строк: проверка уязвимостей "
                       "Astra, метки PDP и подобное — на работу не влияют)", "info")

        crashed = any(any(mark in t for mark in
                          ("Unhandled exception", "page fault", "Backtrace:"))
                      for t in collected)
        if elapsed >= remember_after and not crashed and not self.forced:
            marker = read_marker(app["id"])
            if marker.get("exec"):
                save_working_config(app["id"], marker)
                self._line("   Настройки запомнены как рабочие — к ним можно "
                           "вернуться кнопкой ⚙ → «↩ Вернуть настройки, при "
                           "которых работало».", "info")

        if code == 0:
            self._line(f"✓ {name}: программа завершилась нормально "
                       f"(проработала {int(elapsed)} с).", "ok")
        elif self._stop:
            self._line(f"⚠ {name}: остановлено из окна установщика.", "warn")
        else:
            self._line(f"✗ {name}: завершилась с ошибкой, код {code}"
                       f" (через {int(elapsed)} с после запуска).", "err")
            if elapsed < 3:
                self._line("   Программа упала сразу — скорее всего, не хватает "
                           "системной библиотеки или компонента. Смотрите строки выше.",
                           "warn")
            for hint in hints_for("\n".join(collected[-60:])):
                self._line("   💡 " + hint, "warn")
            if not collected:
                self._line("   Программа не выдала ни одной строки. Попробуйте запустить "
                           "её из терминала той же командой (она показана выше) — "
                           "иногда ошибка печатается только там.", "info")
        self.sig_done.emit(app["id"], code)


# ---------------------------------------------------------------------------
# Раздача по локальной сети
# ---------------------------------------------------------------------------

def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "127.0.0.1"


class _ShareServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    """Сервер раздачи.

    ThreadingMixIn обязателен: обычный TCPServer обслуживает по одному
    клиенту за раз, и пока первый компьютер качает архив на сотни мегабайт,
    остальные стоят в очереди — со стороны это выглядит как зависший сервер.
    Теперь класс можно раздавать сразу на все машины.

    daemon_threads — чтобы зависшее соединение (выключили ПК посреди
    загрузки) не мешало закрыть программу."""

    allow_reuse_address = True
    daemon_threads = True
    request_queue_size = 64

    def handle_error(self, request, client_address):
        # обрыв связи с учеником — обычное дело, не нужно ни трассировок,
        # ни падения сервера
        pass


class _QuietHandler(http.server.SimpleHTTPRequestHandler):
    """Отдаёт ТОЛЬКО папку раздачи (в ней лежит один архив) и сообщает
    в журнал, какой компьютер класса его забрал.

    Поддерживает докачку (заголовок Range): если связь оборвалась на
    середине, приёмник продолжит с того же места, а не начнёт заново."""

    on_download = None      # callback(ip, path, event) — подставляет главное окно
    protocol_version = "HTTP/1.1"
    timeout = 300

    def log_message(self, *args):
        pass

    def _notify(self, event):
        if callable(_QuietHandler.on_download):
            try:
                _QuietHandler.on_download(self.client_address[0], self.path, event)
            except Exception:
                pass

    def do_GET(self):
        if not self.path.endswith(".zip"):
            return super().do_GET()

        path = self.translate_path(self.path)
        if not os.path.isfile(path):
            self.send_error(404, "File not found")
            return

        size = os.path.getsize(path)
        start, end = 0, size - 1
        rng = self.headers.get("Range")
        partial = False
        if rng and rng.startswith("bytes="):
            try:
                a, _, b = rng[6:].partition("-")
                start = int(a) if a else 0
                end = int(b) if b else size - 1
                partial = 0 <= start <= end < size
            except ValueError:
                partial = False

        self._notify("start")
        try:
            with open(path, "rb") as f:
                if partial:
                    f.seek(start)
                    self.send_response(206)
                    self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
                else:
                    start, end = 0, size - 1
                    self.send_response(200)
                length = end - start + 1
                self.send_header("Content-Type", "application/zip")
                self.send_header("Content-Length", str(length))
                self.send_header("Accept-Ranges", "bytes")
                self.end_headers()

                left = length
                while left > 0:
                    chunk = f.read(min(262144, left))
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    left -= len(chunk)
            self._notify("done" if left <= 0 else "broken")
        except (BrokenPipeError, ConnectionResetError, OSError):
            # ученик закрыл окно или пропала сеть — остальным это не мешает
            self._notify("broken")


class ShareZipWorker(QThread):
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(str)

    def __init__(self, base_dir):
        super().__init__()
        self.base = base_dir

    def run(self):
        name = os.path.basename(self.base)
        # Архив кладём в ОТДЕЛЬНУЮ папку и раздаём по сети только её:
        # если раздавать папку-родитель, классу стали бы видны все соседние
        # файлы (например, всё содержимое «Загрузок» или домашней папки).
        zip_path = os.path.join(SHARE_DIR, "koderlab-share.zip")
        try:
            os.makedirs(SHARE_DIR, exist_ok=True)
            files = []
            for root, _dirs, fs in os.walk(self.base):
                for f in fs:
                    files.append(os.path.join(root, f))
            total = len(files) or 1
            self.sig_line.emit(f"→ Упаковываю {total} файлов (без сжатия, это быстро)…", "run")
            with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_STORED, allowZip64=True) as z:
                for i, fp in enumerate(files, 1):
                    arc = os.path.join(name, os.path.relpath(fp, self.base))
                    z.write(fp, arc)
                    if i % 40 == 0 or i == total:
                        self.sig_progress.emit(f"Упаковано {i}/{total}")
            mb = os.path.getsize(zip_path) // (1024 * 1024)
            self.sig_line.emit(f"✓ Архив готов: {zip_path} ({mb} МБ)", "ok")
            self.sig_done.emit(zip_path)
        except Exception as e:
            self.sig_line.emit(f"✗ Ошибка упаковки: {e}", "err")
            self.sig_done.emit("")


class ReceiveWorker(QThread):
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(str)

    def __init__(self, url, dest):
        super().__init__()
        self.url = url
        self.dest = dest

    def run(self):
        tmp = os.path.join(self.dest, "koderlab-download.zip")
        try:
            os.makedirs(self.dest, exist_ok=True)
            self.sig_line.emit(f"→ Скачиваю {self.url}…", "run")
            self._download(tmp)
            self.sig_line.emit("→ Распаковываю…", "run")
            with zipfile.ZipFile(tmp) as z:
                z.extractall(self.dest)
            os.remove(tmp)
            # права на запуск теряются в zip — возвращаем их скриптам
            for sh in globmod.glob(os.path.join(self.dest, "**", "*.sh"), recursive=True):
                try:
                    os.chmod(sh, 0o755)
                except OSError:
                    pass
            self.sig_line.emit(f"✓ Получено в: {self.dest}", "ok")
            self.sig_done.emit(self.dest)
        except Exception as e:
            self.sig_line.emit(f"✗ Ошибка получения: {e}", "err")
            self.sig_line.emit("   Недокачанный файл сохранён — нажмите «Получить по "
                               "сети» ещё раз, загрузка продолжится с того же места.",
                               "warn")
            self.sig_done.emit("")

    def _download(self, tmp):
        """Скачивание с докачкой: если файл уже частично есть, просим сервер
        отдать остаток. В классе на 15 машин обрывы — обычное дело."""
        have = os.path.getsize(tmp) if os.path.exists(tmp) else 0
        req = urllib.request.Request(self.url)
        if have:
            req.add_header("Range", f"bytes={have}-")
            self.sig_line.emit(f"→ Файл уже скачан на {have // 1048576} МБ — "
                               "продолжаю с этого места", "info")
        with urllib.request.urlopen(req, timeout=60) as r:
            resuming = r.status == 206
            total = int(r.headers.get("Content-Length") or 0) + (have if resuming else 0)
            mode = "ab" if resuming else "wb"
            if not resuming:
                have = 0
            done = have
            with open(tmp, mode) as f:
                while True:
                    chunk = r.read(262144)
                    if not chunk:
                        break
                    f.write(chunk)
                    done += len(chunk)
                    if total:
                        self.sig_progress.emit(
                            f"Загрузка: {min(100, int(done * 100 / total))}% "
                            f"({done // 1048576} из {total // 1048576} МБ)")
                    else:
                        self.sig_progress.emit(f"Загрузка: {done // 1048576} МБ")


# ---------------------------------------------------------------------------
# Раскладывание скачанных файлов по installers/<id>/
# ---------------------------------------------------------------------------

SORT_EXTS = (".rpm", ".deb", ".appimage", ".zip", ".tar.gz", ".tgz", ".tar.xz",
             ".tar.bz2", ".jar", ".sh", ".run", ".html", ".htm", ".flatpak", ".exe")


def _has_sort_ext(name):
    low = name.lower()
    return any(low.endswith(e) for e in SORT_EXTS)


def sort_downloads(src_dir, apps, line, progress, cancel):
    """Раскладывает скачанные файлы (любые имена) по installers/<id>/
    под именем, которое ожидает courses.json."""
    try:
        files = sorted(f for f in os.listdir(src_dir)
                       if os.path.isfile(os.path.join(src_dir, f)) and _has_sort_ext(f))
    except OSError as e:
        line(f"✗ Не удалось прочитать папку {src_dir}: {e}", "err")
        return {"matched": 0, "ambiguous": 0, "unmatched": 0, "errors": 1}

    if not files:
        line(f"○ В папке {src_dir} не найдено файлов "
             ".rpm/.deb/.AppImage/.tar.gz/.zip/.jar/.sh/.html", "info")
        return {"matched": 0, "ambiguous": 0, "unmatched": 0, "errors": 0}

    line(f"→ Найдено файлов для распределения: {len(files)}", "run")
    matched = ambiguous = unmatched = errors = 0

    for i, fname in enumerate(files, 1):
        if cancel():
            line("⚠ Отменено пользователем", "warn")
            break
        norm_name = _normalize(_strip_ext(fname))
        candidates = []
        for app_id, app in apps.items():
            if not app.get("file"):
                continue
            for kw in _app_keywords(app_id, app):
                nk = _normalize(kw)
                if nk and nk in norm_name:
                    candidates.append(app_id)
                    break
        candidates = sorted(set(candidates))

        if len(candidates) == 1:
            app_id = candidates[0]
            app = apps[app_id]
            dest_dir = os.path.join(INSTALLERS_DIR, app_id)
            # сохраняем реальное расширение файла, а не то, что в конфиге
            expected = os.path.basename(app["file"])
            src_ext = next((e for e in SORT_EXTS if fname.lower().endswith(e)), "")
            exp_ext = next((e for e in SORT_EXTS if expected.lower().endswith(e)), "")
            dest_name = expected if src_ext == exp_ext else _strip_ext(expected) + src_ext
            dest = os.path.join(dest_dir, dest_name)
            try:
                os.makedirs(dest_dir, exist_ok=True)
                src_path = os.path.join(src_dir, fname)
                if os.path.exists(dest) and \
                        os.path.getsize(dest) == os.path.getsize(src_path):
                    line(f"○ {fname}: такой файл уже лежит в installers/{app_id}/ — "
                         "пропускаю", "info")
                    matched += 1
                    progress(f"Разобрано {i}/{len(files)}")
                    continue
                shutil.copy2(src_path, dest)
                line(f"✓ {fname} → installers/{app_id}/{dest_name}  ({app['name']})", "ok")
                matched += 1
            except OSError as e:
                line(f"✗ {fname}: не удалось скопировать — {e}", "err")
                errors += 1
        elif len(candidates) > 1:
            line(f"⚠ {fname}: подходит сразу несколько программ "
                 f"({', '.join(candidates)}) — разложите вручную", "warn")
            ambiguous += 1
        else:
            line(f"○ {fname}: не удалось определить программу — разложите вручную", "info")
            unmatched += 1
        progress(f"Разобрано {i}/{len(files)}")

    return {"matched": matched, "ambiguous": ambiguous, "unmatched": unmatched, "errors": errors}


class SortWorker(QThread):
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(dict)

    def __init__(self, src_dir, apps):
        super().__init__()
        self.src_dir = src_dir
        self.apps = apps
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        report = sort_downloads(
            self.src_dir, self.apps,
            lambda t, k="info": self.sig_line.emit(t, k),
            lambda t: self.sig_progress.emit(t),
            lambda: self._cancel,
        )
        self.sig_done.emit(report)


# ---------------------------------------------------------------------------
# Поиск программы на GitHub по названию
# ---------------------------------------------------------------------------

class _GhWorker(QThread):
    """Сетевые запросы к GitHub в отдельном потоке, чтобы окно не подвисало."""
    sig_repos = pyqtSignal(object)
    sig_releases = pyqtSignal(object)

    def __init__(self, mode, arg):
        super().__init__()
        self.mode = mode
        self.arg = arg

    def run(self):
        if self.mode == "search":
            self.sig_repos.emit(github_search_repos(self.arg))
        else:
            self.sig_releases.emit(github_releases(self.arg))


class _GhDownloadWorker(QThread):
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(str)

    def __init__(self, url, dest):
        super().__init__()
        self.url = url
        self.dest = dest
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        r = download_file(self.url, self.dest,
                          lambda t, k="info": self.sig_line.emit(t, k),
                          lambda t: self.sig_progress.emit(t),
                          lambda: self._cancel)
        self.sig_done.emit(r or "")


# ---------------------------------------------------------------------------
# Встроенный редактор файлов настроек
# ---------------------------------------------------------------------------

class ConfigEditorDialog(QDialog):
    """Правка файла настроек прямо в окне установщика.

    Через xdg-open такие файлы открываются не всегда: в системе может не быть
    ассоциации для .toml или .conf, и тогда просто ничего не происходит —
    техник видит, что «кнопка не работает». Поэтому редактируем сами."""

    def __init__(self, title, path, template="", hint="", parent=None):
        super().__init__(parent)
        self.path = os.path.expanduser(path)
        self.template = template
        self.win = parent
        self.setWindowTitle(title)
        self.resize(760, 560)
        self._build(hint)
        self._load()

    def _build(self, hint):
        v = QVBoxLayout(self)
        head = QLabel(f"<b>{os.path.basename(self.path)}</b><br>"
                      f"<span style='color:#888'>{self.path}</span>")
        head.setWordWrap(True)
        v.addWidget(head)
        if hint:
            lbl = QLabel(hint)
            lbl.setWordWrap(True)
            lbl.setStyleSheet("color:#888; font-size:12px;")
            v.addWidget(lbl)

        self.edit = QTextEdit()
        self.edit.setLineWrapMode(QTextEdit.NoWrap)
        self.edit.setStyleSheet(
            "font-family: 'DejaVu Sans Mono', monospace; font-size: 13px;")
        v.addWidget(self.edit, stretch=1)

        self.status = QLabel("")
        self.status.setStyleSheet("color:#888; font-size:12px;")
        self.status.setWordWrap(True)
        v.addWidget(self.status)

        row = QHBoxLayout()
        save = QPushButton("💾 Сохранить")
        save.clicked.connect(self._save)
        row.addWidget(save)
        reset = QPushButton("↺ Вернуть образец")
        reset.setToolTip("Заменить содержимое стандартным набором настроек "
                         "с пояснениями. Текущий файл сохранится рядом как .bak")
        reset.clicked.connect(self._reset)
        row.addWidget(reset)
        folder = QPushButton("📁 Открыть папку")
        folder.clicked.connect(self._open_folder)
        row.addWidget(folder)
        row.addStretch()
        box = QDialogButtonBox(QDialogButtonBox.Close)
        box.rejected.connect(self.reject)
        row.addWidget(box)
        v.addLayout(row)

    def _load(self):
        if os.path.exists(self.path):
            try:
                with open(self.path, encoding="utf-8", errors="replace") as f:
                    self.edit.setPlainText(f.read())
                self.status.setText("Файл загружен.")
                return
            except OSError as e:
                self.status.setText(f"Не удалось прочитать файл: {e}")
                return
        self.edit.setPlainText(self.template)
        self.status.setText("Файла ещё нет — показан образец. "
                            "Нажмите «Сохранить», чтобы создать его.")

    def _save(self):
        try:
            _user_makedirs(os.path.dirname(self.path))
            if os.path.exists(self.path):
                shutil.copy2(self.path, self.path + ".bak")
            with open(self.path, "w", encoding="utf-8") as f:
                f.write(self.edit.toPlainText())
            _chown_to_user(os.path.dirname(self.path))
            self.status.setText("✓ Сохранено. Изменения применятся при "
                                "следующем запуске программы.")
            if self.win:
                self.win.log(f"✓ Сохранён файл настроек: {self.path}", "ok")
        except OSError as e:
            self.status.setText(f"✗ Не удалось сохранить: {e}")

    def _reset(self):
        r = QMessageBox.question(
            self, "Вернуть образец",
            "Заменить содержимое стандартным набором настроек?\n\n"
            "Текущий файл сохранится рядом с расширением .bak",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r == QMessageBox.Yes:
            self.edit.setPlainText(self.template)
            self.status.setText("Показан образец — нажмите «Сохранить».")

    def _open_folder(self):
        d = os.path.dirname(self.path)
        if not os.path.isdir(d):
            self.status.setText("Папки ещё нет — сначала сохраните файл.")
            return
        try:
            subprocess.Popen(_as_user(["xdg-open", d]), start_new_session=True)
        except OSError as e:
            self.status.setText(f"Не удалось открыть папку: {e}")


VINEGAR_CONFIG_TEMPLATE = """\
# Настройки Vinegar (Roblox Studio под Linux).
# После правки закройте файл и запустите Studio заново.

[studio]
# Отключите, если Studio не запускается из-за DXVK
dxvk = true
# Версия Windows, под которую притворяется Wine
# wine_root = ""

[studio.env]
# Если нет аппаратного ускорения (в журнале "DRI3 error"), помогает
# программная отрисовка — медленно, но окна появляются:
# LIBGL_ALWAYS_SOFTWARE = "1"
# Принудительно использовать OpenGL вместо Vulkan:
# WINEDLLOVERRIDES = "dxgi,d3d11=b"

[studio.fflags]
# Ограничить частоту кадров (меньше нагрузка на слабый ПК)
# DFIntTaskSchedulerTargetFps = 30
# Отключить тяжёлые эффекты
# FFlagDebugGraphicsDisableDirect3D11 = false
"""

class GitHubSearchDialog(QDialog):
    """Поиск программы на GitHub по названию и скачивание нужного файла
    сразу в installers/<id>/ — оттуда его подхватит установка, а потом всю
    папку можно раздать по локальной сети класса."""

    def __init__(self, app, parent=None):
        super().__init__(parent)
        self.app = app
        self.win = parent
        self.repos = []
        self.releases = []
        self.worker = None
        self.dl = None
        self.saved_path = None
        self.chosen_repo = None
        self.setWindowTitle(f"Поиск на GitHub — {app['name']}")
        self.resize(820, 640)
        self._build()
        self.query.setText(app.get("github") or app["name"])

    def _build(self):
        v = QVBoxLayout(self)
        v.addWidget(QLabel(
            f"<b>{self.app['name']}</b> — найденный файл сохранится в "
            f"<code>installers/{self.app['id']}/</code> и сразу станет доступен "
            "для установки и для раздачи по сети."))

        row = QHBoxLayout()
        self.query = QLineEdit()
        self.query.setPlaceholderText(
            "Название программы (blockbench) или сразу владелец/репозиторий")
        self.query.returnPressed.connect(self._search)
        row.addWidget(self.query)
        self.search_btn = QPushButton("🔎 Найти")
        self.search_btn.clicked.connect(self._search)
        row.addWidget(self.search_btn)
        v.addLayout(row)

        v.addWidget(QLabel("1) Репозиторий (сверху — самые популярные):"))
        self.repo_list = QListWidget()
        self.repo_list.itemSelectionChanged.connect(self._repo_selected)
        v.addWidget(self.repo_list, stretch=2)

        v.addWidget(QLabel("2) Файл для установки "
                           "(★ — лучше всего подходит этой системе):"))
        self.asset_list = QListWidget()
        self.asset_list.itemSelectionChanged.connect(self._update_buttons)
        v.addWidget(self.asset_list, stretch=3)

        self.status = QLabel("Введите название и нажмите «Найти».")
        self.status.setStyleSheet("color:#888; font-size:12px;")
        self.status.setWordWrap(True)
        v.addWidget(self.status)

        btns = QHBoxLayout()
        self.dl_btn = QPushButton("⬇ Скачать в папку установщика")
        self.dl_btn.setEnabled(False)
        self.dl_btn.clicked.connect(self._download)
        btns.addWidget(self.dl_btn)
        btns.addStretch()
        box = QDialogButtonBox(QDialogButtonBox.Close)
        box.rejected.connect(self.reject)
        btns.addWidget(box)
        v.addLayout(btns)

    # ---- поиск ----
    def _search(self):
        q = self.query.text().strip()
        if not q:
            return
        self.repo_list.clear()
        self.asset_list.clear()
        self._set_busy(True, f"Ищу «{q}» на GitHub…")
        if re.fullmatch(r"[\w.-]+/[\w.-]+", q):   # ввели готовое «владелец/репо»
            self._show_repos([{"full_name": q, "description": "указан вручную",
                               "stars": 0, "archived": False}])
            return
        self.worker = _GhWorker("search", q)
        self.worker.sig_repos.connect(self._show_repos)
        self.worker.start()

    def _show_repos(self, repos):
        self._set_busy(False)
        if repos is None:
            self.status.setText(GH_LAST_ERROR or "Не удалось связаться с GitHub.")
            if "лимит" in GH_LAST_ERROR:
                QMessageBox.information(self, "GitHub ограничил запросы", GH_LAST_ERROR)
            return
        self.repos = repos
        if not repos:
            self.status.setText("Ничего не найдено. Попробуйте другое написание или "
                                "введите «владелец/репозиторий» целиком.")
            return
        for r in repos:
            label = f"{r['full_name']}   ★ {r['stars']}"
            if r["archived"]:
                label += "   [архив, больше не развивается]"
            if r["description"]:
                label += f"\n      {r['description'][:110]}"
            it = QListWidgetItem(label)
            it.setData(Qt.UserRole, r["full_name"])
            self.repo_list.addItem(it)
        self.status.setText(f"Найдено репозиториев: {len(repos)}. Проверьте владельца — "
                            "у популярных программ бывает много чужих копий.")
        self.repo_list.setCurrentRow(0)

    # ---- релизы и файлы ----
    def _repo_selected(self):
        items = self.repo_list.selectedItems()
        if not items:
            return
        repo = items[0].data(Qt.UserRole)
        self.chosen_repo = repo
        self.asset_list.clear()
        self._set_busy(True, f"Смотрю релизы {repo}…")
        self.worker = _GhWorker("releases", repo)
        self.worker.sig_releases.connect(self._show_assets)
        self.worker.start()

    def _show_assets(self, releases):
        self._set_busy(False)
        if releases is None:
            self.status.setText(GH_LAST_ERROR or "Не удалось получить список релизов.")
            if "лимит" in GH_LAST_ERROR:
                QMessageBox.information(self, "GitHub ограничил запросы", GH_LAST_ERROR)
            return
        self.releases = releases
        if not releases:
            self.status.setText("У этого репозитория нет релизов с готовыми файлами — "
                                "программу пришлось бы собирать из исходников. "
                                "Выберите другой репозиторий.")
            return

        rows = []
        for rel in releases[:5]:
            for a in rel["assets"]:
                score = rank_asset(a["name"])
                if score is not None:
                    rows.append((score, rel, a))
        if not rows:
            self.status.setText("В релизах нет файлов для Linux — только Windows/macOS. "
                                "Такую программу ставят через Wine "
                                "(installer: \"wine\") либо ищут замену.")
            return

        rows.sort(key=lambda t: (-t[0], t[1]["tag"]))
        best = rows[0][0]
        for score, rel, a in rows:
            mark = "★ " if score == best else "   "
            tag = rel["tag"] + (" (предрелиз)" if rel["prerelease"] else "")
            it = QListWidgetItem(f"{mark}{a['name']}\n      {tag}   •   "
                                 f"{a['size'] / 1048576:.0f} МБ")
            it.setData(Qt.UserRole, a)
            if score < 0:
                it.setToolTip("Похоже, файл не для этой системы "
                              f"(архитектура {_machine_arch()}, пакеты .{PKG_FAMILY}).")
            self.asset_list.addItem(it)
        self.asset_list.setCurrentRow(0)
        self.status.setText(f"Подходящих файлов: {len(rows)}. "
                            "Звёздочкой отмечен лучший для этой системы.")

    def _update_buttons(self):
        self.dl_btn.setEnabled(bool(self.asset_list.selectedItems()) and not self.dl)

    def _set_busy(self, busy, text=None):
        self.search_btn.setEnabled(not busy)
        self.query.setEnabled(not busy)
        if text:
            self.status.setText(text)

    # ---- скачивание ----
    def _download(self):
        items = self.asset_list.selectedItems()
        if not items:
            return
        asset = items[0].data(Qt.UserRole)
        dest = os.path.join(INSTALLERS_DIR, self.app["id"], asset["name"])
        if os.path.exists(dest) and os.path.getsize(dest) > 0:
            r = QMessageBox.question(
                self, "Файл уже скачан",
                f"{asset['name']} уже лежит в installers/{self.app['id']}/ "
                f"({os.path.getsize(dest) // 1048576} МБ).\n\nСкачать заново?",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
            if r != QMessageBox.Yes:
                self.saved_path = dest
                self.status.setText("Используется уже скачанный файл.")
                self.accept()
                return
            try:
                os.remove(dest)
            except OSError:
                pass
        self.dl_btn.setEnabled(False)
        self.status.setText(f"Скачиваю {asset['name']}…")
        self.dl = _GhDownloadWorker(asset["url"], dest)
        if self.win:
            self.dl.sig_line.connect(self.win.log)
        self.dl.sig_progress.connect(self.status.setText)
        self.dl.sig_done.connect(self._downloaded)
        self.dl.start()

    def _downloaded(self, path):
        self.dl = None
        self.dl_btn.setEnabled(True)
        if not path:
            self.status.setText("Скачать не удалось — подробности в журнале окна.")
            return
        self.saved_path = path
        name = os.path.basename(path)
        self.status.setText(f"✓ Готово: installers/{self.app['id']}/{name}")
        r = QMessageBox.question(
            self, "Файл скачан",
            f"Файл сохранён:\ninstallers/{self.app['id']}/{name}\n\n"
            "Запомнить этот репозиторий в courses.json, чтобы на других "
            "компьютерах программа скачивалась сама?\n\n"
            "(Файл уже лежит в папке — её можно просто раздать по сети класса, "
            "тогда интернет на остальных ПК не понадобится.)",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
        if r == QMessageBox.Yes and self.win:
            self.win.remember_github(self.app["id"], self.chosen_repo, name)
        self.accept()

    def reject(self):
        if self.dl:
            self.dl.cancel()
        super().reject()


# ---------------------------------------------------------------------------
# Автоподбор рабочей сборки Wine
# ---------------------------------------------------------------------------

def list_wine_builds_online(limit_releases=12):
    """Список доступных для скачивания сборок Wine (без wow64).

    Нужен, когда в новой версии Wine появилась регрессия и программа
    перестала запускаться: берём версию постарше."""
    out = []
    seen = set()
    data = _gh_api(f"https://api.github.com/repos/{WINE_BUILDS_REPO}"
                   f"/releases?per_page={limit_releases}")
    if not data:
        return out
    for rel in data:
        for a in rel.get("assets", []):
            name = a.get("name", "")
            low = name.lower()
            if "wow64" in low or "arm" in low:
                continue
            if not low.endswith((".tar.xz", ".tar.gz")) or "amd64" not in low:
                continue
            if "tkg" in low or "proton" in low:
                continue
            if name in seen:
                continue
            seen.add(name)
            out.append({"name": name, "tag": rel.get("tag_name", ""),
                        "url": a.get("browser_download_url"),
                        "size": a.get("size", 0),
                        "staging": "staging" in low})
    return out


def _wine_asset_version(name):
    """Версия из имени файла сборки: wine-9.2-amd64.tar.xz → (9, 2)."""
    m = re.search(r"wine-(\d+)\.(\d+)", name.lower())
    return (int(m.group(1)), int(m.group(2))) if m else None


def find_wine_build_version(version, line=None, max_pages=6, want_x86=False):
    """Ищет сборку нужной версии Wine.

    Если точной версии нет (например 9.2 уже убрали), берётся ближайшая из
    той же ветки — для нас важна не цифра, а поколение Wine, в котором
    программа работала.

    want_x86=True — искать прежде всего чисто 32-битную сборку (x86):
    именно в ней 32-битная часть присутствует гарантированно."""
    try:
        want = tuple(int(x) for x in str(version).split(".")[:2])
        if len(want) == 1:
            want = (want[0], 0)
    except ValueError:
        want = None

    exact, nearby = None, []
    for page in range(1, max_pages + 1):
        data = _gh_api(f"https://api.github.com/repos/{WINE_BUILDS_REPO}"
                       f"/releases?per_page=100&page={page}")
        if not data:
            break
        for rel in data:
            for a in rel.get("assets", []):
                name = a.get("name", "")
                low = name.lower()
                if "wow64" in low or "arm" in low or "tkg" in low:
                    continue
                is_x86 = ("x86" in low and "x86_64" not in low)
                if want_x86:
                    # 32-битная сборка в приоритете, amd64 — как запасной
                    if not (is_x86 or "amd64" in low):
                        continue
                elif "amd64" not in low:
                    continue
                if not low.endswith((".tar.xz", ".tar.gz")):
                    continue
                ver = _wine_asset_version(name)
                if not ver or not want:
                    continue
                item = {"name": name, "tag": rel.get("tag_name", ""),
                        "url": a.get("browser_download_url"),
                        "size": a.get("size", 0),
                        "staging": "staging" in low, "ver": ver,
                        "x86": is_x86}
                if ver == want and (exact is None
                                    or exact["staging"]
                                    or (want_x86 and is_x86
                                        and not exact.get("x86"))):
                    exact = item
                elif ver[0] == want[0]:
                    nearby.append(item)
        if exact:
            break
        if len(data) < 100:
            break

    if exact:
        if line:
            line(f"→ Найдена сборка Wine {version}: {exact['name']} "
                 f"({exact['size'] // 1048576} МБ)", "info")
        return exact

    if nearby:
        # ближайшая версия той же ветки, обычные сборки предпочтительнее staging
        nearby.sort(key=lambda i: (abs(i["ver"][1] - want[1]), i["staging"]))
        best = nearby[0]
        if line:
            line(f"○ Точной версии {version} нет, беру ближайшую из той же "
                 f"ветки: {best['name']}", "warn")
        return best

    if line:
        line(f"✗ Сборок ветки Wine {version} в репозитории не нашлось.", "warn")
    return None


def ensure_wine_version(app, line, progress, cancel):
    """Обеспечивает нужную программе версию Wine.

    У Kodu это 9.2: именно в ней разработчики Wine исправили ошибки, из-за
    которых программа падала. Если такой сборки на компьютере нет — она
    скачивается и закрепляется за программой."""
    want = app.get("wine_prefer_version")
    if not want:
        return None

    try:
        want_t = tuple(int(x) for x in str(want).split(".")[:2])
    except ValueError:
        want_t = None
    for path, origin in wine_candidates():
        have = wine_version_tuple(path)
        if want_t and have == want_t:
            if app.get("wine_needs_win32") and not wine_supports_win32(path):
                continue
            line(f"✓ Нужная версия Wine {want} уже есть ({origin}): {path}", "ok")
            set_wine_for_app(app["id"], path)
            return path

    line(f"→ Программе рекомендована версия Wine {want} — "
         "проверяю, есть ли она…", "run")
    # Если программе нужен win32, ищем прежде всего чисто 32-битную сборку:
    # в amd64-сборках 32-битной части может не быть вовсе, и тогда скачанное
    # окажется бесполезным (ровно это и вышло с wine-9.2-amd64).
    item = find_wine_build_version(want, line,
                                   want_x86=bool(app.get("wine_needs_win32")))
    if not item:
        line(f"   Продолжу с текущей сборкой; если программа не запустится, "
             "сработает автоподбор.", "warn")
        return None
    path = install_wine_build(item, line, progress, cancel)
    if not path:
        return None
    if app.get("wine_needs_win32") and not wine_supports_win32(path):
        line("   В скачанной сборке нет 32-битной части — не подходит.", "warn")
        # снимаем закрепление: иначе на следующем запуске find_wine снова
        # вернёт эту непригодную сборку из настроек
        st = load_settings()
        if (st.get("wine_by_app") or {}).pop(app["id"], None):
            save_settings(st)
        line("   Возьму сборку, в которой 32-битная часть есть.", "info")
        return None
    set_wine_for_app(app["id"], path)
    line(f"✓ Для «{app['name']}» будет использована сборка "
         f"{wine_version(path) or want}", "ok")
    return path


def install_wine_build(item, line, progress, cancel):
    """Скачивает и распаковывает выбранную сборку, возвращает путь к wine."""
    dest = download_file(item["url"],
                         os.path.join(WINE_BUILDS_DIR, item["name"]),
                         line, progress, cancel)
    if not dest:
        return None
    target = os.path.join(WINE_BUILDS_DIR, _strip_ext(item["name"]))
    if os.path.isdir(target):
        shutil.rmtree(target, ignore_errors=True)
    _user_makedirs(target)
    line(f"→ Распаковываю {item['name']}…", "run")
    try:
        extract_archive(dest, target)
    except Exception as e:
        line(f"✗ Не удалось распаковать: {e}", "err")
        return None
    for path in sorted(globmod.glob(os.path.join(target, "**", "bin", "wine"),
                                    recursive=True)):
        try:
            for f in globmod.glob(os.path.join(os.path.dirname(path), "*")):
                os.chmod(f, 0o755)
        except OSError:
            pass
        _chown_to_user(WINE_BUILDS_DIR)
        return path
    return None


def _window_tools():
    """Чем можно проверить, появилось ли окно у программы."""
    return shutil.which("wmctrl"), shutil.which("xdotool")


def has_visible_window(pid, deadline):
    """Появилось ли у процесса (или его потомков) окно на экране.

    Без этой проверки «программа жива N секунд» — плохой признак: Wine
    может держать процесс без единого окна, и подбор посчитает такую
    конфигурацию рабочей, перезаписав действительно рабочую."""
    wmctrl, xdotool = _window_tools()
    if not (wmctrl or xdotool):
        return None                      # проверить нечем
    pids = {str(pid)}
    try:
        # потомки: Wine запускает программу через свои процессы
        out = subprocess.run(["ps", "-o", "pid=", "--ppid", str(pid)],
                             capture_output=True, text=True, timeout=10)
        pids.update(x.strip() for x in (out.stdout or "").split() if x.strip())
    except (OSError, subprocess.SubprocessError):
        pass

    while time.time() < deadline:
        try:
            if xdotool:
                for p in list(pids):
                    r = subprocess.run(["xdotool", "search", "--pid", p],
                                       capture_output=True, text=True, timeout=10)
                    if r.returncode == 0 and (r.stdout or "").strip():
                        return True
            if wmctrl:
                r = subprocess.run(["wmctrl", "-lp"], capture_output=True,
                                   text=True, timeout=10)
                for ln in (r.stdout or "").splitlines():
                    parts = ln.split()
                    if len(parts) > 2 and parts[2] in pids:
                        return True
        except (OSError, subprocess.SubprocessError):
            return None
        time.sleep(2)
    return False


def trial_launch(app, wine, exe, seconds, line, cancel):
    """Запускает программу и смотрит, действительно ли она заработала.

    Успех = процесс жив И (если есть чем проверить) появилось окно."""
    arch = read_marker(app["id"]).get("wine_arch") or app.get("wine_arch") or "win32"
    wine = wine_exe_for_arch(wine, arch)
    env = _launch_env(wine_env(
        wine_prefix(app["id"]), arch, wine, app.get("wine_env_extra")))
    try:
        proc = subprocess.Popen(_as_user([wine, exe]), env=env,
                                cwd=wine_prefix(app["id"]),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, text=True,
                                encoding="utf-8", errors="replace",
                                start_new_session=True)
    except OSError as e:
        line(f"   не удалось запустить: {e}", "err")
        return False

    collected = []

    def reader():
        try:
            for raw in proc.stdout:
                collected.append(raw.rstrip("\n"))
        except (OSError, ValueError):
            pass

    threading.Thread(target=reader, daemon=True).start()
    start = time.time()
    while time.time() - start < seconds:
        if cancel() or proc.poll() is not None:
            break
        time.sleep(1)
    alive = proc.poll() is None
    windowed = None
    if alive:
        windowed = has_visible_window(proc.pid, time.time() + 8)
    if not alive:
        time.sleep(0.5)
    try:
        proc.terminate()
        proc.wait(timeout=10)
    except (OSError, subprocess.SubprocessError):
        try:
            proc.kill()
        except OSError:
            pass
    text = "\n".join(collected)
    crashed = any(m in text for m in ("Unhandled exception", "page fault",
                                      "Backtrace:", "wine: Call from"))
    if crashed:
        for ln in [t for t in collected
                   if "Unhandled exception" in t or "page fault" in t][:1]:
            line("     " + ln[:120], "info")
    if alive and not crashed and windowed is False:
        line("     процесс работает, но окно не появилось — считаю неудачей",
             "warn")
        return False
    return alive and not crashed


def save_working_config(app_id, marker):
    """Запоминает конфигурацию, при которой программа реально запускалась."""
    data = read_marker(app_id)
    data["working"] = {"exec": marker.get("exec"), "env": marker.get("env"),
                       "workdir": marker.get("workdir"),
                       "wine_arch": marker.get("wine_arch"),
                       "saved_at": datetime.now().isoformat()}
    try:
        path = os.path.join(MARKERS_DIR, f"{app_id}.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        _chown_to_user(MARKERS_DIR)
    except OSError:
        pass


def restore_working_config(app_id, line=None):
    """Возвращает последнюю конфигурацию, при которой программа работала."""
    data = read_marker(app_id)
    good = data.get("working")
    if not good or not good.get("exec"):
        if line:
            line("   Сохранённой рабочей настройки нет.", "warn")
        return False
    data.update({k: v for k, v in good.items() if k != "saved_at"})
    try:
        path = os.path.join(MARKERS_DIR, f"{app_id}.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        _chown_to_user(MARKERS_DIR)
    except OSError:
        return False
    # и сборку Wine возвращаем ту же
    exec_cmd = good.get("exec") or []
    if exec_cmd:
        set_wine_for_app(app_id, exec_cmd[0])
    if line:
        line(f"✓ Возвращена рабочая настройка от "
             f"{good.get('saved_at', '')[:16].replace('T', ' ')}", "ok")
    return True


def auto_pick_graphics(app, exe, wine, line, cancel):
    """Перебирает профили вывода графики, пока программа не заработает.

    Артефакты программно не распознать, зато падение — вполне. Профили
    заданы в courses.json полем wine_env_profiles; первым идёт тот, что
    проверен на практике."""
    profiles = app.get("wine_env_profiles") or []
    if not profiles:
        return None
    base = dict(app.get("wine_env_extra") or {})
    for prof in profiles:
        if cancel():
            return None
        env_extra = dict(base)
        env_extra.update(prof.get("env") or {})
        line(f"→ Пробую режим графики: {prof.get('name', 'без названия')}", "run")
        probe = dict(app)
        probe["wine_env_extra"] = env_extra
        if trial_launch(probe, wine, exe, app.get("wine_verify_seconds", 20),
                        line, cancel):
            line(f"✓ Работает: {prof.get('name')}", "ok")
            return env_extra
        line("✗ В этом режиме программа не запускается", "err")
    line("○ Ни один режим графики не подошёл — оставляю как было.", "warn")
    return None


def auto_pick_wine(app, exe, current, line, progress, cancel):
    """Автоматически подбирает сборку Wine, в которой программа запускается.

    Вызывается сразу после установки, чтобы техник не занимался этим сам:
    сначала проверяется текущая сборка, затем другие имеющиеся, затем при
    необходимости скачиваются версии постарше (частый случай — регрессия в
    новом Wine)."""
    seconds = app.get("wine_verify_seconds", 20)
    need32 = bool(app.get("wine_needs_win32"))

    if read_marker(app["id"]).get("working"):
        line("   (рабочие настройки сохранены — если подбор ничего лучше "
             "не найдёт, они вернутся автоматически)", "info")
    line(f"→ Проверяю, запускается ли {app['name']} (до {seconds} с)…", "run")
    if trial_launch(app, current, exe, seconds, line, cancel):
        line("✓ Программа запускается на текущей сборке Wine — "
             "ничего менять не буду", "ok")
        save_working_config(app["id"], read_marker(app["id"]))
        return current

    line("✗ На текущей сборке программа падает. Подбираю другую "
         "автоматически…", "warn")

    tried = {os.path.realpath(current)}
    for path, origin in wine_candidates():
        if cancel():
            return None
        real = os.path.realpath(path)
        if real in tried:
            continue
        tried.add(real)
        if need32 and not wine_supports_win32(path):
            continue
        line(f"→ Пробую {wine_version(path) or path}  ({origin})", "run")
        if trial_launch(app, path, exe, seconds, line, cancel):
            line(f"✓ Подходит: {wine_version(path) or path}", "ok")
            set_wine_for_app(app["id"], path)
            return path

    # ничего из имеющегося не подошло — качаем версии постарше
    wanted = app.get("wine_fallback_versions") or ["10.0", "9.0", "8.0"]
    line(f"→ Ни одна из имеющихся сборок не подошла. Скачиваю версии "
         f"постарше: {', '.join(wanted)}", "run")
    online = list_wine_builds_online()
    if not online:
        line("✗ Список сборок получить не удалось (нет интернета или лимит "
             "GitHub).", "err")
        return None

    for ver in wanted:
        if cancel():
            return None
        match = None
        for item in online:
            low = item["name"].lower()
            if f"-{ver}-" in low and not item["staging"]:
                match = item
                break
        if not match:
            for item in online:
                if f"-{ver}-" in item["name"].lower():
                    match = item
                    break
        if not match:
            line(f"   версии {ver} в списке нет — пропускаю", "info")
            continue
        line(f"→ Скачиваю {match['name']} "
             f"({match['size'] // 1048576} МБ)…", "run")
        path = install_wine_build(match, line, progress, cancel)
        if not path:
            continue
        if need32 and not wine_supports_win32(path):
            line("   в этой сборке нет 32-битной части — пропускаю", "warn")
            continue
        line(f"→ Пробую {wine_version(path) or path}", "run")
        if trial_launch(app, path, exe, seconds, line, cancel):
            line(f"✓ Подходит: {wine_version(path) or path}", "ok")
            set_wine_for_app(app["id"], path)
            return path
        line(f"✗ {wine_version(path) or ver}: тоже падает", "err")

    # Ничего лучше не нашли — возвращаем исходную сборку, чтобы подбор не
    # сделал хуже, чем было. Раньше это было настоящей проблемой: программа
    # работала, а после перебора переставала запускаться.
    line("○ Ни одна другая сборка не подошла — возвращаю исходную "
         "конфигурацию.", "warn")
    set_wine_for_app(app["id"], current)
    restore_working_config(app["id"], line)
    return None


class WineTrialWorker(QThread):
    """Перебирает сборки Wine и находит ту, в которой программа запускается.

    Проверка честная: программа действительно запускается, и если она
    прожила заданное время и не упала — сборка считается рабочей."""

    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(str)

    CRASH_MARKS = ("Unhandled exception", "page fault", "wine: Call from",
                   "err:module:", "Backtrace:")

    def __init__(self, app, candidates, alive_seconds=25, download=None):
        super().__init__()
        self.app = app
        self.candidates = candidates      # [(путь, откуда)]
        self.alive = alive_seconds
        self.download = download or []    # сборки, которые нужно скачать
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def _line(self, t, k="info"):
        self.sig_line.emit(t, k)

    def _exe(self):
        m = read_marker(self.app["id"])
        cmd = m.get("exec")
        if isinstance(cmd, list) and len(cmd) > 1:
            return cmd[1]
        return None

    def _try(self, wine, exe):
        """Запускает программу и смотрит, выживет ли она."""
        arch = (read_marker(self.app["id"]).get("wine_arch")
                or self.app.get("wine_arch") or "win32")
        wine = wine_exe_for_arch(wine, arch)
        env = _launch_env(wine_env(wine_prefix(self.app["id"]), arch,
                                   wine, self.app.get("wine_env_extra")))
        try:
            proc = subprocess.Popen(_as_user([wine, exe]), env=env,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    stdin=subprocess.DEVNULL, text=True,
                                    encoding="utf-8", errors="replace",
                                    start_new_session=True)
        except OSError as e:
            self._line(f"   не удалось запустить: {e}", "err")
            return False, ""

        collected = []

        def reader():
            try:
                for raw in proc.stdout:
                    collected.append(raw.rstrip("\n"))
            except (OSError, ValueError):
                pass

        threading.Thread(target=reader, daemon=True).start()

        start = time.time()
        while time.time() - start < self.alive:
            if self._cancel:
                break
            if proc.poll() is not None:
                break
            left = int(self.alive - (time.time() - start))
            self.sig_progress.emit(f"Проверяю запуск… осталось {left} с")
            time.sleep(1)

        alive = proc.poll() is None
        if not alive:
            time.sleep(0.5)      # дать потоку чтения забрать последние строки
        try:
            proc.terminate()
            proc.wait(timeout=10)
        except (OSError, subprocess.SubprocessError):
            try:
                proc.kill()
            except OSError:
                pass
        text = "\n".join(collected)
        crashed = any(mark in text for mark in self.CRASH_MARKS)
        return (alive and not crashed), text

    def run(self):
        name = self.app["name"]
        exe = self._exe()
        if not exe or not os.path.exists(exe):
            self._line(f"✗ {name}: программа не установлена — сначала "
                       "установите её, потом подбирайте сборку Wine.", "err")
            self.sig_done.emit("")
            return

        self._line(f"═══ Подбор рабочей сборки Wine для «{name}» ═══", "run")
        self._line(f"   Программа: {exe}", "info")
        self._line(f"   Каждая сборка проверяется запуском на {self.alive} с. "
                   "Окна программы будут появляться и закрываться — так и надо.",
                   "info")

        tried = []
        for item in self.download:
            if self._cancel:
                break
            self._line(f"→ Скачиваю сборку {item['name']}…", "run")
            path = install_wine_build(item, self._line, self.sig_progress.emit,
                                      lambda: self._cancel)
            if path:
                self.candidates.append((path, f"скачана ({item['tag']})"))

        for wine, origin in self.candidates:
            if self._cancel:
                self._line("⚠ Отменено", "warn")
                break
            ver = wine_version(wine) or os.path.basename(wine)
            if not wine_supports_win32(wine) and \
                    (self.app.get("wine_needs_win32")
                     or read_marker(self.app["id"]).get("wine_arch") == "win32"):
                self._line(f"○ {ver}: пропускаю — сборка без 32-битной части", "info")
                continue
            self._line(f"→ Пробую {ver}  ({origin})", "run")
            ok, text = self._try(wine, exe)
            tried.append((ver, wine, ok))
            if ok:
                self._line(f"✓ {ver}: программа проработала {self.alive} с "
                           "и не упала — эта сборка подходит!", "ok")
                set_wine_for_app(self.app["id"], wine)
                save_working_config(self.app["id"], read_marker(self.app["id"]))
                self._line(f"✓ Сборка закреплена за «{name}». Остальные "
                           "программы продолжат работать на своей.", "ok")
                self.sig_done.emit(wine)
                return
            reason = "упала с ошибкой" if text else "закрылась сразу"
            self._line(f"✗ {ver}: {reason}", "err")
            for ln in [t for t in text.splitlines()
                       if any(m in t for m in self.CRASH_MARKS)][:2]:
                self._line("     " + ln[:120], "info")

        self._line("═══ Итог ═══", "run")
        for ver, _w, ok in tried:
            self._line(f"   {'✓' if ok else '✗'} {ver}", "ok" if ok else "err")
        if not any(ok for _v, _w, ok in tried):
            self._line("✗ Ни одна из проверенных сборок не подошла.", "err")
            self._line("→ Возвращаю то, что было до подбора, чтобы не сделать "
                       "хуже.", "warn")
            restore_working_config(self.app["id"], self._line)
            self._line("   Попробуйте «⬇ Скачать другую версию Wine…» и выбрать "
                       "версию постарше — часто помогает 9.x или 8.x.", "warn")
        self.sig_done.emit("")


# ---------------------------------------------------------------------------
# Настройки Wine
# ---------------------------------------------------------------------------

# Компоненты Windows, которые чаще всего требуются учебным программам.
WINE_COMPONENTS = [
    ("remove_mono", "Убрать встроенный Mono — ОБЯЗАТЕЛЬНО перед установкой .NET"),
    ("dotnet48", "Microsoft .NET 4.8 — нужен Kodu Game Lab (ставить ПЕРВЫМ)"),
    ("xna40", "Microsoft XNA 4.0 — нужен Kodu Game Lab (ставить вторым, до самой Kodu)"),
    ("dotnet40", "Microsoft .NET 4.0 — более старый вариант, если 4.8 не встал"),
    ("d3dx9", "DirectX 9 (d3dx9) — старые игры и Algodoo"),
    ("d3dcompiler_47", "Компилятор шейдеров — часть игр на Unity"),
    ("vcrun2008", "Visual C++ 2008 — нужен Algodoo"),
    ("vcrun2019", "Visual C++ 2015–2019 — очень многим программам"),
    ("corefonts", "Шрифты Microsoft — если в программе «квадратики» вместо букв"),
    ("dxvk", "DXVK — DirectX через Vulkan, иногда сильно ускоряет графику"),
]

WINE_WINVER = ["winxp", "win7", "win10"]


class WineToolWorker(QThread):
    """Долгие операции Wine (winecfg, winetricks, установка компонентов)
    в отдельном потоке, с выводом в журнал главного окна."""
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(int)

    def __init__(self, cmd, env):
        super().__init__()
        self.cmd = cmd
        self.env = env
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        code = _stream_env(self.cmd, self.env,
                           lambda t, k="info": self.sig_line.emit(t, k),
                           lambda t: self.sig_progress.emit(t),
                           lambda: self._cancel)
        self.sig_done.emit(code)


class _WinetricksUpdateWorker(QThread):
    sig_line = pyqtSignal(str, str)
    sig_progress = pyqtSignal(str)
    sig_done = pyqtSignal(str)

    def run(self):
        path = update_winetricks(lambda t, k="info": self.sig_line.emit(t, k),
                                 lambda t: self.sig_progress.emit(t),
                                 lambda: False)
        self.sig_done.emit(path or "")


class WineSettingsDialog(QDialog):
    """Управление окружениями Wine: настройки, компоненты, диагностика.

    У каждой Windows-программы своё окружение (префикс), поэтому все действия
    выполняются над выбранным в списке."""

    def __init__(self, apps, parent=None):
        super().__init__(parent)
        self.win = parent
        self.apps = apps          # {id: app} — только программы с Wine
        self.worker = None
        self.setWindowTitle("Настройки Wine")
        self.resize(760, 620)
        self._build()
        self._refresh()

    def _build(self):
        v = QVBoxLayout(self)

        self.wine_label = QLabel()
        self.wine_label.setWordWrap(True)
        v.addWidget(self.wine_label)

        v.addWidget(QLabel("Окружение (у каждой программы своё):"))
        self.app_list = QListWidget()
        self.app_list.itemSelectionChanged.connect(self._app_changed)
        v.addWidget(self.app_list, stretch=1)

        self.prefix_label = QLabel()
        self.prefix_label.setWordWrap(True)
        self.prefix_label.setStyleSheet("color:#888; font-size:12px;")
        v.addWidget(self.prefix_label)

        tools = QHBoxLayout()
        for text, tip, slot in (
            ("⚙ winecfg", "Настройки Wine: версия Windows, графика, диски, звук.",
             self._winecfg),
            ("🧰 winetricks", "Графическое окно winetricks — установка любых "
                              "компонентов Windows вручную.", self._winetricks),
            ("📁 Открыть папку", "Открыть диск C: этого окружения в файловом менеджере.",
             self._open_prefix),
            ("🗑 Сбросить", "Полностью удалить окружение — программу придётся "
                            "установить заново.", self._reset_prefix),
        ):
            b = QPushButton(text)
            b.setToolTip(tip)
            b.clicked.connect(slot)
            tools.addWidget(b)
        v.addLayout(tools)

        wrow = QHBoxLayout()
        self.wine_pick = QPushButton("🔀 Выбрать другой Wine…")
        self.wine_pick.setToolTip("Если в системе несколько сборок Wine "
                                  "(staging, Lutris, /opt) — выбрать, какой использовать.")
        self.wine_pick.clicked.connect(self._pick_wine)
        wrow.addWidget(self.wine_pick)
        self.wine_get = QPushButton("⬇ Скачать свежий Wine…")
        self.wine_get.setToolTip("Отдельная сборка Wine (staging) с GitHub, "
                                 "ставится в домашнюю папку и не трогает системный Wine. "
                                 "Помогает, когда в дистрибутиве Wine старый.")
        self.wine_get.clicked.connect(self._download_wine)
        wrow.addWidget(self.wine_get)
        self.wt_upd = QPushButton("⟳ Обновить winetricks")
        self.wt_upd.setToolTip("Свежий winetricks нужен для установки dotnet48 и "
                               "других компонентов: в старых версиях рецепты "
                               "устаревают и ссылки на файлы Microsoft не работают.")
        self.wt_upd.clicked.connect(self._update_winetricks)
        wrow.addWidget(self.wt_upd)
        self.trial_btn = QPushButton("🧪 Подобрать рабочую сборку")
        self.trial_btn.setToolTip(
            "Перебирает сборки Wine и запускает программу в каждой.\n"
            "Нужно, когда в новой версии Wine появилась регрессия и программа "
            "перестала запускаться.\nНайденная сборка закрепляется только за "
            "этой программой.")
        self.trial_btn.clicked.connect(self._trial_wine)
        wrow.addWidget(self.trial_btn)
        self.diag_btn = QPushButton("🩺 Диагностика")
        self.diag_btn.setToolTip("Проверить окружение выбранной программы: версия Wine, "
                                 "владелец папки, разрядность, установленные компоненты. "
                                 "Результат — в журнале главного окна.")
        self.diag_btn.clicked.connect(self._diagnose)
        wrow.addWidget(self.diag_btn)
        wrow.addStretch()
        v.addLayout(wrow)

        row2 = QHBoxLayout()
        row2.addWidget(QLabel("Версия Windows:"))
        self.winver = QListWidget()
        self.winver.setMaximumHeight(28 * len(WINE_WINVER))
        self.winver.setMaximumWidth(140)
        for w in WINE_WINVER:
            self.winver.addItem(w)
        row2.addWidget(self.winver)
        set_ver = QPushButton("Применить версию")
        set_ver.setToolTip("Некоторые программы работают только под конкретной "
                           "версией Windows (Kodu — под win7 или winxp).")
        set_ver.clicked.connect(self._set_winver)
        row2.addWidget(set_ver)
        row2.addStretch()
        v.addLayout(row2)

        v.addWidget(QLabel("Компоненты Windows (отметьте нужные и нажмите «Установить»):"))
        self.comp_list = QListWidget()
        self.comp_list.setSelectionMode(QListWidget.MultiSelection)
        for name, desc in WINE_COMPONENTS:
            it = QListWidgetItem(f"{name} — {desc}")
            it.setData(Qt.UserRole, name)
            self.comp_list.addItem(it)
        v.addWidget(self.comp_list, stretch=1)

        row3 = QHBoxLayout()
        self.install_btn = QPushButton("⬇ Установить отмеченные компоненты")
        self.install_btn.setToolTip("Загружается из интернета, может занять "
                                    "10–30 минут. Прогресс виден в журнале окна.")
        self.install_btn.clicked.connect(self._install_components)
        row3.addWidget(self.install_btn)
        run_exe = QPushButton("▶ Запустить .exe в этом окружении…")
        run_exe.setToolTip("Полезно, чтобы проверить программу или запустить "
                           "её собственный установщик/настройщик.")
        run_exe.clicked.connect(self._run_exe)
        row3.addWidget(run_exe)
        row3.addStretch()
        v.addLayout(row3)

        self.status = QLabel("")
        self.status.setWordWrap(True)
        self.status.setStyleSheet("color:#888; font-size:12px;")
        v.addWidget(self.status)

        box = QDialogButtonBox(QDialogButtonBox.Close)
        box.rejected.connect(self.reject)
        v.addWidget(box)

    # ---- состояние ----
    def _refresh(self):
        wine = find_wine()
        if wine:
            ver = wine_version(wine)
            wtp = find_winetricks()
            wtv = winetricks_version(wtp) if wtp else None
            if not wtp:
                wt = "winetricks: НЕ установлен (нужен для компонентов)"
            elif wtv and wtv >= WINETRICKS_MIN:
                wt = f"winetricks: {wtv} ✓"
            else:
                wt = f"winetricks: {wtv or '?'} — устарел, нажмите «⟳ Обновить»"
            origin = "выбран вручную" if load_settings().get("wine_binary") == wine \
                else "системный"
            self.wine_label.setText(
                f"<b>Wine:</b> {ver or wine} ({origin})<br>"
                f"<span style='color:#888'>{wine} &nbsp;•&nbsp; {wt} &nbsp;•&nbsp; "
                f"найдено сборок в системе: {len(wine_candidates())}</span>")
        else:
            self.wine_label.setText(
                "<b>Wine в системе не найден.</b> Установите: "
                "<code>sudo dnf install wine winetricks</code> (ROSA) или "
                "<code>sudo apt-get install wine winetricks</code> (Альт/Astra).")

        self.app_list.clear()
        for aid, app in self.apps.items():
            prefix = wine_prefix(aid)
            exists = os.path.isdir(prefix)
            size = ""
            if exists:
                try:
                    total = sum(os.path.getsize(os.path.join(r, f))
                                for r, _d, fs in os.walk(prefix) for f in fs
                                if os.path.exists(os.path.join(r, f)))
                    size = f", {total // 1048576} МБ"
                except OSError:
                    pass
            state = f"создано{size}" if exists else "ещё не создано"
            pinned = (load_settings().get("wine_by_app") or {}).get(aid)
            if pinned:
                state += f", Wine: {wine_version(pinned) or 'своя сборка'}"
            it = QListWidgetItem(f"{app['name']}   [{state}]")
            it.setData(Qt.UserRole, aid)
            self.app_list.addItem(it)
        if self.app_list.count():
            self.app_list.setCurrentRow(0)

    def _current(self):
        items = self.app_list.selectedItems()
        if not items:
            return None, None, None
        aid = items[0].data(Qt.UserRole)
        app = self.apps[aid]
        return aid, app, wine_prefix(aid)

    def _app_changed(self):
        aid, app, prefix = self._current()
        if not aid:
            return
        arch = app.get("wine_arch", "win32")
        self.prefix_label.setText(f"Папка окружения: {prefix}\nРазрядность: {arch} "
                                  f"(меняется только пересозданием окружения)")

    def _env(self):
        aid, app, prefix = self._current()
        if not aid:
            return None
        return wine_env(prefix,
                        read_marker(aid).get("wine_arch")
                        or app.get("wine_arch") or "win64",
                        find_wine())

    # ---- действия ----
    def _busy(self, on):
        self.install_btn.setEnabled(not on)
        self.status.setText("Выполняется… смотрите журнал в главном окне." if on else "")

    def _run(self, cmd, need_wine=True):
        if need_wine and not find_wine():
            QMessageBox.warning(self, "Нет Wine", "Wine не установлен.")
            return
        env = self._env()
        if not env:
            QMessageBox.information(self, "Выберите программу",
                                    "Сначала выберите окружение в списке.")
            return
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Предыдущая операция ещё идёт.")
            return
        _user_makedirs(env["WINEPREFIX"])
        self._busy(True)
        self.worker = WineToolWorker(cmd, env)
        if self.win:
            self.worker.sig_line.connect(self.win.log)
            self.worker.sig_progress.connect(self.win.log_progress)
        self.worker.sig_done.connect(self._finished)
        self.worker.start()

    def _finished(self, code):
        self._busy(False)
        self._refresh()
        if self.win:
            self.win.log(f"═══ Wine: операция завершена (код {code}) ═══",
                         "ok" if code == 0 else "warn")

    def _update_winetricks(self):
        """Качает свежий winetricks в домашнюю папку.

        Системный пакет не трогаем: для него нужен root, а --self-update
        у пакетной версии обычно не работает."""
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Предыдущая операция ещё идёт.")
            return
        self._busy(True)
        self.wt_worker = _WinetricksUpdateWorker()
        if self.win:
            self.wt_worker.sig_line.connect(self.win.log)
            self.wt_worker.sig_progress.connect(self.win.log_progress)
        self.wt_worker.sig_done.connect(self._wt_updated)
        self.wt_worker.start()

    def _wt_updated(self, path):
        self._busy(False)
        self._refresh()
        if path:
            QMessageBox.information(
                self, "winetricks обновлён",
                f"Версия {winetricks_version(path)}\n{path}\n\n"
                "Системный winetricks не изменён — установщик будет "
                "пользоваться этой копией.")
        else:
            QMessageBox.warning(self, "Не получилось",
                                "Подробности в журнале главного окна.")

    def _diagnose(self):
        """Собирает всё, что нужно знать об окружении, в журнал одним нажатием.

        Нужно, чтобы не гадать: реально ли встали компоненты, та ли версия
        Wine, та ли разрядность, есть ли сама программа."""
        aid, app, prefix = self._current()
        if not aid:
            QMessageBox.information(self, "Выберите программу",
                                    "Сначала выберите окружение в списке.")
            return
        log = self.win.log if self.win else (lambda t, k="info": None)
        log(f"═══ Диагностика окружения: {app['name']} ═══", "run")

        wine = find_wine()
        ver = wine_version(wine) if wine else "не найден"
        log(f"Wine: {ver}   ({wine or '—'})", "info")
        need = app.get("wine_min_version")
        if need and wine:
            have = wine_version_tuple(wine)
            parts = str(need).split(".")
            need_t = (int(parts[0]), int(parts[1]) if len(parts) > 1 else 0)
            if have and have < need_t:
                log(f"✗ Версия Wine ниже требуемой {need} — это и есть причина. "
                    "Нажмите «⬇ Скачать свежий Wine…».", "err")
            else:
                log(f"✓ Версия Wine подходит (нужна не ниже {need})", "ok")

        if not os.path.isdir(prefix):
            log("✗ Окружение ещё не создано — установите программу.", "err")
            return
        st = os.stat(prefix)
        try:
            import pwd
            owner = pwd.getpwuid(st.st_uid).pw_name
        except (KeyError, ImportError):
            owner = str(st.st_uid)
        log(f"Папка окружения: {prefix}", "info")
        log(f"Владелец папки: {owner}" + (" ✓" if st.st_uid != 0 else
            "  ✗ — папка принадлежит root, Wine откажется работать!"),
            "info" if st.st_uid != 0 else "err")

        marker_arch = read_marker(aid).get("wine_arch")
        real_arch = "win64" if os.path.isdir(
            os.path.join(prefix, "drive_c", "Program Files (x86)")) else "win32"
        log(f"Разрядность окружения: {real_arch} "
            f"(в настройках программы: {app.get('wine_arch') or 'авто'}, "
            f"при установке: {marker_arch or '—'})", "info")

        exe = read_marker(aid).get("exec")
        exe = exe[1] if isinstance(exe, list) and len(exe) > 1 else None
        if exe and os.path.exists(exe):
            a = pe_arch(exe)
            log(f"Программа: {exe}", "info")
            log(f"Разрядность программы: {a or 'не определилась'}" +
                ("  ✗ НЕ СОВПАДАЕТ с окружением — будет «Bad EXE format»"
                 if a and a != real_arch else "  ✓"),
                "err" if a and a != real_arch else "ok")
        else:
            log("✗ Программа внутри окружения не найдена — установка не "
                "завершилась (мастер надо пройти до кнопки Finish).", "err")

        wt = find_winetricks()
        if wt:
            log(f"winetricks: {winetricks_version(wt) or '?'}   ({wt})", "info")
            try:
                r = subprocess.run(_as_user([wt, "list-installed"]),
                                   capture_output=True, text=True, timeout=90,
                                   env=_launch_env(self._env()))
                got = [ln.strip() for ln in (r.stdout or "").splitlines()
                       if ln.strip() and " " not in ln.strip()]
                log(f"Установленные компоненты: {', '.join(got) if got else '— ничего —'}",
                    "info" if got else "warn")
                for need_c in (app.get("wine_tricks") or []):
                    ok = need_c in got
                    log(f"   {need_c}: " + ("✓ есть" if ok else "✗ НЕ УСТАНОВЛЕН"),
                        "ok" if ok else "err")
            except (OSError, subprocess.SubprocessError) as e:
                log(f"Не удалось получить список компонентов: {e}", "warn")
        else:
            log("winetricks не установлен — компоненты поставить нечем.", "err")

        mono = os.path.join(prefix, "drive_c", "windows", "mono")
        if os.path.isdir(mono):
            log("⚠ В окружении есть встроенный Mono. Если программа на .NET падает "
                "с NullReferenceException — значит используется он вместо настоящего "
                ".NET. Поставьте dotnet48 и переустановите программу.", "warn")
        log("═══ Конец диагностики ═══", "run")

    def _pick_wine(self):
        """Выбор сборки Wine из уже имеющихся или указание файла вручную."""
        cands = wine_candidates()
        items = []
        for path, origin in cands:
            ver = wine_version(path)
            bits = "win32+win64" if wine_supports_win32(path) else "только win64"
            items.append(f"{ver or 'wine'}  [{bits}]  —  {path}  ({origin})")
        items.append("Указать файл вручную…")
        cur = load_settings().get("wine_binary")
        choice, ok = QInputDialog.getItem(
            self, "Какой Wine использовать",
            "Сейчас используется:\n" + (cur or find_wine() or "— не найден") +
            "\n\nВыберите сборку:", items, 0, False)
        if not ok:
            return
        if choice == items[-1]:
            path, _ = QFileDialog.getOpenFileName(
                self, "Выберите исполняемый файл wine", "/usr/bin", "wine (wine wine64 *)")
            if not path:
                return
        else:
            path = cands[items.index(choice)][0]
        st = load_settings()
        st["wine_binary"] = path
        save_settings(st)
        if self.win:
            self.win.log(f"✓ Выбран Wine: {path} ({wine_version(path)})", "ok")
        self._refresh()

    def _trial_wine(self):
        aid, app, prefix = self._current()
        if not aid:
            QMessageBox.information(self, "Выберите программу",
                                    "Сначала выберите программу в списке.")
            return
        if not os.path.isdir(prefix):
            QMessageBox.information(
                self, "Программа не установлена",
                f"«{app['name']}» ещё не установлена. Сначала установите её, "
                "потом подбирайте сборку Wine.")
            return

        have = wine_candidates()
        r = QMessageBox.question(
            self, "Подбор рабочей сборки",
            f"Сборок на компьютере: {len(have)}.\n\n"
            "Программа будет запущена в каждой по очереди — окна будут "
            "появляться и закрываться, это нормально. Проверка одной сборки "
            "занимает около 30 секунд.\n\n"
            "Скачать дополнительно версии постарше? Часто помогает, если "
            "программа перестала работать после обновления Wine.",
            QMessageBox.Yes | QMessageBox.No | QMessageBox.Cancel,
            QMessageBox.Yes)
        if r == QMessageBox.Cancel:
            return

        download = []
        if r == QMessageBox.Yes:
            if self.win:
                self.win.log("→ Смотрю доступные версии Wine…", "run")
            online = list_wine_builds_online()
            if not online:
                QMessageBox.warning(self, "Список не получен",
                                    "Не удалось получить список сборок. "
                                    "Проверю только те, что уже есть.")
            else:
                names = [f"{i['name']}  ({i['size'] // 1048576} МБ)"
                         for i in online]
                picked, ok = QInputDialog.getItem(
                    self, "Какую версию скачать",
                    "Если программа работала на старом Wine, выберите версию "
                    "постарше:", names, 0, False)
                if ok:
                    download = [online[names.index(picked)]]

        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Дождитесь окончания операции.")
            return
        self._busy(True)
        self.trial = WineTrialWorker(app, list(have), download=download)
        if self.win:
            self.trial.sig_line.connect(self.win.log)
            self.trial.sig_progress.connect(self.win.log_progress)
        self.trial.sig_done.connect(self._trial_done)
        self.trial.start()

    def _trial_done(self, wine):
        self._busy(False)
        self._refresh()
        aid, app, _p = self._current()
        if wine:
            QMessageBox.information(
                self, "Сборка найдена",
                f"Для «{app['name'] if app else ''}» закреплена сборка:\n"
                f"{wine_version(wine) or wine}\n\n"
                "Остальные программы продолжат работать на своей сборке.")
        else:
            QMessageBox.warning(
                self, "Подходящая сборка не найдена",
                "Ни одна из проверенных сборок не подошла. Попробуйте "
                "повторить и выбрать для скачивания версию постарше "
                "(9.x или 8.x) — подробности в журнале.")

    def _download_wine(self):
        """Качает отдельную сборку Wine с GitHub в домашнюю папку.

        Системный Wine при этом не трогается: если новая сборка не подойдёт,
        можно вернуться к старой кнопкой «Выбрать другой Wine»."""
        repo, ok = QInputDialog.getText(
            self, "Скачать сборку Wine",
            "Репозиторий GitHub со сборками Wine:\n\n"
            "По умолчанию — Kron4ek/Wine-Builds: готовые сборки wine-staging,\n"
            "распаковываются в домашнюю папку и не требуют прав root.\n"
            "Можно указать любой другой репозиторий.",
            QLineEdit.Normal, "Kron4ek/Wine-Builds")
        if not ok or not repo.strip():
            return
        if self.win:
            self.win.log(f"═══ Загрузка сборки Wine из {repo} ═══", "run")
        dlg = GitHubSearchDialog(
            {"id": "_wine", "name": "Wine (сборка)", "github": repo.strip(),
             "file": "_wine/wine.tar.xz"}, self.win)
        if self.win:
            self.win.log("   Подсказка: для Kodu и других программ, которым нужно "
                         "32-битное окружение, берите файл БЕЗ слова wow64 в "
                         "названии (например wine-11.13-amd64.tar.xz, а не "
                         "wine-11.13-amd64-wow64.tar.xz).", "warn")
        dlg.query.setText(repo.strip())
        dlg._search()
        dlg.exec_()
        if not dlg.saved_path:
            return
        self._unpack_wine(dlg.saved_path)

    def _unpack_wine(self, archive):
        target = _user_makedirs(WINE_BUILDS_DIR)
        name = _strip_ext(os.path.basename(archive))
        dest = os.path.join(target, name)
        if os.path.isdir(dest):
            shutil.rmtree(dest, ignore_errors=True)
        os.makedirs(dest, exist_ok=True)
        if self.win:
            self.win.log(f"→ Распаковываю {os.path.basename(archive)}…", "run")
        try:
            extract_archive(archive, dest)
        except Exception as e:
            QMessageBox.warning(self, "Не удалось распаковать", str(e))
            return
        found = sorted(globmod.glob(os.path.join(dest, "**", "bin", "wine"),
                                    recursive=True))
        if not found:
            QMessageBox.warning(self, "Wine не найден",
                                "В архиве нет bin/wine — возможно, это не сборка Wine.")
            return
        path = found[0]
        try:
            for f in globmod.glob(os.path.join(os.path.dirname(path), "*")):
                os.chmod(f, 0o755)
        except OSError:
            pass
        _chown_to_user(target)
        st = load_settings()
        st["wine_binary"] = path
        save_settings(st)
        ver = wine_version(path)
        win32 = wine_supports_win32(path)
        if self.win:
            self.win.log(f"✓ Установлена сборка Wine: {ver or path}", "ok")
            self.win.log("   32-битные окружения: "
                         + ("поддерживаются" if win32 else
                            "НЕ поддерживаются (сборка wow64). Для Kodu "
                            "понадобится другая сборка — без wow64 в названии."),
                         "ok" if win32 else "warn")
            self.win.log("   Окружения, созданные старым Wine, лучше сбросить "
                         "и установить программы заново.", "warn")
        QMessageBox.information(
            self, "Готово",
            f"Теперь используется:\n{ver or path}\n\n"
            "Системный Wine не изменён — вернуться к нему можно кнопкой "
            "«Выбрать другой Wine».\n\n"
            "Ранее созданные окружения желательно сбросить и установить "
            "программы заново.")
        self._refresh()

    def _winecfg(self):
        self._run([find_wine() or "wine", "winecfg"])

    def _winetricks(self):
        wt = find_winetricks()
        if not wt:
            QMessageBox.warning(self, "Нет winetricks",
                                "Установите пакет winetricks:\n"
                                "ROSA: sudo dnf install winetricks\n"
                                "Альт/Astra: sudo apt-get install winetricks")
            return
        self._run([wt, "--gui"])

    def _set_winver(self):
        items = self.winver.selectedItems()
        if not items:
            QMessageBox.information(self, "Версия Windows",
                                    "Выберите версию в списке слева.")
            return
        self._run([find_wine() or "wine", "winecfg", "-v", items[0].text()])

    def _install_components(self):
        names = [i.data(Qt.UserRole) for i in self.comp_list.selectedItems()]
        if not names:
            QMessageBox.information(self, "Компоненты",
                                    "Отметьте хотя бы один компонент в списке.")
            return
        wt = find_winetricks()
        if not wt:
            QMessageBox.warning(self, "Нет winetricks",
                                "Установите пакет winetricks или нажмите "
                                "«⟳ Обновить winetricks» — он скачается "
                                "в домашнюю папку.")
            return
        r = QMessageBox.question(
            self, "Установка компонентов",
            f"Установить в это окружение: {', '.join(names)}?\n\n"
            "Компоненты качаются из интернета, это может занять 10–30 минут.\n"
            "Прогресс будет виден в журнале главного окна.",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
        if r == QMessageBox.Yes:
            self._run([wt, "-q"] + names)

    def _run_exe(self):
        aid, app, prefix = self._current()
        if not aid:
            return
        start = os.path.join(prefix, "drive_c")
        path, _ = QFileDialog.getOpenFileName(
            self, "Выберите .exe внутри окружения", start, "Windows-программы (*.exe)")
        if path:
            self._run([find_wine() or "wine", path])

    def _open_prefix(self):
        aid, app, prefix = self._current()
        if not aid:
            return
        target = os.path.join(prefix, "drive_c")
        if not os.path.isdir(target):
            QMessageBox.information(self, "Окружения ещё нет",
                                    "Сначала установите программу — окружение "
                                    "создаётся при установке.")
            return
        try:
            subprocess.Popen(_as_user(["xdg-open", target]), start_new_session=True)
        except OSError as e:
            QMessageBox.warning(self, "Не удалось открыть", str(e))

    def _reset_prefix(self):
        aid, app, prefix = self._current()
        if not aid or not os.path.isdir(prefix):
            QMessageBox.information(self, "Нечего сбрасывать",
                                    "Окружение ещё не создано.")
            return
        r = QMessageBox.question(
            self, "Сброс окружения",
            f"Удалить окружение «{app['name']}» целиком?\n\n{prefix}\n\n"
            "Программу внутри него придётся установить заново.",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r != QMessageBox.Yes:
            return
        remove_prefix(prefix, find_wine(aid),
                      self.win.log if self.win else None)
        remove_marker(aid)
        remove_desktop_entry(aid)
        if self.win:
            self.win.log(f"→ Окружение Wine удалено: {prefix}", "warn")
            self.win._refresh_statuses()
        self._refresh()


# ---------------------------------------------------------------------------
# Отчёт о компьютере (для сравнения машин в классе)
# ---------------------------------------------------------------------------

REPORTS_DIR = os.path.join(DATA_DIR, "reports")


class SystemReportWorker(QThread):
    """Собирает состояние компьютера в один текстовый файл.

    Нужно, когда в классе одинаковые с виду ПК ведут себя по-разному:
    снимаем отчёт на работающем и на неработающем и сравниваем построчно.
    Всё выполняется от имени пользователя — иначе браузер по умолчанию и
    содержимое ~/.var будут не те."""

    sig_line = pyqtSignal(str, str)
    sig_done = pyqtSignal(str)

    def _run(self, args, shell=False, timeout=60):
        try:
            cmd = ["sh", "-c", args] if shell else args
            r = subprocess.run(_as_user(cmd), capture_output=True, text=True,
                               timeout=timeout, env=_launch_env())
            out = ((r.stdout or "") + (r.stderr or "")).strip()
            return out or "(пусто)"
        except (OSError, subprocess.SubprocessError) as e:
            return f"(не удалось выполнить: {e})"

    def run(self):
        lines = []

        def add(title, value):
            value = " ".join(str(value).split()) or "НЕ ЗАДАНО"
            lines.append(f"{title}: {value}")

        def section(name):
            lines.append("")
            lines.append("=" * 70)
            lines.append(name)
            lines.append("=" * 70)

        host = socket.gethostname()
        lines.append(f"Отчёт о компьютере  —  {host}")
        lines.append(f"Снят: {datetime.now().strftime('%d.%m.%Y %H:%M')}")

        section("СИСТЕМА")
        add("Дистрибутив", DISTRO_NAME)
        add("Ядро", self._run(["uname", "-r"]))
        add("Пакеты", f".{PKG_FAMILY} ({PKG_MANAGER})")
        add("Пользователь", (real_user()[0] or os.environ.get("USER", "?")))
        add("Сеанс", os.environ.get("XDG_SESSION_TYPE", "?"))

        section("ГРАФИКА  (от неё зависит окно входа Roblox)")
        add("Видеокарта", self._run(
            "lspci 2>/dev/null | grep -iE 'vga|3d|display' || echo '(lspci нет)'",
            shell=True))
        add("Прямой рендеринг", self._run(
            "glxinfo 2>/dev/null | grep -i 'direct rendering' "
            "|| echo '(glxinfo нет: sudo apt-get install mesa-utils)'", shell=True))
        add("OpenGL", self._run(
            "glxinfo 2>/dev/null | grep -i 'OpenGL renderer' || echo '-'", shell=True))
        add("Драйверы Intel/Mesa DRI", self._run(
            "D=$(ls /usr/lib/x86_64-linux-gnu/dri /usr/lib64/dri 2>/dev/null | "
            "grep -iE 'i965|iris|crocus|swrast' | sort -u | tr '\\n' ' '); "
            "echo \"${D:-НЕ НАЙДЕНЫ — установите libgl1-mesa-dri}\"", shell=True))
        add("Vulkan", self._run(
            "vulkaninfo --summary 2>/dev/null | grep -i deviceName "
            "|| echo '(vulkaninfo нет)'", shell=True))

        section("БРАУЗЕР И ВХОД В ROBLOX")
        add("Браузер по умолчанию", self._run(
            "B=$(xdg-settings get default-web-browser 2>/dev/null); echo \"${B:-НЕ ЗАДАН}\"",
            shell=True))
        add("Обработчик roblox-studio-auth", self._run(
            "H=$(xdg-mime query default x-scheme-handler/roblox-studio-auth 2>/dev/null); "
            "echo \"${H:-НЕ ЗАДАН}\"", shell=True))
        add("Установленные браузеры", self._run(
            "L=$(ls /usr/share/applications 2>/dev/null | "
            "grep -iE 'chrom|firefox|yandex|browser' | tr '\\n' ' '); "
            "echo \"${L:-нет}\"", shell=True))

        section("FLATPAK")
        add("Версия flatpak", self._run(["flatpak", "--version"]))
        add("Репозитории", self._run(
            "flatpak remotes --columns=name,url 2>/dev/null | tr '\\n' '; ' || echo '-'",
            shell=True))
        add("Установлено", self._run(
            "flatpak list --columns=application,version 2>/dev/null | tr '\\n' '; ' || echo '-'",
            shell=True))

        section("VINEGAR / ROBLOX STUDIO")
        base = os.path.join(USER_HOME, ".var", "app", "org.vinegarhq.Vinegar")
        add("Папка Vinegar", base if os.path.isdir(base) else "(нет — не установлен)")
        add("Версии Studio", self._run(
            f"V=$(ls {shell_quote(base)}/data/vinegar/versions 2>/dev/null | tr '\\n' ' '); "
            "echo \"${V:-нет}\"", shell=True))
        add("WebView2 (окно входа)", self._run(
            f"W=$(find {shell_quote(base)}/data/vinegar -maxdepth 5 "
            "\\( -iname '*EBWebView*' -o -iname 'msedgewebview2.exe' "
            "-o -iname 'WebView2*' \\) 2>/dev/null | head -3 | tr '\\n' ' '); "
            "echo \"${W:-НЕ НАЙДЕН — это и есть причина пустого окна входа}\"",
            shell=True))
        cfg = os.path.join(base, "config", "vinegar", "config.toml")
        if os.path.exists(cfg):
            try:
                with open(cfg, encoding="utf-8", errors="replace") as f:
                    body = f.read().strip()
                lines.append("config.toml:")
                lines.append(body or "(пустой)")
            except OSError:
                add("config.toml", "(не прочитать)")
        else:
            add("config.toml", "(нет — настройки по умолчанию)")

        section("WINE / JAVA")
        wine = find_wine()
        add("Wine", f"{wine_version(wine)}  ({wine})" if wine else "не установлен")
        add("winetricks", str(winetricks_version(find_winetricks()) or "нет"))
        add("Окружения Wine", self._run(
            f"ls {shell_quote(WINE_ROOT)} 2>/dev/null | tr '\\n' ' ' || echo '-'",
            shell=True))
        java = find_java(need_gui=False)
        add("Java", f"{java} (окна: {'да' if java and java_has_gui(java) else 'НЕТ'})"
            if java else "не установлена")

        text = "\n".join(lines) + "\n"
        for ln in lines:
            self.sig_line.emit("   " + ln if ln else "", "info")

        path = ""
        try:
            _user_makedirs(REPORTS_DIR)
            path = os.path.join(REPORTS_DIR, f"otchet-{host}.txt")
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
            _chown_to_user(REPORTS_DIR)
            self.sig_line.emit(f"✓ Отчёт сохранён: {path}", "ok")
            self.sig_line.emit("   Снимите такой же на компьютере, где всё работает, "
                               "и сравните файлы — различие и будет причиной.", "info")
        except OSError as e:
            self.sig_line.emit(f"⚠ Не удалось сохранить файл отчёта: {e}", "warn")
        self.sig_done.emit(path)


# ---------------------------------------------------------------------------
# Плиточный экран для педагога
# ---------------------------------------------------------------------------

_TILE_COLORS = ["#4C6EF5", "#12B886", "#F76707", "#E64980", "#7048E8",
                "#1098AD", "#F59F00", "#37B24D", "#E03131", "#5C7CFA"]


def _avatar_pixmap(text, size=64):
    """Цветной кружок с буквами вместо иконки — резервный вариант, если для
    программы нет файла в icons/ (см. _app_icon_pixmap)."""
    color = QColor(_TILE_COLORS[sum(text.encode("utf-8")) % len(_TILE_COLORS)])
    pix = QPixmap(size, size)
    pix.fill(Qt.transparent)
    p = QPainter(pix)
    p.setRenderHint(QPainter.Antialiasing)
    p.setBrush(QBrush(color))
    p.setPen(Qt.NoPen)
    p.drawEllipse(0, 0, size - 1, size - 1)
    p.setPen(QPen(QColor("#ffffff")))
    font = QFont()
    font.setPointSize(int(size * 0.38))
    font.setBold(True)
    p.setFont(font)
    letters = "".join(w[0] for w in text.split()[:2]).upper() or "?"
    p.drawText(pix.rect(), Qt.AlignCenter, letters)
    p.end()
    return pix


_ICON_EXTS = (".png", ".svg", ".jpg", ".jpeg", ".webp")


def _app_icon_pixmap(app_id, name, size=64):
    """Иконка программы: файл icons/<id>.* если он есть, иначе цветной
    аватар с буквами. Файл может быть любого размера — вписываем в квадрат
    size×size с сохранением пропорций."""
    for ext in _ICON_EXTS:
        path = os.path.join(ICONS_DIR, app_id + ext)
        if os.path.exists(path):
            pix = QPixmap(path)
            if not pix.isNull():
                return pix.scaled(size, size, Qt.KeepAspectRatio,
                                  Qt.SmoothTransformation)
    return _avatar_pixmap(name, size)


class AppTile(QFrame):
    """Одна плитка программы: аватар, название, статус. Клик — установить
    или запустить, в зависимости от текущего статуса."""

    clicked = pyqtSignal(str)

    TILE_SIZE = (148, 158)

    def __init__(self, app_id, name, installed, parent=None):
        super().__init__(parent)
        self.app_id = app_id
        self.setFixedSize(*self.TILE_SIZE)
        self.setCursor(Qt.PointingHandCursor)
        self.setObjectName("tile")
        self.setStyleSheet(
            "QFrame#tile { border: 1px solid #333; border-radius: 12px;"
            " background: #1c1e22; }"
            "QFrame#tile:hover { border: 1px solid #4C6EF5; background: #22252b; }")
        lay = QVBoxLayout(self)
        lay.setAlignment(Qt.AlignHCenter)
        lay.setContentsMargins(8, 14, 8, 10)
        icon_label = QLabel()
        icon_label.setPixmap(_app_icon_pixmap(app_id, name, 56))
        icon_label.setAlignment(Qt.AlignCenter)
        lay.addWidget(icon_label)
        lay.addSpacing(8)
        name_label = QLabel(name)
        name_label.setWordWrap(True)
        name_label.setAlignment(Qt.AlignCenter)
        name_label.setStyleSheet("color:#eee; font-weight:600; font-size:12px; border:none;")
        lay.addWidget(name_label)
        self.status_label = QLabel()
        self.status_label.setAlignment(Qt.AlignCenter)
        self.status_label.setStyleSheet("border:none;")
        lay.addWidget(self.status_label)
        self.set_installed(installed)

    def set_installed(self, installed, busy=False):
        self.installed = installed
        if busy:
            self.status_label.setText("⏳ устанавливается…")
            self.status_label.setStyleSheet("color:#F59F00; font-size:11px; border:none;")
        elif installed:
            self.status_label.setText("● установлено")
            self.status_label.setStyleSheet("color:#4EC94E; font-size:11px; border:none;")
        else:
            self.status_label.setText("○ не установлено")
            self.status_label.setStyleSheet("color:#999; font-size:11px; border:none;")

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.clicked.emit(self.app_id)
        super().mousePressEvent(event)


class CourseSelectDialog(QDialog):
    """Список курсов с галочками — для установки всех программ выбранных
    курсов одной кнопкой."""

    def __init__(self, courses, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Выбор курсов")
        self.resize(440, 420)
        lay = QVBoxLayout(self)
        hint = QLabel("Отметьте курсы — установятся все программы из них "
                      "(уже установленные пропускаются).")
        hint.setWordWrap(True)
        lay.addWidget(hint)
        self.list = QListWidget()
        for c in courses:
            n = len(c.get("app_ids") or [])
            item = QListWidgetItem(f"{c['name']}  ({n})")
            item.setFlags(item.flags() | Qt.ItemIsUserCheckable)
            item.setCheckState(Qt.Unchecked)
            item.setData(Qt.UserRole, c["id"])
            self.list.addItem(item)
        lay.addWidget(self.list)
        btns = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        btns.button(QDialogButtonBox.Ok).setText("Установить отмеченные")
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        lay.addWidget(btns)

    def checked_course_ids(self):
        ids = []
        for i in range(self.list.count()):
            item = self.list.item(i)
            if item.checkState() == Qt.Checked:
                ids.append(item.data(Qt.UserRole))
        return ids


class LauncherWindow(QMainWindow):
    """То, что видит педагог: поиск сверху и плитки программ снизу —
    зелёная подпись «установлено», серая «не установлено».

    Клик по неустановленной плитке предлагает установить. Вся «тяжёлая»
    логика (установка, Wine, лог) не дублируется — ей заведует спрятанное
    окно администрирования (MainWindow), которое открывается только по
    кнопке ⚙ либо появляется на экране само, если что-то пошло не так."""

    def __init__(self):
        super().__init__()
        self.admin = MainWindow()
        self.setWindowTitle(self.admin.windowTitle())
        self.setWindowIcon(_koderlab_icon())
        self.resize(900, 640)
        self._tiles = {}
        self._busy_app = None
        self._batch_ids = []
        self._cols = 0
        self._build_ui()
        self._populate()

    # ---- интерфейс ----
    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)

        header = QHBoxLayout()
        title = QLabel(self.admin.courses.get("title") or "KoderLab")
        title.setStyleSheet("font-size:20px; font-weight:600;")
        header.addWidget(title)
        ver = QLabel(f"v{KODERLAB_VERSION}")
        ver.setStyleSheet("color:#888; font-size:12px;")
        header.addWidget(ver)
        header.addStretch()
        self.courses_btn = QPushButton("📚 Курсы…")
        self.courses_btn.setToolTip("Выбрать курсы и установить все программы из них разом")
        self.courses_btn.clicked.connect(self._pick_courses)
        header.addWidget(self.courses_btn)
        self.gear_btn = QToolButton()
        self.gear_btn.setText("⚙")
        self.gear_btn.setToolTip("Установка, переустановка, настройки Wine, журнал")
        self.gear_btn.setStyleSheet("font-size:18px; padding:4px 12px;")
        self.gear_btn.clicked.connect(self._open_admin)
        header.addWidget(self.gear_btn)
        layout.addLayout(header)

        self.search = QLineEdit()
        self.search.setPlaceholderText("Поиск: kodu, algodoo, scratch…")
        self.search.textChanged.connect(self._filter)
        layout.addWidget(self.search)

        prog_row = QHBoxLayout()
        self.status_label = QLabel("")
        self.status_label.setStyleSheet("color:#aaa; font-size:12px;")
        self.status_label.setVisible(False)
        prog_row.addWidget(self.status_label, stretch=1)
        self.progress = QProgressBar()
        self.progress.setMaximum(0)
        self.progress.setVisible(False)
        self.progress.setMaximumWidth(160)
        prog_row.addWidget(self.progress)
        self.op_cancel_btn = QPushButton("Отмена")
        self.op_cancel_btn.setVisible(False)
        self.op_cancel_btn.clicked.connect(lambda: self.admin._cancel())
        prog_row.addWidget(self.op_cancel_btn)
        layout.addLayout(prog_row)

        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.NoFrame)
        self.grid_host = QWidget()
        self.grid = QGridLayout(self.grid_host)
        self.grid.setSpacing(14)
        self.grid.setAlignment(Qt.AlignTop | Qt.AlignLeft)
        self.scroll.setWidget(self.grid_host)
        layout.addWidget(self.scroll, stretch=1)

    def _populate(self):
        self._tiles = {}
        self._tile_order = []
        # одна программа может входить в несколько курсов — плитка должна
        # быть одна, иначе сетка «расползается»: виджет нельзя показать
        # сразу в нескольких ячейках QGridLayout
        seen = set()
        for course in self.admin.courses.get("courses", []):
            for app in self.admin._course_apps(course):
                if app["id"] in seen:
                    continue
                if (app.get("installer") or "").lower() in ("unsupported", "none"):
                    continue
                seen.add(app["id"])
                tile = AppTile(app["id"], app["name"], is_app_installed(app),
                               parent=self.grid_host)
                tile.setToolTip(app["name"])
                tile.clicked.connect(self._on_tile_clicked)
                self._tiles[app["id"]] = tile
                self._tile_order.append(app["id"])
        self._relayout(force=True)

    def _columns_for_width(self, width):
        tile_w = AppTile.TILE_SIZE[0] + self.grid.spacing()
        return max(1, width // tile_w)

    def _relayout(self, force=False):
        cols = self._columns_for_width(self.scroll.viewport().width() or self.width())
        if cols == self._cols and not force:
            return
        self._cols = cols
        for aid in self._tile_order:
            self.grid.removeWidget(self._tiles[aid])
        row = col = 0
        for aid in self._tile_order:
            tile = self._tiles[aid]
            if not tile.isVisible() and self.search.text().strip():
                continue
            self.grid.addWidget(tile, row, col)
            col += 1
            if col >= cols:
                col = 0
                row += 1

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._relayout()

    # ---- поиск ----
    def _filter(self, text):
        text = (text or "").strip().lower()
        for aid, tile in self._tiles.items():
            app = self.admin._app_by_id(aid)
            name = (app["name"] if app else aid).lower()
            tile.setVisible(not text or text in name or text in aid.lower())
        self._relayout(force=True)

    # ---- клик по плитке ----
    def _on_tile_clicked(self, app_id):
        if self._busy_app:
            QMessageBox.information(
                self, "Занято", "Дождитесь окончания текущей установки.")
            return
        app = self.admin._app_by_id(app_id)
        if not app:
            return
        if is_app_installed(app):
            self._launch(app_id)
            return
        r = QMessageBox.question(
            self, "Установка",
            f"«{app['name']}» ещё не установлена.\n\nУстановить сейчас?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
        if r == QMessageBox.Yes:
            self._install(app_id)

    def _launch(self, app_id):
        self.admin._run_app(app_id)
        w = self.admin._launchers.get(app_id)
        if w:
            w.sig_done.connect(lambda code, aid=app_id: self._refresh_tile(aid))

    # ---- установка с лёгким индикатором прямо тут ----
    def _install(self, app_id):
        self._busy_app = app_id
        tile = self._tiles.get(app_id)
        if tile:
            tile.set_installed(False, busy=True)
        name = self.admin._app_by_id(app_id)["name"]
        self.status_label.setText(f"Устанавливаю «{name}»…")
        self.status_label.setVisible(True)
        self.progress.setVisible(True)
        self.op_cancel_btn.setVisible(True)
        self.admin._on_app_button(app_id)
        w = self.admin.worker
        if not (w and w.isRunning()):
            # установка не началась (например, отменили запрос подтверждения)
            self._op_reset()
            if tile:
                self._refresh_tile(app_id)
            return
        w.sig_line.connect(self._on_worker_line)
        w.sig_done.connect(lambda report, aid=app_id: self._on_install_done(aid, report))

    def _on_worker_line(self, text, kind):
        if kind in ("ok", "err", "warn") and text.strip():
            self.status_label.setText(text.strip())

    def _on_install_done(self, app_id, report):
        ok = (report or {}).get("error", 0) == 0
        self._op_reset()
        self._refresh_tile(app_id)
        if not ok:
            name = self.admin._app_by_id(app_id)["name"]
            QMessageBox.warning(
                self, "Не получилось",
                f"«{name}» не установилась.\n\n"
                "Подробности — в окне настроек (кнопка ⚙).")

    def _op_reset(self):
        self._busy_app = None
        self._batch_ids = []
        self.progress.setMaximum(0)
        self.progress.setVisible(False)
        self.status_label.setVisible(False)
        self.op_cancel_btn.setVisible(False)

    def _refresh_tile(self, app_id):
        app = self.admin._app_by_id(app_id)
        tile = self._tiles.get(app_id)
        if app and tile:
            tile.set_installed(is_app_installed(app))

    # ---- выбор курсов и установка всего разом ----
    def _pick_courses(self):
        if self._busy_app:
            QMessageBox.information(
                self, "Занято", "Дождитесь окончания текущей установки.")
            return
        dlg = CourseSelectDialog(self.admin.courses.get("courses", []), self)
        if dlg.exec_() != QDialog.Accepted:
            return
        wanted = set(dlg.checked_course_ids())
        if not wanted:
            return
        apps, seen = [], set()
        for course in self.admin.courses.get("courses", []):
            if course["id"] not in wanted:
                continue
            for app in self.admin._course_apps(course):
                if app["id"] in seen:
                    continue
                if (app.get("installer") or "").lower() in ("unsupported", "none"):
                    continue
                seen.add(app["id"])
                apps.append(app)
        if apps:
            self._install_batch(apps)

    def _install_batch(self, apps):
        self._busy_app = "*batch*"
        self._batch_ids = [a["id"] for a in apps]
        for aid in self._batch_ids:
            tile = self._tiles.get(aid)
            if tile and not tile.installed:
                tile.set_installed(False, busy=True)
        self.status_label.setText(f"Устанавливаю {len(apps)} программ…")
        self.status_label.setVisible(True)
        self.progress.setMaximum(len(apps))
        self.progress.setValue(0)
        self.progress.setVisible(True)
        self.op_cancel_btn.setVisible(True)
        self.admin._start(apps, "install")
        w = self.admin.worker
        if not (w and w.isRunning()):
            self._op_reset()
            for aid in self._batch_ids:
                self._refresh_tile(aid)
            return
        w.sig_line.connect(self._on_worker_line)
        w.sig_step.connect(self._on_batch_step)
        w.sig_done.connect(self._on_batch_done)

    def _on_batch_step(self, current, total, name):
        self.progress.setMaximum(total)
        self.progress.setValue(current - 1)
        self.status_label.setText(f"[{current}/{total}] {name}…")

    def _on_batch_done(self, report):
        ids = self._batch_ids
        self._op_reset()
        for aid in ids:
            self._refresh_tile(aid)
        report = report or {}
        msg = (f"Успешно: {report.get('success', 0)}    "
               f"Пропущено: {report.get('skipped', 0)}    "
               f"Ошибок: {report.get('error', 0)}")
        if report.get("error", 0):
            QMessageBox.warning(self, "Готово с ошибками",
                                msg + "\n\nПодробности — в окне настроек (кнопка ⚙).")
        else:
            QMessageBox.information(self, "Готово", msg)

    # ---- окно администратора по ⚙ ----
    def _open_admin(self):
        self.admin._refresh_statuses()
        self.admin.show()
        self.admin.raise_()
        self.admin.activateWindow()

    def showEvent(self, event):
        super().showEvent(event)
        for aid in list(self._tiles):
            self._refresh_tile(aid)

    def closeEvent(self, event):
        self.admin.close()
        super().closeEvent(event)


# ---------------------------------------------------------------------------
# Главное окно
# ---------------------------------------------------------------------------

class MainWindow(QMainWindow):
    # сервер раздачи работает в отдельном потоке, а трогать интерфейс можно
    # только из главного — поэтому сообщение о скачивании идёт через сигнал
    sig_share_download = pyqtSignal(str)   # "событие|IP"

    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"Установщик KoderLab — Linux ({DISTRO_NAME})")
        self.setWindowIcon(_koderlab_icon())
        self.resize(960, 740)
        self.worker = None
        self.action = "install"
        self._last_progress = False
        self._t0 = 0
        self._spin = 0
        self._step_text = ""
        self._rows = {}
        self._state = {}
        self._launchers = {}
        self._log_formats = {}
        self._log_has_text = False
        self._log_queue = []
        self._httpd = None
        self._share_worker = None
        self._recv_worker = None
        self._share_clients = set()
        self._share_active = set()
        self._sort_worker = None
        self._fp_worker = None
        self._report_worker = None
        self.courses = self._load_courses()
        # Упрощённый режим интерфейса: только список программ,
        # установка и запуск. Включается в courses.json:
        #   "ui": { "simple": true }
        self.simple = bool((self.courses.get("ui") or {}).get("simple"))
        # Упрощённый режим: только список программ, установка и запуск.
        # Включается в courses.json: "ui": {"simple": true}

        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick)
        self._log_timer = QTimer(self)
        self._log_timer.timeout.connect(self._flush_log)
        self.sig_share_download.connect(self._share_download_ui)

        if self.courses.get("title"):
            self.setWindowTitle(f"{self.courses['title']} — {DISTRO_NAME}")

        self._build_ui()
        self._populate_tree()
        self._refresh_statuses()
        self._refresh_root_status()
        QTimer.singleShot(300, self._warn_if_root)
        QTimer.singleShot(600, self._log_update_status)

    def _load_courses(self):
        with open(COURSES_FILE, encoding="utf-8") as f:
            return json.load(f)

    def _app_by_id(self, app_id):
        app = self.courses.get("apps", {}).get(app_id)
        if app is None:
            return None
        return dict(app, id=app_id)

    def _course_apps(self, course):
        apps = []
        for aid in course.get("app_ids", []):
            app = self._app_by_id(aid)
            if app:
                apps.append(app)
        return apps

    # ---- построение интерфейса ----
    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)

        header = QHBoxLayout()
        title = QLabel(self.courses.get("title") or "Установщик курсов KoderLab")
        title.setStyleSheet("font-size: 18px; font-weight: 500;")
        header.addWidget(title)
        self.total_label = QLabel("")
        self.total_label.setStyleSheet("color:#888; font-size:13px;")
        header.addWidget(self.total_label)
        header.addStretch()
        refresh_btn = QPushButton("⟳ Обновить статусы")
        refresh_btn.clicked.connect(self._refresh_statuses)
        header.addWidget(refresh_btn)
        help_btn = QPushButton("? Помощь")
        help_btn.clicked.connect(self._show_help)
        header.addWidget(help_btn)
        layout.addLayout(header)

        self.search = QLineEdit()
        self.search.setPlaceholderText("Поиск: blender, scratch, tux…")
        self.search.textChanged.connect(self._filter_tree)
        layout.addWidget(self.search)

        actions = QHBoxLayout()
        self.selected_btn = QPushButton("Установить отмеченные")
        self.selected_btn.clicked.connect(self._install_checked)
        actions.addWidget(self.selected_btn)
        bundle_btn = QPushButton("Установить всё")
        bundle_btn.clicked.connect(self._install_bundle)
        actions.addWidget(bundle_btn)
        course_btn = QPushButton("Установить всё по курсу")
        course_btn.clicked.connect(self._install_selected_course)
        actions.addWidget(course_btn)
        self.force_box = QCheckBox("Переустанавливать уже установленные")
        self.force_box.setToolTip(
            "По умолчанию установленные программы пропускаются: файлы не "
            "скачиваются заново, пакеты не переустанавливаются, окружения Wine "
            "не пересоздаются.\nВключите, если нужно поставить программу "
            "заново поверх — например, после сбоя.")
        actions.addWidget(self.force_box)
        clear_btn = QPushButton("Очистить лог")
        clear_btn.clicked.connect(self._clear_log)
        actions.addWidget(clear_btn)
        actions.addStretch()
        layout.addLayout(actions)

        # ── Панель «Администрирование» ──
        self.admin_toggle = QPushButton(
            "▸ Администрирование  —  Wine, flatpak, Java, раздача по сети, отчёт о ПК")
        self.admin_toggle.setStyleSheet(
            "text-align:left; border:1px solid #444; border-radius:4px;"
            "padding:5px; color:#bbb;")
        self.admin_toggle.setToolTip("Права root, раздача установщика по сети класса.")
        self.admin_toggle.clicked.connect(self._toggle_admin)
        layout.addWidget(self.admin_toggle)

        self.admin_box = QWidget()
        admin_layout = QVBoxLayout(self.admin_box)
        admin_layout.setContentsMargins(12, 0, 0, 0)
        self.admin_box.setVisible(False)
        layout.addWidget(self.admin_box)

        admin_row = QHBoxLayout()
        self.admin_label = QLabel("Права root: —")
        self.admin_label.setStyleSheet("color:#888; font-size:12px;")
        admin_row.addWidget(self.admin_label)
        self.root_btn = QPushButton("🔑 Перезапустить с правами root")
        self.root_btn.setToolTip("Один запрос пароля — дальше пакеты ставятся без "
                                 "повторных окон ввода пароля.")
        self.root_btn.clicked.connect(self._relaunch_root)
        admin_row.addWidget(self.root_btn)
        admin_row.addStretch()
        admin_layout.addLayout(admin_row)

        distro_row = QHBoxLayout()
        self.distro_label = QLabel(
            f"Система: {DISTRO_NAME}   •   пакеты: .{PKG_FAMILY}   •   "
            f"менеджер: {PKG_MANAGER or 'не найден'}")
        self.distro_label.setStyleSheet("color:#888; font-size:12px;")
        distro_row.addWidget(self.distro_label)
        distro_row.addStretch()
        admin_layout.addLayout(distro_row)

        net_row = QHBoxLayout()
        self.share_btn = QPushButton("📡 Раздать по сети")
        self.share_btn.setToolTip("Упаковать эту папку (courses.json + installers) "
                                  "и раздать другим ПК в локальной сети класса.")
        self.share_btn.clicked.connect(self._toggle_share)
        net_row.addWidget(self.share_btn)
        self.receive_btn = QPushButton("📥 Получить по сети")
        self.receive_btn.setToolTip("Скачать папку с компьютера, который раздаёт (по его IP).")
        self.receive_btn.clicked.connect(self._receive_share)
        net_row.addWidget(self.receive_btn)
        self.net_label = QLabel("")
        self.net_label.setStyleSheet("color:#888; font-size:12px;")
        net_row.addWidget(self.net_label)
        net_row.addStretch()
        admin_layout.addLayout(net_row)

        sort_row = QHBoxLayout()
        self.sort_btn = QPushButton("📂 Разложить установщики из папки…")
        self.sort_btn.setToolTip(
            "Выбрать папку со скачанными файлами (любые имена) — программа сама "
            "разложит их по installers/<id>/ по совпадению с названием программы."
        )
        self.sort_btn.clicked.connect(self._sort_downloads)
        sort_row.addWidget(self.sort_btn)
        self.gh_btn = QPushButton("🔎 Найти на GitHub и скачать…")
        self.gh_btn.setToolTip(
            "Выделите программу в списке — поиск по названию на GitHub, "
            "выбор нужного файла и загрузка сразу в installers/<id>/.")
        self.gh_btn.clicked.connect(self._github_search)
        sort_row.addWidget(self.gh_btn)
        self.wine_btn = QPushButton("🍷 Настройки Wine…")
        self.wine_btn.setToolTip("Окружения Windows-программ: winecfg, winetricks, "
                                 "версия Windows, компоненты, сброс.")
        self.wine_btn.clicked.connect(self._wine_settings)
        sort_row.addWidget(self.wine_btn)
        self.fp_btn = QPushButton("🩹 Починить flatpak")
        self.fp_btn.setToolTip(
            "Переустанавливает flatpak и libcurl и проверяет результат.\n"
            "Нужно, если в журнале была ошибка flatpak_create_http_session / CURLM.")
        self.fp_btn.clicked.connect(self._repair_flatpak)
        sort_row.addWidget(self.fp_btn)
        self.report_btn = QPushButton("🧾 Отчёт о компьютере")
        self.report_btn.setToolTip(
            "Собирает состояние ПК в один файл: графика, браузер по умолчанию, "
            "flatpak, Vinegar, WebView2, Wine, Java.\n"
            "Снимите отчёт там, где работает, и там, где нет — и сравните.")
        self.report_btn.clicked.connect(self._system_report)
        sort_row.addWidget(self.report_btn)
        sort_row.addStretch()
        admin_layout.addLayout(sort_row)

        if self.simple:
            # Упрощённый режим: по делу для Kodu/Algodoo — установка,
            # переустановка, настройки Wine, лог. Остальное (раздача по
            # сети, поиск на GitHub, починка flatpak, отчёт о ПК) — для
            # техника с целым каталогом курсов, здесь не нужно.
            for widget in (self.search, course_btn,
                           self.admin_label, self.root_btn, self.distro_label,
                           self.share_btn, self.receive_btn, self.net_label,
                           self.sort_btn, self.gh_btn, self.fp_btn,
                           self.report_btn):
                widget.setVisible(False)
            self.admin_toggle.setText("▸ ⚙ Настройки")
            self.admin_toggle.setToolTip("Настройки Wine, переустановка, лог.")

        self.tree = QTreeWidget()
        self.tree.setHeaderLabels(["Программа", "Статус и действия"])
        self.tree.setColumnWidth(0, 450)
        layout.addWidget(self.tree, stretch=2)

        status_row = QHBoxLayout()
        self.status_label = QLabel("Готов к работе")
        self.status_label.setStyleSheet("font-family: 'DejaVu Sans Mono', monospace;")
        status_row.addWidget(self.status_label)
        self.progress = QProgressBar()
        self.progress.setValue(0)
        status_row.addWidget(self.progress, stretch=1)
        self.cancel_btn = QPushButton("Отмена")
        self.cancel_btn.setEnabled(False)
        self.cancel_btn.clicked.connect(self._cancel)
        status_row.addWidget(self.cancel_btn)
        layout.addLayout(status_row)

        hline = QFrame()
        hline.setFrameShape(QFrame.HLine)
        layout.addWidget(hline)

        log_label = QLabel("Журнал:")
        log_label.setStyleSheet("color: #888; font-size: 12px;")
        layout.addWidget(log_label)

        self.log_panel = QTextEdit()
        self.log_panel.setReadOnly(True)
        self.log_panel.setLineWrapMode(QTextEdit.NoWrap)
        # Ограничение обязательно: Wine умеет сыпать десятки тысяч строк,
        # и без предела окно съедает всю память, а компьютер уходит в своп.
        # 0 — без ограничения: журнал хранит все строки целиком
        self.log_panel.document().setMaximumBlockCount(0)
        self.log_panel.setStyleSheet(
            "background: #14161a; color: #C8C8C8;"
            "font-family: 'DejaVu Sans Mono', 'Liberation Mono', monospace; font-size: 12px;"
            "border: 1px solid #333; padding: 6px;"
        )
        layout.addWidget(self.log_panel, stretch=3)

    def _populate_tree(self):
        for course in self.courses["courses"]:
            c_item = QTreeWidgetItem(self.tree, [course["name"]])
            if course.get("note"):
                c_item.setToolTip(0, course["note"])
            c_item.setFlags(c_item.flags() | Qt.ItemIsUserCheckable)
            c_item.setCheckState(0, Qt.Unchecked)
            c_item.setData(0, Qt.UserRole, {"type": "course", "id": course["id"]})
            for app in self._course_apps(course):
                label = app["name"]
                unsupported = (app.get("installer") or "").lower() in ("unsupported", "none")
                if unsupported:
                    label += "  (нет версии для Linux)"
                a_item = QTreeWidgetItem(c_item, [label])
                a_item.setToolTip(0, app.get("note", ""))
                a_item.setData(0, Qt.UserRole, {"type": "app", "id": app["id"]})

                row = QWidget()
                h = QHBoxLayout(row)
                h.setContentsMargins(4, 2, 4, 2)
                status = QLabel()
                status.setMinimumWidth(150)
                btn = QPushButton()
                btn.setMinimumWidth(110)
                btn.clicked.connect(lambda _, aid=app["id"]: self._on_app_button(aid))
                h.addWidget(status)
                h.addStretch()
                tools = app.get("tools") or []
                if tools:
                    tool_btn = QPushButton("⚙")
                    tool_btn.setMaximumWidth(34)
                    tool_btn.setToolTip(
                        "Настройки программы: "
                        + "; ".join(t.get("name", "инструмент") for t in tools))
                    tool_btn.clicked.connect(
                        lambda _, aid=app["id"]: self._run_tool(aid))
                    h.addWidget(tool_btn)
                gh = QPushButton("🔎")
                gh.setVisible(not self.simple)
                gh.setMaximumWidth(34)
                gh.setToolTip("Найти эту программу на GitHub и скачать файл "
                              "в папку установщика")
                gh.clicked.connect(lambda _, aid=app["id"]: self._github_search(aid))
                h.addWidget(gh)
                run_btn = QPushButton("▶ Запустить")
                run_btn.setMinimumWidth(100)
                run_btn.clicked.connect(lambda _, aid=app["id"]: self._run_app(aid))
                h.addWidget(run_btn)
                h.addWidget(btn)
                if unsupported:
                    btn.setEnabled(False)
                    run_btn.setEnabled(False)
                    gh.setEnabled(False)
                self.tree.setItemWidget(a_item, 1, row)
                # одна и та же программа может быть в нескольких курсах —
                # запоминаем все её строки, иначе статус обновится только в одной
                self._rows.setdefault(app["id"], []).append(
                    {"status": status, "button": btn, "run": run_btn,
                     "item": a_item, "unsupported": unsupported})
            c_item.setExpanded(True)
        self.tree.itemChanged.connect(self._on_item_changed)

    def _on_item_changed(self, item, column):
        if column != 0:
            return
        data = item.data(0, Qt.UserRole)
        if not data or data["type"] != "course":
            self._update_selected_btn()
            return
        self.tree.blockSignals(True)
        state = item.checkState(0)
        for i in range(item.childCount()):
            item.child(i).setCheckState(0, state)
        self.tree.blockSignals(False)
        self._update_selected_btn()

    def _checked_apps(self):
        apps = []
        seen = set()
        root = self.tree.invisibleRootItem()
        for i in range(root.childCount()):
            c = root.child(i)
            for j in range(c.childCount()):
                a = c.child(j)
                if a.checkState(0) == Qt.Checked and not a.isHidden():
                    d = a.data(0, Qt.UserRole)
                    if d["id"] in seen:
                        continue
                    app = self._app_by_id(d["id"])
                    if app:
                        seen.add(d["id"])
                        apps.append(app)
        return apps

    def _update_selected_btn(self):
        n = len(self._checked_apps())
        self.selected_btn.setText(f"Установить отмеченные ({n})" if n else "Установить отмеченные")
        self.selected_btn.setEnabled(n > 0)

    def _install_checked(self):
        apps = self._checked_apps()
        if not apps:
            QMessageBox.information(self, "Ничего не отмечено",
                                    "Отметьте галочками приложения или курс в списке.")
            return
        apps = self._pending(apps)
        if not apps:
            QMessageBox.information(self, "Всё уже установлено",
                                    "Все отмеченные программы уже установлены.\n\n"
                                    "Чтобы поставить заново, включите галочку "
                                    "«Переустанавливать уже установленные».")
            return
        self._start(apps, "install")

    def _filter_tree(self, text):
        q = text.strip().lower()
        root = self.tree.invisibleRootItem()
        for i in range(root.childCount()):
            c = root.child(i)
            visible_children = 0
            for j in range(c.childCount()):
                a = c.child(j)
                name = a.text(0).lower()
                match = (not q) or (q in name) or (q in c.text(0).lower())
                a.setHidden(not match)
                visible_children += int(match)
            c.setHidden(visible_children == 0)
            if q:
                c.setExpanded(True)
        self._update_selected_btn()

    def _refresh_statuses(self):
        self.tree.blockSignals(True)
        total_installed = 0
        state = {}   # проверяем каждую программу один раз, а не по разу на курс
        for aid, rows in self._rows.items():
            app = self._app_by_id(aid)
            unsupported = rows[0].get("unsupported")
            installed = False if unsupported else is_app_installed(app)
            state[aid] = installed
            if not unsupported:
                total_installed += int(installed)
            running = aid in self._launchers and self._launchers[aid].isRunning()
            for row in rows:
                row["run"].setText("⏹ Остановить" if running else "▶ Запустить")
                if unsupported:
                    row["status"].setText("— нет для Linux")
                    row["status"].setStyleSheet("color:#777;")
                    row["button"].setText("Недоступно")
                elif installed:
                    row["status"].setText("● установлено")
                    row["status"].setStyleSheet("color:#4EC94E;")
                    row["button"].setText("Удалить")
                else:
                    row["status"].setText("○ не установлено")
                    row["status"].setStyleSheet("color:#999;")
                    row["button"].setText("Установить")
        self._state = state
        root = self.tree.invisibleRootItem()
        for i in range(root.childCount()):
            c_item = root.child(i)
            d = c_item.data(0, Qt.UserRole)
            course = next((c for c in self.courses["courses"] if c["id"] == d["id"]), None)
            if not course:
                continue
            c_apps = [a for a in self._course_apps(course)
                      if (a.get("installer") or "").lower() not in ("unsupported", "none")]
            done = sum(1 for a in c_apps if state.get(a["id"], False))
            c_item.setText(0, f"{course['name']}  ({done}/{len(c_apps)})")
        self.tree.blockSignals(False)
        supported = sum(1 for rows in self._rows.values() if not rows[0].get("unsupported"))
        self.total_label.setText(f"установлено {total_installed} из {supported}")
        self._update_selected_btn()

    # ---- лог ----
    def _clear_log(self):
        self._log_queue = []
        self.log_panel.clear()
        self._log_has_text = False
        self._last_progress = False

    def _scroll(self):
        sb = self.log_panel.verticalScrollBar()
        sb.setValue(sb.maximum())

    def log(self, text, kind="info"):
        """Кладёт строку в очередь на вывод.

        Строки не пишутся в окно по одной: при потоке вывода от Wine это
        занимало миллисекунды на строку, интерфейс переставал отвечать, и
        подвисал весь компьютер. Вместо этого очередь выгружается пачкой
        несколько раз в секунду — одна вставка на всю пачку."""
        ts = datetime.now().strftime("%H:%M:%S")
        self._log_queue.append((kind, text if text == "" else f"[{ts}] {text}"))
        self._last_progress = False
        # длинную очередь не копим: окно всё равно хранит ограниченное число строк
        if len(self._log_queue) > 4000:
            del self._log_queue[:len(self._log_queue) - 4000]
        if not self._log_timer.isActive():
            self._log_timer.start(100)

    def _flush_log(self):
        """Выгружает накопленные строки в окно одной вставкой на цвет."""
        if not self._log_queue:
            self._log_timer.stop()
            return
        batch, self._log_queue = self._log_queue, []

        cur = self.log_panel.textCursor()
        cur.movePosition(QTextCursor.End)
        group_kind, group = batch[0][0], []

        def put(kind, lines):
            if not lines:
                return
            fmt = self._log_formats.get(kind)
            if fmt is None:
                fmt = QTextCharFormat()
                fmt.setForeground(QColor(LOG_COLORS.get(kind,
                                                        LOG_COLORS["info"])))
                self._log_formats[kind] = fmt
            cur.setCharFormat(fmt)
            prefix = "\n" if self._log_has_text else ""
            cur.insertText(prefix + "\n".join(lines))
            self._log_has_text = True

        for kind, line_text in batch:
            if kind != group_kind:
                put(group_kind, group)
                group_kind, group = kind, []
            group.append(line_text)
        put(group_kind, group)
        self._scroll()

    def log_progress(self, text):
        if self._log_queue:
            self._flush_log()
        cur = self.log_panel.textCursor()
        cur.movePosition(QTextCursor.End)
        if self._last_progress:
            cur.movePosition(QTextCursor.StartOfBlock, QTextCursor.KeepAnchor)
            cur.removeSelectedText()
        elif self.log_panel.toPlainText():
            cur.insertText("\n")
        fmt = QTextCharFormat()
        fmt.setForeground(QColor(LOG_COLORS["run"]))
        cur.setCharFormat(fmt)
        ts = datetime.now().strftime("%H:%M:%S")
        cur.insertText(f"[{ts}] {text}")
        self._last_progress = True
        self._scroll()

    def _tick(self):
        if not (self.worker and self.worker.isRunning()):
            return
        self._spin = (self._spin + 1) % len(SPINNER)
        el = int(time.time() - self._t0)
        self.status_label.setText(f"{SPINNER[self._spin]}  {self._step_text}  —  {el} с")

    # ---- запуск операций ----
    def _install_bundle(self):
        apps = [a for a in (self._app_by_id(x) for x in self.courses.get("koderlab_bundle", []))
                if a and (a.get("installer") or "").lower() not in ("unsupported", "none")]
        apps = self._pending(apps)
        if not apps:
            QMessageBox.information(self, "Всё уже установлено",
                                    "Базовый набор KoderLab уже стоит целиком.")
            return
        self._start(apps, "install")

    def _install_selected_course(self):
        root = self.tree.invisibleRootItem()
        for i in range(root.childCount()):
            c_item = root.child(i)
            data = c_item.data(0, Qt.UserRole)
            if data["type"] == "course" and c_item.checkState(0) == Qt.Checked:
                course = next(c for c in self.courses["courses"] if c["id"] == data["id"])
                apps = [a for a in self._course_apps(course)
                        if (a.get("installer") or "").lower() not in ("unsupported", "none")]
                total = len(apps)
                apps = self._pending(apps)
                if not apps:
                    QMessageBox.information(
                        self, "Курс уже готов",
                        f"Все {total} программ курса «{course['name']}» "
                        "уже установлены.")
                    return
                self._start(apps, "install")
                return
        QMessageBox.information(self, "Выбор курса",
                                "Отметьте галочкой курс в дереве, затем нажмите кнопку.")

    def _on_app_button(self, app_id):
        app = self._app_by_id(app_id)
        action = "uninstall" if is_app_installed(app) else "install"
        self._start([app], action)

    def _pending(self, apps):
        """Отсеивает уже установленное и сообщает об этом в журнале."""
        if self.force_box.isChecked():
            return apps
        todo, done = [], []
        for app in apps:
            try:
                (done if is_app_installed(app) else todo).append(app)
            except Exception:
                todo.append(app)
        if done:
            self.log(f"○ Уже установлено, пропускаю ({len(done)}): "
                     + ", ".join(a["name"] for a in done), "ok")
        return todo

    def _run_app(self, app_id):
        """Запуск программы прямо из окна: весь её вывод и ошибки идут
        в журнал, повторное нажатие останавливает программу."""
        if app_id in self._launchers:
            w = self._launchers[app_id]
            if w.isRunning():
                r = QMessageBox.question(
                    self, "Программа уже запущена",
                    f"«{self._app_by_id(app_id)['name']}» уже работает.\n"
                    "Остановить её?",
                    QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
                if r == QMessageBox.Yes:
                    w.stop()
                return
        app = self._app_by_id(app_id)
        if not app:
            return
        tool_key = f"{app_id}::tool"
        tool_running = self._launchers.get(tool_key)
        if tool_running and tool_running.isRunning():
            r = QMessageBox.question(
                self, "Открыты настройки",
                f"Сейчас работает окно настроек «{app['name']}».\n\n"
                "Запуск программы поверх него может прервать работу.\n\n"
                "Закрыть настройки и запустить программу?",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
            if r != QMessageBox.Yes:
                return
            tool_running.stop()
            tool_running.wait(5000)
        self.log("", "info")
        self.log(f"───── Запуск: {app['name']} ─────", "run")
        w = LaunchWorker(app)
        w.sig_line.connect(self.log)
        w.sig_started.connect(self._on_launch_started)
        w.sig_done.connect(self._on_launch_done)
        self._launchers[app_id] = w
        w.start()

    def _run_tool(self, app_id):
        """Запуск вспомогательной программы: конфигуратора, настройщика графики
        и т.п. Для слабых компьютеров это главный способ сделать программу
        играбельной, поэтому кнопка вынесена прямо в строку."""
        app = self._app_by_id(app_id)
        tools = (app or {}).get("tools") or []
        if not tools:
            return
        tool = tools[0]
        if len(tools) > 1:
            name, ok = QInputDialog.getItem(
                self, f"Настройки — {app['name']}", "Что открыть:",
                [t.get("name", "инструмент") for t in tools], 0, False)
            if not ok:
                return
            tool = next(t for t in tools if t.get("name") == name)

        # Vinegar и подобные обёртки при новом запуске убивают предыдущий
        # экземпляр. Если программа уже работает, тихо запускать инструмент
        # рядом нельзя — оборвётся то, что человек делает в программе
        # (например, вход в аккаунт Roblox).
        if tool.get("conflicts_with_running", True):
            running = self._launchers.get(app_id)
            if running and running.isRunning():
                r = QMessageBox.question(
                    self, "Программа сейчас работает",
                    f"«{app['name']}» уже запущена.\n\n"
                    "Запускать что-то ещё поверх неё опасно: обёртка Vinegar "
                    "при новом запуске завершает предыдущий экземпляр — "
                    "именно из-за этого срывается вход в аккаунт.\n\n"
                    "Сначала закрыть работающую программу?",
                    QMessageBox.Yes | QMessageBox.No | QMessageBox.Cancel,
                    QMessageBox.Yes)
                if r == QMessageBox.Cancel:
                    return
                if r == QMessageBox.Yes:
                    running.stop()
                    running.wait(5000)

        # инструмент-действие: открывает нужное окно установщика
        if tool.get("action") == "wine_trial":
            wine_apps = {}
            for a_id in self.courses.get("apps", {}):
                a = self._app_by_id(a_id)
                if (a.get("installer") or "").lower() == "wine" or a.get("wine_arch"):
                    wine_apps[a_id] = a
            dlg = WineSettingsDialog(wine_apps, self)
            # сразу выбираем нужную программу и запускаем подбор
            for i in range(dlg.app_list.count()):
                if dlg.app_list.item(i).data(Qt.UserRole) == app_id:
                    dlg.app_list.setCurrentRow(i)
                    break
            QTimer.singleShot(200, dlg._trial_wine)
            dlg.exec_()
            self._refresh_statuses()
            return

        if tool.get("action") == "wine_restore":
            self.log("", "info")
            self.log(f"───── Возврат рабочих настроек: {app['name']} ─────", "run")
            if restore_working_config(app_id, self.log):
                self.log("   Запустите программу — должна открыться как "
                         "раньше.", "info")
            else:
                self.log("   Сохранённой рабочей настройки нет: она "
                         "появляется после первого удачного запуска.", "warn")
            self._refresh_statuses()
            return

        if tool.get("action") == "wine_settings":
            wine_apps = {}
            for a_id in self.courses.get("apps", {}):
                a = self._app_by_id(a_id)
                if (a.get("installer") or "").lower() == "wine" or a.get("wine_arch"):
                    wine_apps[a_id] = a
            dlg = WineSettingsDialog(wine_apps, self)
            for i in range(dlg.app_list.count()):
                if dlg.app_list.item(i).data(Qt.UserRole) == app_id:
                    dlg.app_list.setCurrentRow(i)
                    break
            dlg.exec_()
            self._refresh_statuses()
            return

        # инструмент-редактор: правим файл настроек прямо здесь
        if tool.get("edit_file"):
            tmpl = VINEGAR_CONFIG_TEMPLATE if tool.get("template") == "vinegar" else ""
            ConfigEditorDialog(tool.get("name", "Настройки"),
                               tool["edit_file"].replace("~", USER_HOME, 1),
                               template=tmpl, hint=tool.get("hint", ""),
                               parent=self).exec_()
            return

        # инструмент-команда: запускаем как есть
        if tool_is_command(tool):
            self.log("", "info")
            self.log(f"───── {tool.get('name', 'Настройки')}: {app['name']} ─────", "run")
            if tool.get("hint"):
                self.log("   " + tool["hint"], "info")
            key = f"{app_id}::tool"
            cmd = [os.path.expanduser(c.replace("~", USER_HOME, 1))
                   if isinstance(c, str) and c.startswith("~") else c
                   for c in tool["cmd"]]
            w = LaunchWorker({"id": key, "name": tool.get("name", "Настройки")},
                             cmd=cmd)
            w.sig_line.connect(self.log)
            w.sig_done.connect(lambda *_: self._launchers.pop(key, None))
            self._launchers[key] = w
            w.start()
            return

        path = find_app_tool(app, tool)
        if not path:
            prefix = wine_prefix(app_id)
            start = os.path.join(prefix, "drive_c")
            if not os.path.isdir(start):
                QMessageBox.information(
                    self, "Программа не установлена",
                    f"«{app['name']}» ещё не установлена, поэтому и настраивать "
                    "нечего.")
                return
            r = QMessageBox.question(
                self, "Файл не найден",
                f"Не нашёл «{tool.get('name', 'инструмент')}» автоматически.\n\n"
                "В разных версиях он называется по-разному. Указать файл "
                "вручную?\n\nОбычно он лежит рядом с самой программой и в "
                "названии есть Config или Setup.",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
            if r != QMessageBox.Yes:
                return
            path, _ = QFileDialog.getOpenFileName(
                self, "Выберите файл настроек", start, "Программы (*.exe *)")
            if not path:
                return

        cmd, cwd, env = app_tool_command(app, path)
        if not cmd:
            QMessageBox.warning(self, "Нет Wine",
                                "Для запуска нужен Wine, а он не найден.")
            return
        self.log("", "info")
        self.log(f"───── {tool.get('name', 'Настройки')}: {app['name']} ─────", "run")
        if tool.get("hint"):
            self.log("   " + tool["hint"], "info")
        key = f"{app_id}::tool"
        w = LaunchWorker({"id": key, "name": tool.get("name", "Настройки")},
                         cmd=cmd, cwd=cwd, env=env)
        w.sig_line.connect(self.log)
        w.sig_done.connect(lambda *_: self._launchers.pop(key, None))
        self._launchers[key] = w
        w.start()

    def _set_run_buttons(self, app_id, text, enabled=True):
        for row in self._rows.get(app_id, []):
            row["run"].setText(text)
            row["run"].setEnabled(enabled)

    def _on_launch_started(self, app_id):
        self._set_run_buttons(app_id, "⏹ Остановить")
        self.status_label.setText(f"Работает: {self._app_by_id(app_id)['name']}")

    def _on_launch_done(self, app_id, code):
        self._set_run_buttons(app_id, "▶ Запустить")
        self._launchers.pop(app_id, None)
        self.status_label.setText("Готов к работе")

    def _start(self, apps, action):
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Операция уже идёт.")
            return

        if action == "install":
            confirmed = []
            for app in apps:
                if app.get("warn"):
                    r = QMessageBox.warning(
                        self, "Внимание", app["warn"],
                        QMessageBox.Yes | QMessageBox.No, QMessageBox.No,
                    )
                    if r != QMessageBox.Yes:
                        self.log(f"⚠ {app['name']}: пропущено пользователем", "warn")
                        continue
                confirmed.append(app)
            apps = confirmed
            if apps and not is_root() and self._needs_root(apps) and not shutil.which("pkexec") \
                    and not shutil.which("sudo"):
                QMessageBox.warning(
                    self, "Нужны права root",
                    "Для установки системных пакетов нужны права root, но в системе "
                    "не найдены ни pkexec, ни sudo.\n\nЗапустите программу так:\n"
                    "sudo python3 main.py")
        else:
            names = "\n".join("• " + a["name"] for a in apps)
            r = QMessageBox.question(
                self, "Удаление", f"Удалить следующее?\n\n{names}",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No,
            )
            if r != QMessageBox.Yes:
                return
        if not apps:
            return
        self._launch(apps, action)

    @staticmethod
    def _needs_root(apps):
        return any((a.get("installer") or "").lower() in ("repo", "rpm", "deb", "script")
                   or (a.get("file", "").lower().endswith((".rpm", ".deb")))
                   for a in apps)

    def _launch(self, apps, action):
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Операция уже идёт.")
            return
        self.action = action
        self.progress.setValue(0)
        self.progress.setMaximum(max(1, len(apps)))
        self.cancel_btn.setEnabled(True)
        self._t0 = time.time()
        self._step_text = "подготовка…"
        self.timer.start(120)
        verb = {"install": "установки", "uninstall": "удаления", "run": "запуска"}.get(action, "операции")
        self.log(f"═══ Запуск {verb} ═══", "run")

        force = self.action == "install" and self.force_box.isChecked()
        self.worker = OpWorker(apps, action, force=force)
        self.worker.sig_line.connect(self.log)
        self.worker.sig_progress.connect(self.log_progress)
        self.worker.sig_step.connect(self._on_step)
        self.worker.sig_done.connect(self._on_finished)
        self.worker.start()

    def _toggle_admin(self):
        show = not self.admin_box.isVisible()
        self.admin_box.setVisible(show)
        if self.simple:
            self.admin_toggle.setText("▾ ⚙ Настройки" if show else "▸ ⚙ Настройки")
        else:
            self.admin_toggle.setText(
                "▾ Администрирование" if show else
                "▸ Администрирование  —  Wine, flatpak, Java, раздача по сети, отчёт о ПК")

    def _warn_if_root(self):
        """Под root Wine отказывается работать с префиксом пользователя, а
        браузеры на Chromium не запускаются вовсе. Предупреждаем сразу."""
        if not is_root():
            return
        user, _home = real_user()
        if user:
            self.log(f"⚠ Установщик запущен от имени root. Wine, flatpak и запуск "
                     f"программ будут выполняться от пользователя {user} — это "
                     "правильно и ничего делать не нужно.", "warn")
            return
        self.log("⚠ Установщик запущен от root, и определить обычного пользователя "
                 "не удалось.", "err")
        self.log("   Из-за этого НЕ БУДУТ работать: Wine («is not owned by you»), "
                 "запуск браузерных программ (Chromium не стартует под root), "
                 "а файлы окажутся в /root вместо домашней папки ученика.", "err")
        self.log("   Закройте окно и запустите обычным пользователем: ./start.sh — "
                 "пароль будет запрошен только при установке системных пакетов.", "warn")
        QMessageBox.warning(
            self, "Запущено под root",
            "Установщик работает от имени root, но определить обычного "
            "пользователя не удалось.\n\n"
            "Wine в таком режиме не запускает программы, а браузерные "
            "приложения не открываются.\n\n"
            "Закройте окно и запустите так:\n    ./start.sh\n\n"
            "Пароль администратора будет запрошен сам — только тогда, когда "
            "он реально нужен.")

    def _log_update_status(self):
        """Пишет в журнал, проверялось ли обновление и чего не хватает —
        чтобы не гадать, почему автообновление молчит."""
        self.log("", "info")
        self.log("═══ Автообновление ═══", "run")
        check_for_update(line=self.log)

    def _refresh_root_status(self):
        if is_root():
            user, _home = real_user()
            if user:
                self.admin_label.setText(
                    f"Права root: есть ✓ (программы запускаются от «{user}»)")
                self.admin_label.setStyleSheet("color:#4EC94E; font-size:12px;")
            else:
                self.admin_label.setText(
                    "Права root: есть, но пользователь не определён — Wine и "
                    "браузерные программы работать не будут!")
                self.admin_label.setStyleSheet("color:#FF6B6B; font-size:12px;")
            self.root_btn.setEnabled(False)
        else:
            self.admin_label.setText("Права root: нет — пароль спросят при установке пакетов")
            self.admin_label.setStyleSheet("color:#FFC24B; font-size:12px;")
            self.root_btn.setEnabled(bool(shutil.which("pkexec")))

    def _relaunch_root(self):
        r = QMessageBox.question(
            self, "Перезапуск с правами root",
            "Программа перезапустится и попросит пароль администратора один раз.\n"
            "Текущее окно закроется. Продолжить?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if r != QMessageBox.Yes:
            return
        if relaunch_as_root():
            self._stop_share()
            QApplication.quit()
        else:
            QMessageBox.warning(self, "Не получилось",
                                "Не удалось перезапустить через pkexec. "
                                "Запустите из терминала: sudo python3 main.py")

    # ---- передача по локальной сети ----
    def _toggle_share(self):
        if self._httpd:
            self._stop_share()
            return
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Дождитесь окончания операции.")
            return
        self.share_btn.setEnabled(False)
        self.log("═══ Подготовка раздачи по сети ═══", "run")
        self._share_worker = ShareZipWorker(BASE_DIR)
        self._share_worker.sig_line.connect(self.log)
        self._share_worker.sig_progress.connect(self.log_progress)
        self._share_worker.sig_done.connect(self._on_zip_ready)
        self._share_worker.start()

    def _on_zip_ready(self, zip_path):
        self.share_btn.setEnabled(True)
        if not zip_path:
            return
        directory = os.path.dirname(zip_path)
        self._share_clients = set()
        self._share_active = set()
        _QuietHandler.on_download = self._on_share_download
        try:
            handler = functools.partial(_QuietHandler, directory=directory)
            self._httpd = _ShareServer(("", SHARE_PORT), handler)
            threading.Thread(target=self._httpd.serve_forever, daemon=True).start()
        except OSError as e:
            self.log(f"✗ Не удалось запустить сервер (порт {SHARE_PORT} занят?): {e}", "err")
            self._httpd = None
            return
        ip = lan_ip()
        url = f"http://{ip}:{SHARE_PORT}/koderlab-share.zip"
        self.share_btn.setText("⏹ Остановить раздачу")
        self.net_label.setText(f"Раздаётся с IP {ip}")
        self.net_label.setStyleSheet("color:#4EC94E; font-size:12px;")
        self.log(f"✓ Раздача идёт. На других ПК нажмите «📥 Получить по сети» "
                 f"и введите IP: {ip}", "ok")
        self.log(f"   Либо откройте в браузере: {url}", "info")
        self.log("   Если не соединяется — на этом ПК разрешите порт 8765 "
                 "(firewall-cmd --add-port=8765/tcp или iptables).", "info")
        self.log(f"   Раздаётся только файл koderlab-share.zip из папки {directory} — "
                 "остальные ваши файлы по сети не видны.", "info")

    def _on_share_download(self, ip, path, event="start"):
        """Вызывается ИЗ ПОТОКА СЕРВЕРА — только шлём сигнал, ничего не рисуем."""
        self.sig_share_download.emit(f"{event}|{ip}")

    def _share_download_ui(self, payload):
        event, _, ip = payload.partition("|")
        if event == "start":
            self._share_active.add(ip)
            self.log(f"↓ {ip}: началась загрузка", "run")
        elif event == "done":
            self._share_active.discard(ip)
            self._share_clients.add(ip)
            self.log(f"✓ {ip}: архив получен полностью", "ok")
        else:
            self._share_active.discard(ip)
            self.log(f"⚠ {ip}: загрузка оборвалась. Пусть повторит — "
                     "скачивание продолжится с того же места.", "warn")
        self.net_label.setText(
            f"Раздаётся с IP {lan_ip()} — забрали: {len(self._share_clients)}"
            + (f", качают сейчас: {len(self._share_active)}"
               if self._share_active else ""))

    def _stop_share(self):
        _QuietHandler.on_download = None
        if self._httpd:
            try:
                self._httpd.shutdown()
                self._httpd.server_close()
            except OSError:
                pass
            self._httpd = None
            self.log("→ Раздача остановлена", "warn")
        self.share_btn.setText("📡 Раздать по сети")
        self.net_label.setText("")

    def _receive_share(self):
        ip, ok = QInputDialog.getText(
            self, "Получить по сети",
            "IP компьютера, который раздаёт\n(смотрите надпись «Раздаётся с IP …» на нём):")
        if not ok or not ip.strip():
            return
        url = f"http://{ip.strip()}:{SHARE_PORT}/koderlab-share.zip"
        dest = os.path.join(os.path.dirname(BASE_DIR), "koderlab-received")
        self.receive_btn.setEnabled(False)
        self.log("═══ Получение по сети ═══", "run")
        self._recv_worker = ReceiveWorker(url, dest)
        self._recv_worker.sig_line.connect(self.log)
        self._recv_worker.sig_progress.connect(self.log_progress)
        self._recv_worker.sig_done.connect(self._on_received)
        self._recv_worker.start()

    def _on_received(self, dest):
        self.receive_btn.setEnabled(True)
        if dest:
            QMessageBox.information(
                self, "Получено",
                f"Папка получена сюда:\n{dest}/koderlab-linux\n\n"
                "Откройте её и запустите оттуда ./start.sh")

    def _github_search(self, app_id=None):
        """Поиск программы на GitHub. Без аргумента берёт выделенную в дереве."""
        if not app_id:
            items = self.tree.selectedItems()
            data = items[0].data(0, Qt.UserRole) if items else None
            if not data or data.get("type") != "app":
                QMessageBox.information(
                    self, "Выберите программу",
                    "Щёлкните в списке по программе, для которой нужно найти файл, "
                    "и нажмите кнопку ещё раз.\n\n"
                    "Либо нажмите кнопку 🔎 прямо в строке нужной программы.")
                return
            app_id = data["id"]
        app = self._app_by_id(app_id)
        if not app:
            return
        dlg = GitHubSearchDialog(app, self)
        dlg.exec_()
        if dlg.saved_path:
            self.log(f"✓ Файл для «{app['name']}» лежит в "
                     f"installers/{app_id}/{os.path.basename(dlg.saved_path)} — "
                     "можно устанавливать, а затем раздать папку по сети.", "ok")
            self._refresh_statuses()

    def _system_report(self):
        if self._report_worker and self._report_worker.isRunning():
            return
        self.report_btn.setEnabled(False)
        self.log("", "info")
        self.log("═══ Отчёт о компьютере ═══", "run")
        self._report_worker = SystemReportWorker()
        self._report_worker.sig_line.connect(self.log)
        self._report_worker.sig_done.connect(self._on_report_done)
        self._report_worker.start()

    def _on_report_done(self, path):
        self.report_btn.setEnabled(True)
        if not path:
            return
        r = QMessageBox.question(
            self, "Отчёт готов",
            f"Отчёт сохранён:\n{path}\n\n"
            "Снимите такой же на компьютере, где всё работает, и сравните файлы — "
            "различие и будет причиной.\n\nОткрыть папку с отчётами?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
        if r == QMessageBox.Yes:
            try:
                subprocess.Popen(_as_user(["xdg-open", os.path.dirname(path)]),
                                 start_new_session=True)
            except OSError as e:
                self.log(f"⚠ Не удалось открыть папку: {e}", "warn")

    def _repair_flatpak(self):
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Дождитесь окончания операции.")
            return
        r = QMessageBox.question(
            self, "Починка flatpak",
            "Будут переустановлены пакеты flatpak и libcurl — это лечит ошибку "
            "flatpak_create_http_session (CURLM).\n\n"
            "Потребуется пароль администратора. Установленные через flatpak "
            "программы при этом не пострадают.\n\nПродолжить?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.Yes)
        if r != QMessageBox.Yes:
            return
        self.fp_btn.setEnabled(False)
        self._fp_worker = FlatpakRepairWorker()
        self._fp_worker.sig_line.connect(self.log)
        self._fp_worker.sig_progress.connect(self.log_progress)
        self._fp_worker.sig_done.connect(self._on_flatpak_repaired)
        self._fp_worker.start()

    def _on_flatpak_repaired(self, state):
        self.fp_btn.setEnabled(True)
        self._refresh_statuses()
        msg = {
            "ok": "flatpak работает. Можно устанавливать программы из Flathub.",
            "broken": "flatpak всё ещё сломан. Подробности и что проверить — "
                      "в журнале окна.",
            "network": "flatpak исправен, но репозиторий недоступен — похоже, "
                       "сеть блокирует Flathub. Используйте бандл .flatpak.",
            "error": "Не удалось выполнить починку — смотрите журнал.",
            "cancelled": "Отменено.",
        }.get(state, "Готово.")
        QMessageBox.information(self, "Починка flatpak", msg)

    def _wine_settings(self):
        wine_apps = {}
        for aid in self.courses.get("apps", {}):
            app = self._app_by_id(aid)
            if (app.get("installer") or "").lower() == "wine" or app.get("wine_arch"):
                wine_apps[aid] = app
        if not wine_apps:
            QMessageBox.information(self, "Нет Windows-программ",
                                    "В этой сборке нет программ, работающих через Wine.")
            return
        WineSettingsDialog(wine_apps, self).exec_()
        self._refresh_statuses()

    def remember_github(self, app_id, repo, filename):
        """Записывает найденный репозиторий в courses.json, чтобы на других
        компьютерах файл скачивался автоматически."""
        try:
            with open(COURSES_FILE, encoding="utf-8") as f:
                cfg = json.load(f)
            app = cfg.get("apps", {}).get(app_id)
            if app is None:
                return
            app["github"] = repo
            # шаблон по расширению — чтобы в следующий раз взялся такой же тип файла
            ext = next((e for e in _LINUX_EXTS if filename.lower().endswith(e)), None)
            if ext:
                app["github_asset"] = "(?i)" + re.escape(ext) + "$"
            app.setdefault("file", f"{app_id}/{filename}")
            tmp = COURSES_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(cfg, f, ensure_ascii=False, indent=2)
            os.replace(tmp, COURSES_FILE)
            _chown_to_user(os.path.dirname(COURSES_FILE))
            self.courses = self._load_courses()
            self.log(f"✓ Запомнил: {app_id} → GitHub {repo} "
                     f"(шаблон файла {app.get('github_asset', '—')})", "ok")
        except Exception as e:
            self.log(f"⚠ Не удалось записать courses.json: {e}", "warn")

    def _sort_downloads(self):
        if self.worker and self.worker.isRunning():
            QMessageBox.warning(self, "Занято", "Дождитесь окончания текущей операции.")
            return
        start_dir = os.path.dirname(BASE_DIR)
        folder = QFileDialog.getExistingDirectory(self, "Папка со скачанными установщиками", start_dir)
        if not folder:
            return
        self.sort_btn.setEnabled(False)
        self.log(f"═══ Раскладываю файлы из {folder} ═══", "run")
        self._sort_worker = SortWorker(folder, self.courses.get("apps", {}))
        self._sort_worker.sig_line.connect(self.log)
        self._sort_worker.sig_progress.connect(self.log_progress)
        self._sort_worker.sig_done.connect(self._on_sort_done)
        self._sort_worker.start()

    def _on_sort_done(self, report):
        self.sort_btn.setEnabled(True)
        msg = (f"Разложено: {report.get('matched', 0)}    "
               f"Неоднозначно: {report.get('ambiguous', 0)}    "
               f"Не распознано: {report.get('unmatched', 0)}")
        self.log(f"═══ Итог: {msg} ═══", "ok")
        self._refresh_statuses()
        extra = ""
        if report.get("ambiguous") or report.get("unmatched"):
            extra = ("\n\nНеоднозначные и нераспознанные файлы разложите вручную "
                     "в installers/<id>/ — какое имя ожидается, видно в подсказке "
                     "ПОЛОЖИТЕ_ФАЙЛ_СЮДА.txt внутри каждой папки.")
        QMessageBox.information(self, "Готово", msg + extra)

    def closeEvent(self, event):
        self._stop_share()
        running = [a for a, w in self._launchers.items() if w.isRunning()]
        if running:
            names = ", ".join(self._app_by_id(a)["name"] for a in running)
            r = QMessageBox.question(
                self, "Есть запущенные программы",
                f"Сейчас работают: {names}.\n\n"
                "«Да» — закрыть установщик и остановить их.\n"
                "«Нет» — остаться в установщике.",
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
            if r != QMessageBox.Yes:
                event.ignore()
                return
            for a in running:
                self._launchers[a].stop()
        super().closeEvent(event)

    def _on_step(self, current, total, name):
        self._step_text = f"{name} ({current}/{total})"
        self.progress.setMaximum(total)
        self.progress.setValue(current)

    def _cancel(self):
        if self.worker and self.worker.isRunning():
            self.worker.cancel()
            self.log("→ Запрошена отмена…", "warn")

    def _on_finished(self, report):
        self.timer.stop()
        self.cancel_btn.setEnabled(False)
        el = int(time.time() - self._t0)
        self.progress.setValue(self.progress.maximum())
        if self.action == "install":
            msg = (f"Успешно: {report.get('success', 0)}    "
                   f"Ошибок: {report.get('error', 0)}    "
                   f"Пропущено: {report.get('skipped', 0)}")
        else:
            msg = (f"Удалено: {report.get('removed', 0)}    "
                   f"Ошибок: {report.get('error', 0)}")
        self.status_label.setText(f"✓ Готово за {el} с")
        self.log(f"═══ Итог за {el} с: {msg} ═══", "ok")
        self._refresh_statuses()
        QMessageBox.information(self, "Готово", msg)

    def _show_help(self):
        text = (
            "• У каждого приложения показан статус: ● установлено / ○ нет.\n"
            "• Кнопка справа: «Установить» или «Удалить» — по текущему статусу.\n"
            "• «▶ Запустить» — открывает уже установленную программу.\n"
            "• «⟳ Обновить статусы» — перечитать состояние системы.\n\n"
            f"Система определена как: {DISTRO_NAME}\n"
            f"Пакетный менеджер: {PKG_MANAGER or 'не найден'} (пакеты .{PKG_FAMILY})\n\n"
            "Файлы установщиков кладутся в installers/<id программы>/ "
            "(имя файла указано в courses.json и в подсказке внутри папки).\n\n")
        if self.simple:
            text += (
                "«▸ ⚙ Настройки» — переустановка и настройки Wine (версия "
                "Wine, компоненты, сброс окружения, диагностика).\n\n")
        else:
            text += (
                "«📡 Раздать по сети» — упаковывает эту папку целиком и раздаёт "
                "другим ПК класса через встроенный веб-сервер. На принимающем "
                "компьютере нажмите «📥 Получить по сети» и введите IP раздающего.\n\n")
        text += (
            "Программы с пометкой «нет версии для Linux» установить нельзя — "
            "наведите на них курсор, во всплывающей подсказке написано, чем их "
            "заменить.")
        QMessageBox.information(self, "Помощь", text)


# ---------------------------------------------------------------------------
# Автообновление
# ---------------------------------------------------------------------------

# Репозиторий приватный: доступ только по токену с правом «только чтение»
# на этот единственный репозиторий (создаётся на github.com/settings/tokens,
# Fine-grained token → Only select repositories → koderlab-linux →
# Repository permissions → Contents: Read-only). Токен кладётся в файл
# update_token.txt рядом с main.py — в git этот файл не попадает
# (см. .gitignore), он существует только на установленных копиях.
UPDATE_REPO = "Wolosko/koderlab-linux"
UPDATE_TOKEN_FILE = os.path.join(BASE_DIR, "update_token.txt")
# Что обновляется из репозитория. installers/ (файлы программ) и то, что
# создаётся на месте (ярлыки, settings.json, markers) — не трогаем, это
# не код, а данные конкретного компьютера.
UPDATE_TRACKED = ["main.py", "courses.json", "start.sh",
                  "build_flatpak_bundles.sh", "ЧИТАЙ.txt", "icons"]


def _update_token():
    try:
        with open(UPDATE_TOKEN_FILE, encoding="utf-8") as f:
            return f.read().strip() or None
    except OSError:
        return None


def check_for_update(line=None):
    """Сверяет версию с GitHub. Возвращает (есть_ли_новее, версия).

    Не ломает запуск, если сети/токена нет или GitHub недоступен — тогда
    просто (False, None), и программа работает как есть. line, если
    передан, получает подробности проверки (для журнала админ-окна)."""
    def report(text, kind="info"):
        if line:
            line(text, kind)

    token = _update_token()
    if not token:
        report(f"○ Автообновление выключено: не найден файл "
               f"{UPDATE_TOKEN_FILE} — положите туда GitHub-токен с правом "
               "читать репозиторий koderlab-linux (см. инструкцию).", "warn")
        return False, None

    report(f"→ Автообновление: сверяю версию с {UPDATE_REPO}…", "run")
    try:
        req = urllib.request.Request(
            f"https://api.github.com/repos/{UPDATE_REPO}/contents/courses.json",
            headers={"Authorization": f"Bearer {token}",
                     "Accept": "application/vnd.github.raw"})
        with urllib.request.urlopen(req, timeout=8) as r:
            remote = json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        if e.code in (401, 403):
            report("✗ Автообновление: токен не подходит (нет доступа к "
                   f"{UPDATE_REPO}) — код {e.code}. Проверьте, что токен "
                   "не истёк и даёт доступ Contents: Read-only именно к "
                   "этому репозиторию.", "err")
        elif e.code == 404:
            report(f"✗ Автообновление: репозиторий {UPDATE_REPO} или файл "
                   "courses.json в нём не найден (код 404).", "err")
        else:
            report(f"⚠ Автообновление: GitHub ответил ошибкой {e.code}.", "warn")
        return False, None
    except (OSError, urllib.error.URLError, ValueError, UnicodeDecodeError) as e:
        report(f"⚠ Автообновление: не удалось проверить — нет сети или "
               f"GitHub недоступен ({e}).", "warn")
        return False, None

    remote_version = remote.get("version")
    if not remote_version:
        report("⚠ Автообновление: в courses.json репозитория не указано "
               "поле \"version\".", "warn")
        return False, None
    if str(remote_version) != KODERLAB_VERSION:
        report(f"⚠ Автообновление: доступна версия {remote_version} "
               f"(сейчас установлена {KODERLAB_VERSION}).", "warn")
        return True, str(remote_version)
    report(f"✓ Автообновление: установлена последняя версия ({KODERLAB_VERSION}).", "ok")
    return False, None


def apply_update():
    """Скачивает свежий снимок репозитория (архив целиком, без git) и
    подменяет файлы программы. Возвращает (успех, сообщение об ошибке)."""
    token = _update_token()
    if not token:
        return False, "нет файла update_token.txt"
    tmp_dir = tempfile.mkdtemp(prefix="koderlab_update_")
    archive = os.path.join(tmp_dir, "update.tar.gz")
    try:
        req = urllib.request.Request(
            f"https://api.github.com/repos/{UPDATE_REPO}/tarball/main",
            headers={"Authorization": f"Bearer {token}"})
        with urllib.request.urlopen(req, timeout=120) as r, open(archive, "wb") as f:
            shutil.copyfileobj(r, f)
        with tarfile.open(archive) as tf:
            tf.extractall(tmp_dir)
        # GitHub кладёт содержимое в одну вложенную папку вида
        # владелец-репо-хэш — берём её.
        roots = [d for d in os.listdir(tmp_dir)
                if os.path.isdir(os.path.join(tmp_dir, d))]
        if not roots:
            return False, "архив обновления пуст"
        src_root = os.path.join(tmp_dir, roots[0])
        for name in UPDATE_TRACKED:
            src = os.path.join(src_root, name)
            if not os.path.exists(src):
                continue
            dest = os.path.join(BASE_DIR, name)
            if os.path.isdir(src):
                shutil.rmtree(dest, ignore_errors=True)
                shutil.copytree(src, dest)
            else:
                shutil.copy2(src, dest)
        return True, ""
    except (OSError, tarfile.TarError, urllib.error.URLError) as e:
        return False, str(e)
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def main():
    ensure_dirs()
    app = QApplication(sys.argv)

    # Автообновление: если есть токен и в репозитории версия отличается —
    # ставим обязательно, до открытия окна. Нет сети/токена — работаем
    # с тем, что есть, никого не блокируем.
    has_update, new_version = check_for_update()
    if has_update:
        dlg = QProgressDialog(
            f"Доступно обновление {new_version} (сейчас {KODERLAB_VERSION}). "
            "Устанавливаю…", None, 0, 0)
        dlg.setWindowTitle("Обновление KoderLab")
        dlg.setWindowModality(Qt.ApplicationModal)
        dlg.setMinimumDuration(0)
        dlg.setCancelButton(None)
        dlg.show()
        app.processEvents()
        ok, err = apply_update()
        dlg.close()
        if ok:
            QMessageBox.information(
                None, "Обновление установлено",
                f"Установлена версия {new_version}. Сейчас программа перезапустится.")
            os.execv(sys.executable, [sys.executable, os.path.abspath(__file__)] + sys.argv[1:])
        else:
            QMessageBox.warning(
                None, "Не удалось обновить",
                f"Не получилось установить обновление {new_version}: {err}\n\n"
                "Программа запустится с текущей версией.")

    # Проверка ключа доступа ВЫКЛЮЧЕНА по умолчанию.
    # Включается только явно: KODERLAB_LICENSE=1 ./start.sh
    # Так задумано: пока схема с ключами не настроена (не сменён секрет,
    # не выложена страница), программа не должна требовать ключ — иначе
    # интерфейс просто не открывается.
    if os.environ.get("KODERLAB_LICENSE") == "1":
        try:
            import license as _license
        except ImportError:
            _license = None
        if _license is not None and not _license.ensure_access():
            sys.exit(0)

    if not os.path.exists(COURSES_FILE):
        QMessageBox.critical(None, "Ошибка",
                             f"Не найден файл courses.json рядом с программой:\n{COURSES_FILE}")
        sys.exit(1)
    if not is_root():
        ensure_launcher_shortcut()
    with open(COURSES_FILE, encoding="utf-8") as f:
        simple = bool((json.load(f).get("ui") or {}).get("simple"))
    win = LauncherWindow() if simple else MainWindow()
    win.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
