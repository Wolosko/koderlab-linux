#!/usr/bin/env bash
# Мини-установщик: KoderLab (Legacy Launcher) + модпак ComputerCraftEdu RUS
# Обычно запускается из окна (./start.sh). Вручную, в терминале:
#   bash install.sh               установка (без sudo — пароль спросит сам)
#   bash install.sh --reinstall   переустановка начисто
#   bash install.sh --uninstall   удаление
# KODERLAB_GUI=1  — вывод для окна: без цветов, с отметками шагов, без вопросов.
# KODERLAB_NICK=… — ник вместо автоматического KoderNNNN.
# KODERLAB_EMBEDDED=1, KODERLAB_INSTALLERS=… — так вызывает основное приложение
#   KoderLab (main.py): шаги строкой в журнал, файлы — из его installers/.
#
# Файлы сначала берутся из installers/ рядом со скриптом, и только если их там
# нет — качаются из интернета (несколько зеркал). Не скачался мод — пропускаем
# его и ставим остальное; без лаунчера установка не имеет смысла.
#
# Как это работает (проверено на Legacy Launcher 1.169.4):
#   - LegacyLauncher.jar — загрузчик; сам лаунчер он при первом запуске
#     скачивает в ~/.tlauncher/bin/legacy.jar;
#   - Forge ставит сам лаунчер: версия «Forge 1.8.9» из его репозитория —
#     это Forge 11.15.1.2318, ровно тот, что нужен модпаку (у установщика
#     Forge 1.8.9 нет режима --installClient, поэтому ставить его отдельно
#     бессмысленно);
#   - ник, версия и папка игры задаются файлами (mc_profile.py) и
#     аргументами --username/--version/--directory при каждом запуске.

set -u
cd "$(dirname "$0")" || exit 1
BASE_DIR="$(pwd)"
# Где искать готовые файлы (по порядку): папка installers/ основного
# приложения KoderLab (передаёт KODERLAB_INSTALLERS), своя installers/,
# files/ — то, что лежит прямо в репозитории (моды: CurseForge в школах
# бывает недоступен).
SEARCH_DIRS=()
[ -n "${KODERLAB_INSTALLERS:-}" ] && SEARCH_DIRS+=("$KODERLAB_INSTALLERS")
SEARCH_DIRS+=("$BASE_DIR/installers" "$BASE_DIR/files")

# те же пути, что у основного приложения KoderLab (main.py)
APP_ID="legacy_launcher"
APP_NAME="KoderLab (Legacy Launcher)"
DATA_DIR="$HOME/.local/share/KoderLab"
APP_DIR="$DATA_DIR/apps/$APP_ID"
MARKER="$DATA_DIR/installed/$APP_ID.json"
DESKTOP_FILE="$HOME/.local/share/applications/koderlab-$APP_ID.desktop"
JAR="$APP_DIR/LegacyLauncher.jar"
RUN_SH="$APP_DIR/run.sh"
PROFILE_PY="$APP_DIR/mc_profile.py"
NICK_FILE="$DATA_DIR/minecraft-nick"
MC_DIR="$HOME/.minecraft"
MODS_DIR="$MC_DIR/mods"
TL_DIR="$HOME/.tlauncher"
SETTINGS="$TL_DIR/legacy.properties"
MC_VERSION="Forge 1.8.9"

CF="https://www.curseforge.com/api/v1/mods"
CDN1="https://mediafilez.forgecdn.net/files"
CDN2="https://edge.forgecdn.net/files"

# Мин. версия Java: на 11-й лаунчеры семейства TLauncher не стартуют.
# Для самой игры лаунчер скачивает свою Java (~/.tlauncher/mojang_jre).
JAVA_MIN=17

# Переносная Java в домашней папке: без пароля и без места на «/»
# (на ПК класса корневой раздел бывает забит — dnf тогда не ставит ничего).
JRE_DIR="$DATA_DIR/jre17"
JRE_FILE="OpenJDK17U-jre_x64_linux_hotspot_17.0.21_9.tar.gz"
JRE_SHA256="9f41bf88c7900c7097444a1bdeb84146ae692bc08842490ab098063c74bf9a8a"
JRE_URLS=(
    "https://github.com/adoptium/temurin17-binaries/releases/download/jdk-17.0.21%2B9/$JRE_FILE"
    "https://mirrors.tuna.tsinghua.edu.cn/Adoptium/17/jre/x64/linux/$JRE_FILE"
    "https://api.adoptium.net/v3/binary/latest/17/ga/linux/x64/jre/hotspot/normal/eclipse"
)

# Сколько места нужно в домашней папке: Java ~130 МБ, лаунчер ~30 МБ,
# Minecraft 1.8.9 + Forge ~250 МБ, Java для игры ~100 МБ
SPACE_NEED_MB=600
SPACE_WARN_MB=1024

GUI="${KODERLAB_GUI:-0}"
if [ "$GUI" = 1 ]; then
    ok()   { printf '✓ %s\n' "$*"; }
    info() { printf '→ %s\n' "$*"; }
    warn() { printf '⚠ %s\n' "$*"; }
    die()  { printf '✗ %s\n' "$*"; exit 1; }
    if [ "${KODERLAB_EMBEDDED:-0}" = 1 ]; then   # журнал основного приложения KoderLab
        step() { printf '▸ [%s/%s] %s\n' "$1" "$2" "$3"; }
    else
        step() { printf '##STEP %s %s %s\n' "$1" "$2" "$3"; }   # мини-окно рисует по ним полосу
    fi
else
    ok()   { printf '\033[32m✓ %s\033[0m\n' "$*"; }
    info() { printf '\033[34m→\033[0m %s\n' "$*"; }
    warn() { printf '\033[33m⚠ %s\033[0m\n' "$*"; }
    die()  { printf '\033[31m✗ %s\033[0m\n' "$*" >&2; exit 1; }
    step() { printf '\n\033[1m[%s/%s] %s\033[0m\n' "$1" "$2" "$3"; }
fi
STEPS=6

[ "$(id -u)" -eq 0 ] && die "Запускайте БЕЗ sudo: под root лаунчер и Minecraft не работают."

ACTION="${1:-install}"   # install | --reinstall | --uninstall

# ---------------------------------------------------------------- пакеты
# dnf — первым: на ROSA есть и apt-get, но это заглушка
# («apt больше не поддерживается. Используйте dnf»)
PM=""
if   command -v dnf     >/dev/null 2>&1; then PM=dnf
elif command -v zypper  >/dev/null 2>&1; then PM=zypper
elif command -v pacman  >/dev/null 2>&1; then PM=pacman
elif command -v apt-get >/dev/null 2>&1; then PM=apt
fi

priv() {  # выполнить с правами администратора: окно пароля, если есть графика
    if command -v pkexec >/dev/null 2>&1 && [ -n "${DISPLAY:-}${WAYLAND_DISPLAY:-}" ]; then
        pkexec "$@"
    elif [ -n "${SUDO_ASKPASS:-}" ]; then
        sudo -A "$@"      # из окна: пароль спрашивает main.py --askpass
    else
        sudo "$@"
    fi
}

pkg_install() {
    [ -n "$PM" ] || return 1
    info "Ставлю пакеты: $*"
    case "$PM" in
        apt)    priv apt-get install -y "$@" ;;
        dnf)    priv dnf install -y "$@" ;;
        zypper) priv zypper --non-interactive install "$@" ;;
        pacman) priv pacman -S --noconfirm "$@" ;;
    esac
}

desktop_dir() {  # xdg-user-dir может вернуть несуществующую папку или сам $HOME
    local d x; x="$(xdg-user-dir DESKTOP 2>/dev/null)"
    for d in "$x" "$HOME/Рабочий стол" "$HOME/Desktop"; do
        [ -n "$d" ] && [ "$d" != "$HOME" ] && [ -d "$d" ] && { echo "$d"; return; }
    done
    d="${x:-$HOME/Desktop}"; [ "$d" = "$HOME" ] && d="$HOME/Desktop"
    echo "$d"
}

# Если KoderLab когда-то запускали через sudo, его папки принадлежат root,
# и обычный пользователь в них ничего не запишет (mkdir: Отказано в доступе).
# Возвращаем их пользователю — один запрос пароля, как _chown_to_user в main.py.
fix_perms() {
    local me; me="$(id -u)"
    local list=() d
    for d in "$HOME/.local" "$HOME/.local/share" "$(desktop_dir)"; do      # только сама папка
        [ -e "$d" ] && [ "$(stat -c %u "$d" 2>/dev/null)" != "$me" ] && list+=("$d")
    done
    for d in "$DATA_DIR" "$HOME/.local/share/applications" "$MC_DIR" "$TL_DIR"; do   # с содержимым
        [ -e "$d" ] && [ -n "$(find "$d" ! -user "$me" -print -quit 2>/dev/null)" ] && list+=("R:$d")
    done
    [ "${#list[@]}" -eq 0 ] && return 0
    warn "Часть папок принадлежит root (KoderLab запускали через sudo?):"
    for d in "${list[@]}"; do warn "   ${d#R:}"; done
    info "Возвращаю их пользователю $(id -un) — нужен пароль администратора."
    priv /bin/sh -c 'o="$1"; shift
        for p in "$@"; do
            case "$p" in R:*) chown -R "$o" "${p#R:}" ;; *) chown "$o" "$p" ;; esac
        done' sh "$me:$(id -g)" "${list[@]}" \
        && ok "Права на папки исправлены" \
        || die "Не удалось исправить права. Выполните в терминале:
   sudo chown -R $(id -un): \"$DATA_DIR\" \"$HOME/.local/share/applications\" \"$MC_DIR\" \"$TL_DIR\""
}

fix_perms

# ---------------------------------------------------------------- удаление / переустановка
MOD_FILES=(BetterFps-1.2.0.jar Ding-MC1.8.9v2.jar ComputerCraft1.79.jar
           ComputerCraftEdu1.79.jar foamfix-0.6.3-law-1.8.x.jar)

remove_all() {
    rm -rf "$APP_DIR" "$DESKTOP_FILE" "$MARKER"
    for d in "$(desktop_dir)" "$HOME/Рабочий стол" "$HOME/Desktop"; do
        rm -f "$d/koderlab-$APP_ID.desktop"
    done
    for f in "${MOD_FILES[@]}"; do
        rm -f "$MODS_DIR/$f"
    done
    # от прошлых версий установщика
    rm -rf "$MC_DIR/versions/1.8.9-forge1.8.9-11.15.1.2318-1.8.9"
}

case "$ACTION" in
    --uninstall)
        remove_all
        rm -rf "$MC_DIR/versions/$MC_VERSION" "$JRE_DIR"
        ok "Удалено. Миры, ник и настройки в ~/.minecraft не тронуты."
        exit 0 ;;
    --reinstall)
        info "Переустановка: удаляю прежнюю установку (миры и ник не трогаю)…"
        remove_all ;;
esac

# Java с поддержкой окон: в headless-вариантах нет libawt_xawt.so,
# и лаунчер падает с UnsatisfiedLinkError
find_java() {
    local c j home v major
    for c in "$JRE_DIR/bin/java" "$(command -v java 2>/dev/null)" /usr/lib/jvm/*/bin/java /usr/lib64/jvm/*/bin/java; do
        [ -n "$c" ] && [ -x "$c" ] || continue
        j="$(readlink -f "$c")"
        home="$(dirname "$(dirname "$j")")"
        find "$home" -name libawt_xawt.so 2>/dev/null | grep -q . || continue
        v="$("$j" -version 2>&1 | head -1)"
        major="$(echo "$v" | sed -n 's/.*version "\([0-9][0-9]*\).*/\1/p')"
        [ "$major" = "1" ] && major="$(echo "$v" | sed -n 's/.*version "1\.\([0-9][0-9]*\).*/\1/p')"
        [ "${major:-0}" -ge "$JAVA_MIN" ] && { echo "$j"; return 0; }
    done
    return 1
}

java_variants() {  # по убыванию предпочтительности, как в main.py
    case "$PM" in
        apt)    echo "openjdk-17-jre"; echo "java-17-openjdk"; echo "openjdk-21-jre" ;;
        dnf)    echo "java-17-openjdk"; echo "java-17-openjdk-devel"; echo "java-21-openjdk" ;;
        zypper) echo "java-17-openjdk"; echo "java-21-openjdk" ;;
        pacman) echo "jre17-openjdk"; echo "jre21-openjdk" ;;
    esac
}

free_mb() {  # свободно на разделе с папкой $1, МБ
    df -Pk "$1" 2>/dev/null | awk 'NR==2 {print int($4/1024)}'
}

# Переносная Java: распаковываем в домашнюю папку (тот же раздел, что и игра),
# пароль и место на «/» не нужны. Берём из installers/java/, иначе качаем.
install_portable_java() {
    local tgz="" t check_sha=0
    [ "$(uname -m)" = "x86_64" ] || { warn "Переносная Java есть только для x86_64 (здесь $(uname -m))."; return 1; }
    local d
    for d in "${SEARCH_DIRS[@]}"; do
        for t in "$d/java/$JRE_FILE" "$d"/java/OpenJDK17U-jre_x64_linux_*.tar.gz; do
            [ -s "$t" ] && { tgz="$t"; break 2; }
        done
    done
    [ -n "$tgz" ] && info "Переносная Java из $(dirname "$tgz")"
    # сумму знаем только для своего файла (чужой архив в installers/ не проверяем)
    [ -n "$tgz" ] && [ "$(basename "$tgz")" = "$JRE_FILE" ] && check_sha=1
    if [ -z "$tgz" ]; then
        info "Скачиваю переносную Java 17 (~45 МБ)…"
        tgz="$DATA_DIR/jre-download.tar.gz"
        mkdir -p "$DATA_DIR" || return 1
        for t in "${JRE_URLS[@]}"; do
            rm -f "$tgz"
            if command -v curl >/dev/null 2>&1; then
                curl -fsL --retry 2 --connect-timeout 15 -o "$tgz" "$t"
            else
                wget -q -T 15 -O "$tgz" "$t"
            fi
            if [ -s "$tgz" ] && gzip -t "$tgz" 2>/dev/null; then
                # ссылки на точную версию — со сверкой суммы; «latest» из API — без
                case "$t" in *"$JRE_FILE") check_sha=1 ;; esac
                break
            fi
        done
        [ -s "$tgz" ] && gzip -t "$tgz" 2>/dev/null || { rm -f "$tgz"; warn "Переносная Java не скачалась."; return 1; }
    fi
    if [ "$check_sha" = 1 ] && command -v sha256sum >/dev/null 2>&1; then
        [ "$(sha256sum "$tgz" | cut -d' ' -f1)" = "$JRE_SHA256" ] \
            || { warn "Архив Java повреждён (контрольная сумма не совпала): $tgz"; return 1; }
    fi
    local tmp="$DATA_DIR/jre-unpack.$$"
    rm -rf "$tmp"; mkdir -p "$tmp" || return 1
    if ! tar -xzf "$tgz" -C "$tmp" 2>/dev/null; then
        rm -rf "$tmp"; warn "Не удалось распаковать Java (мало места в домашней папке?)"; return 1
    fi
    local top; top="$(find "$tmp" -mindepth 1 -maxdepth 1 -type d | head -1)"
    [ -f "$top/bin/java" ] || { rm -rf "$tmp"; warn "В архиве Java нет bin/java"; return 1; }
    chmod +x "$top"/bin/* "$top"/lib/jspawnhelper 2>/dev/null
    rm -rf "$JRE_DIR" && mv "$top" "$JRE_DIR" && rm -rf "$tmp"
    [ "$tgz" = "$DATA_DIR/jre-download.tar.gz" ] && rm -f "$tgz"
    "$JRE_DIR/bin/java" -version >/dev/null 2>&1 \
        || { warn "Переносная Java не запускается ($JRE_DIR/bin/java)."; return 1; }
    ok "Переносная Java 17 установлена: $JRE_DIR"
}

# ---------------------------------------------------------------- место на диске
mkdir -p "$DATA_DIR" 2>/dev/null
FREE="$(free_mb "$HOME")"
if [ -n "$FREE" ]; then
    if [ "$FREE" -lt "$SPACE_NEED_MB" ]; then
        die "В домашней папке свободно всего ${FREE} МБ, а нужно хотя бы ${SPACE_NEED_MB} МБ
   (Java, лаунчер, Minecraft 1.8.9 и Forge). Освободите место и нажмите «Переустановить».
   Посмотреть, что занимает место:  du -sh ~/* ~/.[!.]* | sort -h | tail"
    elif [ "$FREE" -lt "$SPACE_WARN_MB" ]; then
        warn "В домашней папке свободно ${FREE} МБ — впритык (лучше от ${SPACE_WARN_MB} МБ)."
    else
        ok "Место в домашней папке: ${FREE} МБ свободно"
    fi
fi

step 1 $STEPS "Java"
JAVA="$(find_java)" || {
    warn "Нет Java $JAVA_MIN+ с поддержкой окон."
    # сначала переносная: без пароля, офлайн, не зависит от места на «/»
    install_portable_java && JAVA="$(find_java)"
    if [ -z "${JAVA:-}" ]; then
        ROOT_FREE="$(free_mb /)"
        [ -n "$ROOT_FREE" ] && [ "$ROOT_FREE" -lt 300 ] \
            && warn "На системном разделе «/» свободно ${ROOT_FREE} МБ — пакет Java туда может не поместиться."
        info "Пробую поставить Java из репозитория…"
        for p in $(java_variants); do
            pkg_install "$p" && JAVA="$(find_java)" && break
        done
    fi
    [ -n "${JAVA:-}" ] || die "Java поставить не удалось.
   Проще всего: положите $JRE_FILE в installers/java/ и нажмите «Переустановить».
   Или вручную:
   ROSA:            sudo dnf install java-17-openjdk
   Альт / М ОС:     sudo apt-get install java-17-openjdk
   Astra / Debian:  sudo apt-get install openjdk-17-jre"
}
ok "Java: $JAVA"

command -v curl >/dev/null 2>&1 || command -v wget >/dev/null 2>&1 \
    || pkg_install curl || warn "Нет ни curl, ни wget — скачать ничего не получится, только из installers/"
command -v unzip >/dev/null 2>&1 || pkg_install unzip || true
PY="$(command -v python3 2>/dev/null)"
[ -n "$PY" ] || { pkg_install python3 && PY="$(command -v python3 2>/dev/null)"; }

for d in "$APP_DIR" "$MODS_DIR" "$TL_DIR" "$(dirname "$MARKER")" "$(dirname "$DESKTOP_FILE")"; do
    mkdir -p "$d" 2>/dev/null && [ -w "$d" ] || die "Нет доступа к папке $d. Выполните:
   sudo chown -R $(id -un): \"$d\"   — и нажмите «Переустановить»."
done
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

is_zip() {  # jar и zip — это zip: проверяем, что скачался не HTML с ошибкой
    [ -s "$1" ] && [ "$(head -c 2 "$1")" = "PK" ]
}

download() {  # download <файл> <url>...   пробует зеркала по очереди
    local out="$1" u; shift
    for u in "$@"; do
        if command -v curl >/dev/null 2>&1; then
            curl -fsL --retry 2 --connect-timeout 15 -A "Mozilla/5.0" -o "$out" "$u"
        else
            wget -q -T 15 -U "Mozilla/5.0" -O "$out" "$u"
        fi
        is_zip "$out" && return 0
        rm -f "$out"
    done
    return 1
}

fetch() {  # fetch <путь внутри installers/ (или files/)> <куда> <url>...
    local rel="$1" out="$2" d; shift 2
    for d in "${SEARCH_DIRS[@]}"; do
        if is_zip "$d/$rel"; then
            cp -f "$d/$rel" "$out"; return 0
        fi
    done
    download "$out" "$@"
}

# ---------------------------------------------------------------- Legacy Launcher
step 2 $STEPS "Legacy Launcher"
fetch "legacy_launcher/LegacyLauncher.jar" "$TMP/launcher.jar" \
      "https://llaun.ch/jar" \
    || die "Не удалось получить Legacy Launcher. Положите LegacyLauncher.jar в installers/legacy_launcher/"
mv -f "$TMP/launcher.jar" "$JAR" || die "Не удалось записать $JAR"
ok "Legacy Launcher: $JAR"

# ---------------------------------------------------------------- модпак ComputerCraftEdu RUS
# manifest.json модпака: projectID fileID путь-на-CDN
MODS=(
    "229876 2271480 2271/480/BetterFps-1.2.0.jar"
    "231275 2283571 2283/571/Ding-MC1.8.9v2.jar"
    "67504  2291384 2291/384/ComputerCraft1.79.jar"
    "278494 2545191 2545/191/foamfix-0.6.3-law-1.8.x.jar"
)
SKIPPED=()

step 3 $STEPS "Модпак ComputerCraftEdu RUS"
if fetch "computercraftedu_rus/ComputerCraftEdu_RUS-1.0.zip" "$TMP/modpack.zip" \
        "$CF/538679/files/3507371/download" \
        "$CDN1/3507/371/ComputerCraftEdu%20RUS-1.0.zip" \
        "$CDN2/3507/371/ComputerCraftEdu%20RUS-1.0.zip" \
   && unzip -q -o "$TMP/modpack.zip" -d "$TMP/pack" 2>/dev/null; then
    # overrides: русская ComputerCraftEdu и настройки (свои настройки не затираем)
    cp -f "$TMP/pack/overrides/mods/"*.jar "$MODS_DIR/" && ok "Мод: ComputerCraftEdu1.79.jar (русский)"
    [ -f "$MC_DIR/options.txt" ] || cp "$TMP/pack/overrides/options.txt" "$MC_DIR/options.txt"
else
    warn "Модпак не скачался — пропускаю русскую ComputerCraftEdu."
    SKIPPED+=("ComputerCraftEdu RUS")
fi

step 4 $STEPS "Моды"
for entry in "${MODS[@]}"; do
    set -- $entry
    name="$(basename "$3")"
    if fetch "computercraftedu_rus/mods/$name" "$MODS_DIR/$name" \
            "$CF/$1/files/$2/download" "$CDN1/$3" "$CDN2/$3"; then
        ok "Мод: $name"
    else
        warn "Мод $name не скачался — пропускаю."
        SKIPPED+=("$name")
    fi
done

# ---------------------------------------------------------------- ник и настройки лаунчера
step 5 $STEPS "Ник и настройки лаунчера"
cp -f "$BASE_DIR/mc_profile.py" "$PROFILE_PY" || die "Нет файла mc_profile.py рядом с установщиком"
NICK=""
if [ -n "$PY" ]; then
    NICK="$("$PY" "$PROFILE_PY" ensure "$MC_DIR" "$SETTINGS" "$NICK_FILE" ${KODERLAB_NICK:+"$KODERLAB_NICK"})" \
        || die "Не удалось записать ник и настройки лаунчера (см. ошибку выше)"
else
    # без Python — простой вариант: новый профиль и ключи в конец настроек
    NICK="${KODERLAB_NICK:-$(cat "$NICK_FILE" 2>/dev/null)}"
    [ -n "$NICK" ] || NICK="Koder$(( $(od -An -N2 -tu2 /dev/urandom | tr -d ' ') % 9000 + 1000 ))"
    echo "$NICK" > "$NICK_FILE"
    U="$(tr -d '-' < /proc/sys/kernel/random/uuid)"
    printf '{"userSet":{"list":[{"username":"%s","uuid":"%s","elySkins":false,"type":"plain"}],"selected":{"username":"%s","type":"plain"}}}\n' \
        "$NICK" "$U" "$NICK" > "$MC_DIR/tlauncher_profiles.json"
    grep -q '^settings.version=' "$SETTINGS" 2>/dev/null || echo "settings.version=3" >> "$SETTINGS"
    printf '%s\n' "login.version=$MC_VERSION" "minecraft.gamedir=$MC_DIR" \
        "minecraft.servers.promoted=false" "notice.enabled=false" "gui.notices.enabled=false" >> "$SETTINGS"
    warn "Python 3 не найден — настройки записаны упрощённо."
fi
ok "Ник: $NICK"
ok "Версия по умолчанию: $MC_VERSION (Forge 11.15.1.2318) — лаунчер скачает её при первом входе"
ok "Папка игры: $MC_DIR"
ok "Реклама серверов в лаунчере выключена"

# ---------------------------------------------------------------- ярлык и маркер
step 6 $STEPS "Ярлык"
ICON=""
for i in "$BASE_DIR/icons/legacy_launcher.png" "$BASE_DIR/../icons/legacy_launcher.png" "$BASE_DIR/../icons/tlauncher.png"; do
    [ -f "$i" ] && cp -f "$i" "$APP_DIR/icon.png" && { ICON="$APP_DIR/icon.png"; break; }
done

# run.sh — единая точка запуска (ярлык, кнопка в окне, play.sh).
# При каждом запуске: заново ищет Java (путь мог смениться после обновления),
# возвращает ник и настройки (если ученик удалил аккаунт или сменил версию),
# и передаёт лаунчеру папку игры, версию и ник аргументами.
cat > "$RUN_SH" <<EOF
#!/usr/bin/env bash
# Запуск KoderLab (Legacy Launcher) — создано установщиком KoderLab
cd "$APP_DIR" || exit 1
JAR="$JAR"
JAVA="$JAVA"
MC_DIR="$MC_DIR"
SETTINGS="$SETTINGS"
NICK_FILE="$NICK_FILE"
LOG="$APP_DIR/launcher.log"

msg() {  # сообщение — окном, если есть чем его показать, иначе в терминал
    echo "\$2" >&2
    if command -v notify-send >/dev/null 2>&1 && [ "\$1" = info ]; then
        notify-send -i "$APP_DIR/icon.png" "$APP_NAME" "\$2" 2>/dev/null; return
    fi
    command -v zenity  >/dev/null 2>&1 && zenity --\$1 --text="\$2" 2>/dev/null && return
    command -v kdialog >/dev/null 2>&1 && kdialog --\$( [ "\$1" = error ] && echo error || echo msgbox ) "\$2" 2>/dev/null
}

if [ ! -x "\$JAVA" ]; then
    JAVA=""
    for c in "$JRE_DIR/bin/java" /usr/lib/jvm/*/bin/java /usr/lib64/jvm/*/bin/java "\$(command -v java 2>/dev/null)"; do
        [ -n "\$c" ] && [ -x "\$c" ] || continue
        find "\$(dirname "\$(dirname "\$(readlink -f "\$c")")")" -name libawt_xawt.so 2>/dev/null | grep -q . \\
            && { JAVA="\$c"; break; }
    done
fi
[ -f "\$JAR" ]  || { msg error "Не найден лаунчер: \$JAR. Переустановите (bash start.sh)."; exit 1; }
[ -n "\$JAVA" ] || { msg error "Не найдена Java с поддержкой окон. Переустановите (bash start.sh)."; exit 1; }

NICK="\$(cat "\$NICK_FILE" 2>/dev/null)"
if command -v python3 >/dev/null 2>&1; then
    NICK="\$(python3 "$PROFILE_PY" ensure "\$MC_DIR" "\$SETTINGS" "\$NICK_FILE" 2>>"\$LOG")" || NICK="\$(cat "\$NICK_FILE" 2>/dev/null)"
fi
# ник не передаём аргументом: он выбран в tlauncher_profiles.json, а --username
# перебивал бы аккаунт, который ученик сам выбрал в лаунчере
ARGS=(--settings "\$SETTINGS" --directory "\$MC_DIR" --version "$MC_VERSION")

[ -f "$TL_DIR/bin/legacy.jar" ] \\
    || msg info "Первый запуск: лаунчер скачивает себя, около минуты. Окно появится само."
echo "=== \$(date '+%F %T') запуск: ник \$NICK, java \$JAVA" >>"\$LOG"
exec "\$JAVA" -jar "\$JAR" "\${ARGS[@]}" "\$@" >>"\$LOG" 2>&1
EOF
[ -s "$RUN_SH" ] && chmod +x "$RUN_SH" || die "Не удалось записать скрипт запуска $RUN_SH"
ok "Скрипт запуска: $RUN_SH"

write_desktop() {  # write_desktop <файл>; код возврата — удалось ли
    {
        echo "[Desktop Entry]"
        echo "Type=Application"
        echo "Name=$APP_NAME"
        echo "GenericName=Minecraft"
        # через bash: ярлык работает, даже если у run.sh слетел флаг исполнения
        echo "Exec=/bin/bash \"$RUN_SH\""
        echo "Path=$APP_DIR"
        echo "Terminal=false"
        echo "StartupNotify=true"
        echo "Categories=Education;Game;"
        echo "Comment=Minecraft 1.8.9 Forge + ComputerCraftEdu RUS"
        echo "Keywords=minecraft;майнкрафт;computercraft;koderlab;"
        echo "X-KoderLab=true"
        [ -n "$ICON" ] && echo "Icon=$ICON"
    } > "$1" 2>/dev/null && chmod +x "$1"
}

SHORTCUTS_OK=1
rm -f "$DESKTOP_FILE" 2>/dev/null
if write_desktop "$DESKTOP_FILE"; then
    update-desktop-database "$(dirname "$DESKTOP_FILE")" >/dev/null 2>&1 || true
    ok "Ярлык в меню приложений: $DESKTOP_FILE"
else
    warn "Не удалось создать ярлык в меню: $DESKTOP_FILE"; SHORTCUTS_OK=0
fi

DESK="$(desktop_dir)"
mkdir -p "$DESK" 2>/dev/null
DESK_FILE="$DESK/$(basename "$DESKTOP_FILE")"
rm -f "$DESK_FILE" 2>/dev/null
if write_desktop "$DESK_FILE"; then
    # «доверенный» ярлык: GNOME/Cinnamon — gio, иначе файловый менеджер просит разрешить запуск
    gio set "$DESK_FILE" metadata::trusted true >/dev/null 2>&1 || true
    ok "Ярлык на рабочем столе: $DESK_FILE"
else
    warn "Не удалось создать ярлык на рабочем столе: $DESK_FILE"; SHORTCUTS_OK=0
fi

# маркер в формате main.py — основное приложение увидит лаунчер установленным
printf '{"id": "%s", "name": "%s", "installed_at": "%s", "exec": ["/bin/bash", "%s"], "workdir": "%s", "dir": "%s", "run": "%s", "nick": "%s"}\n' \
    "$APP_ID" "$APP_NAME" "$(date +%Y-%m-%dT%H:%M:%S)" "$RUN_SH" "$APP_DIR" "$APP_DIR" "$RUN_SH" "$NICK" > "$MARKER" \
    || warn "Не удалось записать $MARKER — основное приложение KoderLab не увидит установку."

# ---------------------------------------------------------------- итог
echo
if [ "$SHORTCUTS_OK" = 1 ]; then
    ok "Готово! Ярлык «$APP_NAME» — в меню приложений и на рабочем столе."
else
    ok "Готово, но не все ярлыки создались (см. выше). Запуск: кнопка «▶ Запустить» или ./play.sh"
fi
echo "   Ник: $NICK · версия: $MC_VERSION · моды: $MODS_DIR"
echo "   В лаунчере уже выбраны ник и версия — нажмите «Установить»/«Войти в игру»."
echo "   Первый вход: лаунчер скачает Minecraft 1.8.9 и Forge (≈150 МБ, нужен интернет)."
[ "${#SKIPPED[@]}" -gt 0 ] && warn "Пропущено (не скачалось): ${SKIPPED[*]}. Положите файлы в installers/ и запустите ещё раз."
echo "   Если ярлык «недоверенный» — ПКМ → «Разрешить запуск»."
echo

[ "$GUI" = 1 ] && exit 0   # в окне запуск — отдельной кнопкой
read -r -p "Запустить лаунчер сейчас? [Y/n] " a
case "${a:-y}" in
    [Nn]*) ;;
    *) (cd "$APP_DIR" && nohup /bin/bash "$RUN_SH" >/dev/null 2>&1 &) ;;
esac
