#!/usr/bin/env bash
# Собирает офлайн .flatpak-бандлы для всех flatpak-программ KoderLab —
# чтобы install из installers/<id>/ шёл без обращения к Flathub на
# каждом компьютере класса (см. FlatpakInstaller.install() в main.py:
# если файл уже лежит в installers/<id>/, программа берёт его первым
# делом, минуя сеть).
#
# Запускать ОДИН РАЗ на компьютере с интернетом и установленным flatpak
# (сам koderlab-mini для этого не нужен собирать бандлы можно отдельно).
# Готовые файлы разложатся по installers/<id>/<id>.flatpak — дальше эту
# папку можно скопировать на все ПК класса или раздать через
# «📡 Раздать по сети» в самой программе.
#
# Важно: бандл содержит только саму программу, а не рантайм (общую
# платформу), от которой она зависит, — рантайм при первой установке
# на новом компьютере всё равно один раз скачается из Flathub, но уже
# ОДИН РАЗ на класс типов рантайма, а не по разу на программу.
set -e
cd "$(dirname "$0")"

if ! command -v flatpak >/dev/null 2>&1; then
    echo "Нужен flatpak. Поставьте и повторите:"
    echo "  ROSA / Fedora:   sudo dnf install flatpak"
    echo "  Альт / Astra / Debian/Ubuntu: sudo apt install flatpak"
    exit 1
fi

flatpak remote-add --user --if-not-exists flathub \
    https://dl.flathub.org/repo/flathub.flatpakrepo

# id программы (папка в installers/) -> идентификатор flatpak (см. courses.json)
APP_IDS="scratch:edu.mit.Scratch gcompris:org.kde.gcompris \
blockbench:net.blockbench.Blockbench roblox_studio:org.vinegarhq.Vinegar \
unity_hub:com.unity.UnityHub"

REPO="$HOME/.local/share/flatpak/repo"

for pair in $APP_IDS; do
    id="${pair%%:*}"
    ref="${pair##*:}"
    echo "═══ $id ($ref) ═══"
    if flatpak install -y --user flathub "$ref"; then
        mkdir -p "installers/$id"
        if flatpak build-bundle "$REPO" "installers/$id/$id.flatpak" "$ref"; then
            echo "✓ installers/$id/$id.flatpak — $(du -h "installers/$id/$id.flatpak" | cut -f1)"
        else
            echo "✗ не удалось собрать бандл для $id"
        fi
    else
        echo "✗ не удалось поставить $ref — бандл не собран"
    fi
    echo
done

echo "Готово. Проверить: ls -la installers/*/*.flatpak"
