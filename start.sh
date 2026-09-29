#!/usr/bin/env bash
# Запуск: ./start.sh   (без sudo)
cd "$(dirname "$0")" || exit 1

for c in /usr/bin/python3 /usr/bin/python3.12 /usr/bin/python3.11 \
         /usr/bin/python3.10 /usr/bin/python3.9 python3; do
    p="$(command -v "$c" 2>/dev/null)" || continue
    [ -x "$p" ] || continue
    if "$p" -c "import PyQt5.QtWidgets" >/dev/null 2>&1; then exec "$p" main.py "$@"; fi
done

echo "Не найден Python с библиотекой PyQt5. Установите её:"
echo "  ROSA:            sudo dnf install python3-qt5"
echo "  Альт / М ОС:     sudo apt-get install python3-module-PyQt5"
echo "  Astra / Debian:  sudo apt-get install python3-pyqt5"
exit 1
