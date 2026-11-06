#!/usr/bin/env bash
# Запуск Minecraft (Legacy Launcher) без окна установщика: ./play.sh
RUN_SH="$HOME/.local/share/KoderLab/apps/legacy_launcher/run.sh"
JAR="$HOME/.local/share/KoderLab/apps/legacy_launcher/LegacyLauncher.jar"

if [ -f "$RUN_SH" ]; then
    exec bash "$RUN_SH" "$@"
elif [ -f "$JAR" ] && command -v java >/dev/null 2>&1; then
    cd "$(dirname "$JAR")" && exec java -jar "$JAR" "$@"
fi
echo "Лаунчер не установлен. Запустите установщик: bash start.sh"
exit 1
