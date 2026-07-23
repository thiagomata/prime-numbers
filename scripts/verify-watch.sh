#!/usr/bin/env bash
set -euo pipefail

BASE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
LOG_DIR="$BASE_DIR/logs"
LOG_FILE="$LOG_DIR/verify-watch.log"
ALL_LOG="$LOG_DIR/all.log"

# Parse focus argument
FOCUS="${1:-}"

# Setup log files
mkdir -p "$LOG_DIR"
rm -f "$LOG_FILE"

# Timestamping logger: writes to terminal + both log files
log_pipe() {
    while IFS= read -r line; do
        ts="$(date '+%Y-%m-%d %H:%M:%S %z')"
        printf '[%s] %s\n' "$ts" "$line"
        printf '[%s] %s\n' "$ts" "$line" >> "$LOG_FILE"
        printf '[%s] %s\n' "$ts" "$line" >> "$ALL_LOG"
    done
}

log_msg() {
    local ts
    ts="$(date '+%Y-%m-%d %H:%M:%S %z')"
    echo "[$ts] $1" | tee -a "$LOG_FILE" "$ALL_LOG"
}

# Kill any running verification processes
bash "$BASE_DIR/scripts/verify-stop.sh"

# Java is set up by the Justfile recipe (sdk installed sdk use) before exec

STAINLESS_GLOB=$(ls -d "$BASE_DIR"/stainless-dotty-standalone-*/stainless 2>/dev/null | head -1)
STAINLESS="${STAINLESS_GLOB:-$BASE_DIR/stainless-dotty-standalone-0.9.8.8/stainless}"
Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"
TIMEOUT=300

FUNC_FILTER=()
[[ -n "$FOCUS" ]] && FUNC_FILTER=(--functions="$FOCUS")

LAST_FILE_LIST=""
WATCH_PID=""
MONITOR_PID=""
RESTART_COUNT=0

# Temp file for monitor<->loop communication
RESTART_FLAG=$(mktemp)
trap 'rm -f "$RESTART_FLAG"' EXIT

cleanup() {
    log_msg "Shutting down watch (restarts: $RESTART_COUNT)"
    [[ -n "${MONITOR_PID:-}" ]] && kill "$MONITOR_PID" 2>/dev/null || true
    [[ -n "${WATCH_PID:-}" ]] && kill "$WATCH_PID" 2>/dev/null || true
    wait 2>/dev/null || true
    log_msg "===== just verify-watch stopped ====="
    exit 0
}
trap cleanup INT TERM

log_msg "===== just verify-watch started ====="
[[ -n "$FOCUS" ]] && log_msg "  focus: $FOCUS"

while true; do
    FILE_LIST=$(bash "$BASE_DIR/scripts/find-src.sh")
    FILE_COUNT=$(echo "$FILE_LIST" | wc -w | tr -d ' ')

    if [[ "$FILE_LIST" != "$LAST_FILE_LIST" ]]; then
        log_msg "Watching $FILE_COUNT Scala files (restart #$RESTART_COUNT)"
        LAST_FILE_LIST="$FILE_LIST"
    fi

    echo "0" > "$RESTART_FLAG"

    cd "$BASE_DIR"
    DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
    JAVA_OPTS="-Xmx16g -Djava.library.path=$Z3_LIB" \
    "$STAINLESS" --watch --timeout="$TIMEOUT" ${FUNC_FILTER[@]+"${FUNC_FILTER[@]}"} $FILE_LIST 2>&1 | log_pipe &
    WATCH_PID=$!

    # New-file monitor: polls for additions to src/main/scala/
    (
        while kill -0 "$WATCH_PID" 2>/dev/null; do
            sleep 2
            CURRENT=$(bash "$BASE_DIR/scripts/find-src.sh" 2>/dev/null || true)
            if [[ "$CURRENT" != "$LAST_FILE_LIST" ]]; then
                echo "1" > "$RESTART_FLAG"
                kill "$WATCH_PID" 2>/dev/null || true
                exit 0
            fi
        done
    ) &
    MONITOR_PID=$!

    # Wait for watch pipeline to exit
    wait "$WATCH_PID" 2>/dev/null || true

    # Kill monitor
    kill "$MONITOR_PID" 2>/dev/null || true
    wait "$MONITOR_PID" 2>/dev/null || true

    # Check if restart was requested by monitor
    NEEDS_RESTART=$(cat "$RESTART_FLAG")
    if [[ "$NEEDS_RESTART" == "1" ]]; then
        log_msg "Restarting watch with updated file list..."
        RESTART_COUNT=$((RESTART_COUNT + 1))
        sleep 1
        continue
    fi

    # Normal exit (Ctrl+C or stainless exited cleanly)
    break
done

cleanup
