#!/usr/bin/env bash
set -eo pipefail

BASE_DIR="$(cd "$(dirname "$0")/.." && pwd)"

# Parse arguments: chapters (digits) then optional --functions=<pattern>
CHAPTERS=""
FOCUS=""
for arg in "$@"; do
  if [[ "$arg" =~ ^[0-9]+$ ]]; then
    CHAPTERS="$CHAPTERS $arg"
  elif [[ "$arg" == --functions=* ]]; then
    FOCUS="${arg#--functions=}"
  fi
done
CHAPTERS="${CHAPTERS# }"
CHAPTERS="${CHAPTERS:-all}"

source "$HOME/.sdkman/bin/sdkman-init.sh" 2>/dev/null || true
sdk install java 21.0.7-zulu > /dev/null 2>&1 || true
sdk use java 21.0.7-zulu > /dev/null 2>&1 || true

bash "$BASE_DIR/scripts/verify-stop.sh"

STAINLESS="$BASE_DIR/stainless-dotty-standalone-0.9.8.8/stainless"
Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"

# Collect source files: all chapters up to the highest requested
if [[ "$CHAPTERS" == "all" ]]; then
  SRC_FILES=$(find "$BASE_DIR/src/main/scala" -name "*.scala" | sort | tr '\n' ' ')
else
  max_ch=0
  for ch in $CHAPTERS; do
    if [[ "$ch" -gt "$max_ch" ]]; then max_ch=$ch; fi
  done
  SRC_FILES=""
  for ch in $(seq 1 "$max_ch"); do
    ch_files=$(find "$BASE_DIR/src/main/scala" -path "*/chapter${ch}/*" -name "*.scala" | sort | tr '\n' ' ')
    SRC_FILES="$SRC_FILES $ch_files"
  done
fi

# Auto-focus: if chapters given and no explicit focus, verify only the highest chapter
if [[ -z "$FOCUS" && "$CHAPTERS" != "all" ]]; then
  HIGHEST_CH=$(echo "$CHAPTERS" | tr ' ' '\n' | sort -n | tail -1)
  FOCUS="v1.chapter${HIGHEST_CH}._"
  echo "Auto-focus: verifying only ch${HIGHEST_CH} (dep: ch1-$((HIGHEST_CH-1)))" >&2
fi

LOG_TAG=$(echo "$CHAPTERS" | tr ' ' '-')
if [[ -n "$FOCUS" ]]; then
  FOCUS_TAG=$(echo "$FOCUS" | tr -c '[:alnum:]_' '-' | sed 's/-\+/-/g; s/^-//; s/-$//')
LOG_FILE="$BASE_DIR/logs/verify-ch-$LOG_TAG-$FOCUS_TAG.log"
else
  LOG_FILE="$BASE_DIR/logs/verify-ch-$LOG_TAG.log"
fi
mkdir -p "$BASE_DIR/logs"
echo "Stainless log: $LOG_FILE" >&2
rm -f "$LOG_FILE"

FOCUS_FLAG=()
if [[ -n "$FOCUS" ]]; then
  FOCUS_FLAG=(--functions="$FOCUS")
fi

DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
JAVA_OPTS="-Xmx16g -Djava.library.path=$Z3_LIB" \
"$STAINLESS" \
  --timeout=300 --cache-dir="$BASE_DIR/.stainless-cache" \
  "${FOCUS_FLAG[@]}" \
  $SRC_FILES \
  2>&1 | tee "$LOG_FILE"
