#!/usr/bin/env bash
set -euo pipefail

BASE_DIR="$(cd "$(dirname "$0")/.." && pwd)"

# Keep this matcher narrow enough to avoid unrelated Java work, but broad
# enough to catch orphaned Stainless launcher, Java verifier, and Z3 workers.
# The bracketed first letter keeps pgrep from matching this script's own
# command line.
PATTERNS=(
  "[s]tainless-dotty-standalone"
  "[s]tainless.*--batched"
  "[j]ava.*stainless"
  "[j]ava.*${BASE_DIR}"
  "[s]mt-z3"
  "[/]z3([[:space:]]|$)"
  "[[:space:]]z3([[:space:]]|$)"
  "[s]bt.*${BASE_DIR}"
)

PIDS=()

add_pid() {
  local pid="$1"

  [[ -z "$pid" ]] && return 0
  [[ "$pid" == "$$" || "$pid" == "$PPID" ]] && return 0

  for existing in "${PIDS[@]:-}"; do
    [[ "$existing" == "$pid" ]] && return 0
  done

  PIDS+=("$pid")
}

for pattern in "${PATTERNS[@]}"; do
  while IFS= read -r pid; do
    add_pid "$pid"
  done < <(pgrep -f "$pattern" 2>/dev/null || true)
done

if [[ "${#PIDS[@]}" -eq 0 ]]; then
  echo "No Stainless/Z3 verification processes found."
  exit 0
fi

echo "Stopping verification processes:"
for pid in "${PIDS[@]}"; do
  runtime=$(ps -o etime= -p "$pid" 2>/dev/null | tr -d ' ' || echo "?")
  echo "  PID $pid (running $runtime)"
  kill -TERM "$pid" 2>/dev/null || true
done

sleep 2

STILL_RUNNING=()
for pid in "${PIDS[@]}"; do
  if kill -0 "$pid" 2>/dev/null; then
    STILL_RUNNING+=("$pid")
  fi
done

if [[ "${#STILL_RUNNING[@]}" -gt 0 ]]; then
  echo "Force-stopping stubborn verification processes:"
  for pid in "${STILL_RUNNING[@]}"; do
    runtime=$(ps -o etime= -p "$pid" 2>/dev/null | tr -d ' ' || echo "?")
    echo "  PID $pid (still alive after $runtime)"
    kill -KILL "$pid" 2>/dev/null || true
  done
fi

echo "Verification process cleanup complete."
