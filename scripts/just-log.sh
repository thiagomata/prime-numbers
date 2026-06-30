#!/usr/bin/env bash

just_log() {
  local recipe="$1"
  local base_dir="${2:-$(pwd)}"
  local log_dir="$base_dir/logs/just"
  local command_log="$log_dir/$recipe.log"
  local overall_log="$log_dir/all.log"
  local fifo="$log_dir/.$recipe.$$.fifo"
  local tee_pid
  local started_at
  local restore_wrap=""

  mkdir -p "$log_dir"
  started_at="$(date '+%Y-%m-%d %H:%M:%S %z')"

  mkfifo "$fifo"
  exec 3>&1 4>&2
  if [[ -t 3 ]] && command -v tput >/dev/null 2>&1; then
    tput rmam >&3 2>/dev/null && restore_wrap="yes"
  fi
  while IFS= read -r line || [[ -n "$line" ]]; do
    printf '%s\n' "$line" >&3
    printf '[%s] %s\n' "$(date '+%Y-%m-%d %H:%M:%S %z')" "$line"
  done < "$fifo" | tee -a "$command_log" "$overall_log" > /dev/null &
  tee_pid="$!"

  exec > "$fifo" 2>&1

  rm -f "$fifo"
  trap 'status=$?; if [[ -n "'"$restore_wrap"'" ]]; then tput smam >&3 2>/dev/null || true; fi; exec 1>&3 2>&4; wait '"$tee_pid"' 2>/dev/null || true; exit "$status"' EXIT

  echo
  echo "===== just $recipe started at $started_at ====="
  echo "cwd: $(pwd)"
}
