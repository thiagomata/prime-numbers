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

  mkdir -p "$log_dir"
  started_at="$(date '+%Y-%m-%d %H:%M:%S %z')"

  mkfifo "$fifo"
  tee -a "$command_log" -a "$overall_log" < "$fifo" &
  tee_pid="$!"

  exec 3>&1 4>&2
  exec > "$fifo" 2>&1

  rm -f "$fifo"
  trap 'status=$?; exec 1>&3 2>&4; wait '"$tee_pid"' 2>/dev/null || true; exit "$status"' EXIT

  echo
  echo "===== just $recipe started at $started_at ====="
  echo "cwd: $(pwd)"
}
