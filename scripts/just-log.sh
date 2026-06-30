#!/usr/bin/env bash

just_log() {
  local recipe="$1"
  local base_dir="${2:-$(pwd)}"
  local args="$3"
  local log_dir="$base_dir/logs"
  local log_file="$log_dir/$recipe.log"
  local overall_log="$log_dir/all.log"

  mkdir -p "$log_dir"

  # Append start marker, then redirect all output to both terminal and log files
  local start_timestamp
  start_timestamp="$(date '+%Y-%m-%d %H:%M:%S %z')"
  {
    echo
    echo "[$start_timestamp] ===== just $recipe started ====="
    if [[ -n "$args" ]]; then
      echo "[$start_timestamp]   args: $args"
    fi
    echo "[$start_timestamp]   cwd: $(pwd)"
    echo "[$start_timestamp]   log: $log_file"
    echo "[$start_timestamp]   overall log: $overall_log"
  } | tee -a "$log_file" "$overall_log"

  # Keep terminal output unchanged, but timestamp every saved log line.
  exec 3>&1 4>&2
  local restore_wrap=0
  if [[ -t 1 ]] && command -v tput >/dev/null 2>&1; then
    if tput rmam 2>/dev/null; then
      restore_wrap=1
    fi
  fi
  local fifo_dir="${TMPDIR:-/tmp}/prime-just-log.$$"
  local fifo="$fifo_dir/output"
  mkdir -p "$fifo_dir"
  mkfifo "$fifo"
  trap 'if [[ "$restore_wrap" == "1" ]]; then tput smam 2>/dev/null || true; fi; rm -f "$fifo"; rmdir "$fifo_dir" 2>/dev/null || true' EXIT

  awk -v log_file="$log_file" -v overall_log="$overall_log" '
      {
        cmd = "date \"+%Y-%m-%d %H:%M:%S %z\""
        cmd | getline timestamp
        close(cmd)

        print
        print "[" timestamp "] " $0 >> log_file
        print "[" timestamp "] " $0 >> overall_log

        fflush()
        fflush(log_file)
        fflush(overall_log)
      }
    ' < "$fifo" >&3 &

  exec > "$fifo" 2>&1
}
