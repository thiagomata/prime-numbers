#!/usr/bin/env bash

just_log() {
  local recipe="$1"
  local base_dir="${2:-$(pwd)}"
  local log_dir="$base_dir/logs"
  local log_file="$log_dir/$recipe.log"
  local overall_log="$log_dir/all.log"

  mkdir -p "$log_dir"

  # Append start marker, then redirect all output to both terminal and log files
  {
    echo
    echo "===== just $recipe started at $(date '+%Y-%m-%d %H:%M:%S %z') ====="
    echo "cwd: $(pwd)"
  } >> "$log_file" "$overall_log"

  # Tee stdout/stderr to terminal (as-is) and append to log files
  exec 3>&1 4>&2
  exec > >(tee -a "$log_file" "$overall_log") 2>&1
}
