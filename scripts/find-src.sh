#!/usr/bin/env bash
# Helper script: prints all scala source files sorted, space-separated
BASE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
find "$BASE_DIR/src/main/scala" -name "*.scala" | sort | tr '\n' ' '
