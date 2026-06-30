#!/usr/bin/env bash
# Restore: remove DISABLED markers and re-instate .holds
set -eo pipefail
for f in $(find src/main/scala/v1/chapter5 src/main/scala/v1/chapter6 -name "*.scala" | sort); do
  sed -i '' '/\/\/ DISABLED/d' "$f"
done
echo "Restored."
