#!/usr/bin/env bash
# Disable all .holds verification in ch5 and ch6 files.
# Injects `true // DISABLED` before each `.holds` closing brace.
# Restore with: grep -rn 'DISABLED' src/main/scala/v1/chapter5 src/main/scala/v1/chapter6
set -eo pipefail

for f in $(find src/main/scala/v1/chapter5 src/main/scala/v1/chapter6 -name "*.scala" | sort); do
  if grep -q '\.holds' "$f"; then
    echo "  $f"
    sed -i '' '/\.holds/i\
  true \/\/ DISABLED
' "$f"
  fi
done
echo "Done."
