#!/usr/bin/env bash
# Build modules with lake (writes .olean files), serialized by a lock file.
# usage: bash scripts/build.sh [Module.Name ...]   (no argument: the default targets)
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.." || exit 2
exec 9>/tmp/zeta-window-lean-build.lock
flock 9
timeout "${TIMEOUT:-3600}" lake build "$@" 2>&1 | tail -c 150000
echo "---"
echo "exit=${PIPESTATUS[0]}"
