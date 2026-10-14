#!/usr/bin/env bash
# Offline verification and bounded checks; run --help for arguments/overrides.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd -- "$ROOT"
# One lock covers configuration and every root, including paths containing spaces.
# Keep help available without waiting for a running proof check.
if [[ "${1:-}" == --help || "${1:-}" == -h ]]; then
  exec python3 "$ROOT/tools/configure.py" "$@"
fi
exec flock -w 1200 -- "${DELOOP_LOCK:-/tmp/delooping-agda.lock}" \
  python3 "$ROOT/tools/configure.py" "$@"
