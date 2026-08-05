#!/usr/bin/env bash
# #11520: code_at_header_state_root must pair with EMPTY_CODE_HASH check.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
exec python3 "$ROOT/scripts/check-code-preimage-empty-hash.py" "$@"
