#!/usr/bin/env bash
# Class-A provided-BAL ratchet (#11183). See scripts/check-bal-class-a-ratchet.py.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
exec python3 scripts/check-bal-class-a-ratchet.py "$@"
