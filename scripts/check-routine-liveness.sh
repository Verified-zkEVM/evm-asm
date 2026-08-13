#!/usr/bin/env bash
# Routine-liveness gate (GH #11303): every in-image routine that carries a
# theorem (_eq_prog via MANIFEST.tsv, or a Progress/Routines.lean row) must be
# referenced somewhere in emitted text or present in the guest symbol census.
# Absent-from-image manifest routines are classified separately. Pure source scan,
# seconds, no build. See scripts/check_routine_liveness.py for the mechanism
# and its derived absent-from-image/in-image classification.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check_routine_liveness.py "$@"
