#!/usr/bin/env bash
# Cross-registry verdict gate (GH #11294): a routine with a witnessed
# RoutineEntry in EvmAsm/Progress/Routines.lean must not carry verdict
# .unproven in EvmAsm/Progress/Correspondence.lean. Source-level twin of the
# kernel-checked `witnessed_not_unproven` theorem in Routines.lean, so the
# disagreement fails in source-checks in seconds rather than an hour into the
# build. See scripts/check_registry_crosscheck.py for the mechanism.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check_registry_crosscheck.py "$@"
