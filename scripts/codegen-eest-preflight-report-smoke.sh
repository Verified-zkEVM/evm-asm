#!/usr/bin/env bash
# Smoke the host-side 200M resource preflight report on a normal one-row EEST
# manifest selection. This intentionally uses --preflight-report always so the
# decoded dimensions/caps are visible even when the guest halts successfully.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_PREFLIGHT_SMOKE_JOBS:-1}"
STEPS="${EEST_PREFLIGHT_SMOKE_STEPS:-${EEST_STEPS:-200000000}}"

# GH #11737: the harness now exits non-zero when a row FAILs. This smoke checks
# that the PREFLIGHT REPORT renders, not that the selected row conforms -- its
# header says the decoded dimensions must be visible "even when the guest halts
# successfully", and equally when it does not. Under `set -e` a failing row would
# otherwise abort this script and hide the very report it exists to smoke, so the
# opt-out is deliberate here and must not be copied to conformance callers.
scripts/codegen-eest-stateless-check.sh \
  --limit 1 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --preflight-report always \
  --exit-zero-on-failures \
  --steps "$STEPS" \
  "$@"

