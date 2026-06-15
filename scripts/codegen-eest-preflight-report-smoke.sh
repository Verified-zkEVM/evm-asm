#!/usr/bin/env bash
# Smoke the host-side 200M resource preflight report on a normal one-row EEST
# manifest selection. This intentionally uses --preflight-report always so the
# decoded dimensions/caps are visible even when the guest halts successfully.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_PREFLIGHT_SMOKE_JOBS:-1}"
STEPS="${EEST_PREFLIGHT_SMOKE_STEPS:-${EEST_STEPS:-200000000}}"

scripts/codegen-eest-stateless-check.sh \
  --limit 1 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --preflight-report always \
  --steps "$STEPS" \
  "$@"

