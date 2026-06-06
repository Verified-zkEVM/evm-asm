#!/usr/bin/env bash
# Run the BAL replay frontier at the default 64 KiB block_state_root witness
# cap. This locks in the current measured progress: the smaller
# withdrawal-request case full-matches and only the large 170 KiB witness case
# remains a conservative miss.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_BAL_REPLAY_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_BAL_REPLAY_STEPS:-${EEST_STEPS:-1000000000}}"
CAP_ARGS=()
CAP_NOTE="default"
if [[ -n "${EEST_BSR_WITNESS_CAP:-}" ]]; then
  CAP_ARGS=(--bsr-witness-cap "$EEST_BSR_WITNESS_CAP")
  CAP_NOTE="$EEST_BSR_WITNESS_CAP"
fi

scripts/codegen-eest-stateless-check.sh \
  --filter withdrawal_requests \
  --skip 83 \
  --limit 20 \
  --jobs "$JOBS" \
  --quiet-passes \
  "${CAP_ARGS[@]}" \
  --steps "$STEPS" \
  --min-full 19 \
  "$@"

echo "==> PASS: BAL replay frontier reaches 19/20 full matches with bsr_witness_cap=$CAP_NOTE"
