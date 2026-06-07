#!/usr/bin/env bash
# Probe the large remaining EIP-7002 withdrawal-request BAL replay frontier.
#
# The default 64 KiB block_state_root witness cap conservatively misses this
# fixture. Raising the experimental cap to 256 KiB exposes the next blocker
# directly: the guest currently exits before completing the replay.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_BAL_LARGE_WITNESS_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_BAL_LARGE_WITNESS_STEPS:-${EEST_STEPS:-2000000000}}"
BSR_WITNESS_CAP="${EEST_BSR_WITNESS_CAP:-262144}"

scripts/codegen-eest-stateless-check.sh \
  --filter withdrawal_requests \
  --skip 87 \
  --limit 1 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --bsr-witness-cap "$BSR_WITNESS_CAP" \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: BAL large-witness frontier probe completed with bsr_witness_cap=$BSR_WITNESS_CAP"
