#!/usr/bin/env bash
# Run the current BAL replay frontier window around EIP-7002 withdrawal-request
# cases in zkevm@v0.4.0 fixture order.
#
# This gate filters to withdrawal-request fixtures, starts at local skip 83,
# and covers the single-block request cluster. It stops after the two known
# conservative misses; with parallel jobs, the number of completed passes before
# the stop point depends on scheduling.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_BAL_REPLAY_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_BAL_REPLAY_STEPS:-${EEST_STEPS:-1000000000}}"

scripts/codegen-eest-stateless-check.sh \
  --filter withdrawal_requests \
  --skip 83 \
  --limit 20 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 2 \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: BAL replay frontier reached the known conservative misses"
