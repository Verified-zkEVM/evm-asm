#!/usr/bin/env bash
# Run the fourth EEST stateless-guest regression window after random_statetest
# in zkevm@v0.4.0 fixture order.
#
# This gate starts at skip 20085 and covers 1000 selected stateless blocks.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_POST_RANDOM_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_POST_RANDOM_STEPS:-${EEST_STEPS:-1000000000}}"

scripts/codegen-eest-stateless-check.sh \
  --skip 20085 \
  --limit 1000 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 5 \
  --min-full 1000 \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: post-random EEST window 4 full-matches"
