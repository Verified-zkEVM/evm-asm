#!/usr/bin/env bash
# Run the EEST stateless-guest regression window immediately after
# random_statetest in zkevm@v0.4.0 fixture order.
#
# The preceding random_statetest class starts at skip 16582 and has 503 blocks;
# this gate starts at 17085 and covers the next 1000 selected stateless blocks.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_POST_RANDOM_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_POST_RANDOM_STEPS:-${EEST_STEPS:-1000000000}}"

scripts/codegen-eest-stateless-check.sh \
  --skip 17085 \
  --limit 1000 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --min-full 1000 \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: post-random EEST window full-matches"
