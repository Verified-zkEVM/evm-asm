#!/usr/bin/env bash
# Regression gate for the Amsterdam exp_power256 stateless fixture. This case
# exercises an opcode-heavy state-test path while still requiring the full
# 105-byte stateless output to match.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_EXP_POWER256_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_EXP_POWER256_STEPS:-${EEST_STEPS:-1000000000}}"

scripts/codegen-eest-stateless-check.sh \
  --filter exp_power256 \
  --limit 1 \
  --jobs "$JOBS" \
  --quiet-passes \
  --steps "$STEPS" \
  --min-full 1 \
  "$@"

echo "==> PASS: exp_power256 reaches 1/1 full match"
