#!/usr/bin/env bash
# codegen-eest-eip8037-pricing-various-gas-check.sh -- EIP-8037 state gas pricing gate.
#
# The default selection covers every stateless row selected by the
# pricing_at_various_gas_limits fixture. The limit is derived from the converted
# manifest so future gas-limit rows for that fixture are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EIP8037_PRICING_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_EIP8037_PRICING_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP8037_PRICING_RUN_DIR:-gen-out/eest-eip8037-pricing-various-gas}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP8037_PRICING_FILTER:-blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_pricing/pricing_at_various_gas_limits.json}"
LIMIT_OVERRIDE="${EEST_EIP8037_PRICING_LIMIT:-}"
REQUIRED="blockchain_tests/for_amsterdam/amsterdam/eip8037_state_creation_gas_cost_increase/state_gas_pricing/pricing_at_various_gas_limits.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip8037-pricing-various-gas-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null

manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for EIP-8037 pricing filter: $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"
LIMIT="${LIMIT_OVERRIDE:-$COUNT}"

if ! awk -F'\t' -v required="$REQUIRED" '$7 == required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
  echo "required EIP-8037 pricing fixture not selected by $FILTER: $REQUIRED" >&2
  exit 1
fi

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$LIMIT" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-8037 pricing gas-limit rows full-matched selected=$LIMIT of available=$COUNT"
