#!/usr/bin/env bash
# codegen-eest-eip8037-state-pricing-high-gas-check.sh -- full-match all observed
# high-gas EIP-8037 state_gas_pricing rows.
#
# The 2026-06-03 broad EEST log exposed 200M/300M/500M/1G block-gas rows across
# six EIP-8037 pricing fixture files. This wrapper keeps the 1G layout work aimed
# at semantic success for that whole high-gas surface, not just one matrix.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.0}"
JOBS="${EEST_EIP8037_STATE_PRICING_HIGH_GAS_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP8037_STATE_PRICING_HIGH_GAS_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP8037_STATE_PRICING_HIGH_GAS_RUN_DIR:-gen-out/eest-eip8037-state-pricing-high-gas}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP8037_STATE_PRICING_HIGH_GAS_FILTER:-eip8037_state_creation_gas_cost_increase/state_gas_pricing}"
REQUIRED_GAS_LIMITS="${EEST_EIP8037_STATE_PRICING_HIGH_GAS_REQUIRED_GAS_LIMITS:-200000000 300000000 500000000 1000000000}"
REQUIRED_FIXTURES="${EEST_EIP8037_STATE_PRICING_HIGH_GAS_REQUIRED_FIXTURES:-auth_state_gas_scales_with_cpsb.json call_new_account_state_gas_scales_with_cpsb.json create_state_gas_scales_with_cpsb.json pricing_at_various_gas_limits.json selfdestruct_new_beneficiary_scales_with_cpsb.json sstore_refund_scales_with_cpsb.json}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip8037-state-pricing-high-gas-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null
manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"

for fixture in $REQUIRED_FIXTURES; do
  for gas in $REQUIRED_GAS_LIMITS; do
    if ! awk -F'\t' -v fixture="$fixture" -v gas="$gas" \
      '$6 == gas && $7 ~ ("/" fixture "$") { found = 1 } END { exit found ? 0 : 1 }' \
      "$manifest"; then
      echo "required EIP-8037 state_gas_pricing row not selected: $fixture gas_limit=$gas" >&2
      exit 1
    fi
  done
done

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

RUN_MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$RUN_MANIFEST" ]] || { echo "missing run manifest: $RUN_MANIFEST" >&2; exit 1; }

high_selected=0
high_results=0
high_full=0
layout_errors=0
missing_results=0
semantic_failures=0

while IFS=$'\t' read -r label input expected_hex succ_bit input_len gas_limit relpath; do
  fixture="${relpath##*/}"
  case " $REQUIRED_GAS_LIMITS " in
    *" $gas_limit "*) ;;
    *) continue ;;
  esac
  case " $REQUIRED_FIXTURES " in
    *" $fixture "*) ;;
    *) continue ;;
  esac

  high_selected=$((high_selected + 1))
  result="$RUN_DIR/$label.result.tsv"
  if [[ ! -f "$result" ]]; then
    missing_results=$((missing_results + 1))
    continue
  fi
  high_results=$((high_results + 1))
  if IFS=$'\t' read -r status detail < "$result"; then
    if [[ "$status" == "ERROR" && "$detail" == static_layout_gas_limit:* ]]; then
      layout_errors=$((layout_errors + 1))
      echo "layout error remained for gas_limit=$gas_limit: $relpath ($detail)" >&2
    elif [[ "$status" == "OK" && "${detail:0:210}" == "${expected_hex:0:210}" ]]; then
      high_full=$((high_full + 1))
    else
      semantic_failures=$((semantic_failures + 1))
      echo "semantic mismatch for gas_limit=$gas_limit: $relpath (status=$status)" >&2
    fi
  fi
done < "$RUN_MANIFEST"

if [[ "$high_selected" -eq 0 ]]; then
  echo "no required high-gas EIP-8037 state_gas_pricing rows selected" >&2
  exit 1
fi
if [[ "$high_results" -eq 0 ]]; then
  echo "no required high-gas EIP-8037 state_gas_pricing rows produced results" >&2
  exit 1
fi
if [[ "$missing_results" -ne 0 ]]; then
  echo "missing result files for $missing_results required high-gas EIP-8037 row(s)" >&2
  exit 1
fi
if [[ "$layout_errors" -ne 0 ]]; then
  echo "found $layout_errors high-gas EIP-8037 layout error(s)" >&2
  exit 1
fi
if [[ "$semantic_failures" -ne 0 ]]; then
  echo "found $semantic_failures high-gas EIP-8037 semantic failure(s)" >&2
  exit 1
fi
if [[ "$high_full" -ne "$high_selected" ]]; then
  echo "only $high_full of $high_selected required high-gas EIP-8037 row(s) full-matched" >&2
  exit 1
fi

echo "==> PASS: EIP-8037 high-gas state_gas_pricing rows full-match selected=$high_selected ran=$high_results full=$high_full layout_errors=0"
