#!/usr/bin/env bash
# codegen-eest-eip8037-layout-check.sh -- high-gas EIP-8037 launch coverage.
#
# This is a regression check for the 1G static BSR/BAL layout and the
# largest-gas EIP-8037 pricing rows. It selects the
# pricing_at_various_gas_limits matrix and asserts that the high-gas rows
# observed in EEST logs launch through ziskemu and full-match the expected
# 105-byte stateless verdict.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
JOBS="${EEST_EIP8037_LAYOUT_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP8037_LAYOUT_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP8037_LAYOUT_RUN_DIR:-gen-out/eest-eip8037-layout}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP8037_LAYOUT_FILTER:-pricing_at_various_gas_limits}"
REQUIRED_GAS_LIMITS="${EEST_EIP8037_LAYOUT_REQUIRED_GAS_LIMITS:-200000000 300000000 500000000 1000000000}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip8037-layout-count"
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

for gas in $REQUIRED_GAS_LIMITS; do
  if ! awk -F'\t' -v gas="$gas" '$6 == gas { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
    echo "required EIP-8037 gas limit not selected by $FILTER: $gas" >&2
    exit 1
  fi
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
  case " $REQUIRED_GAS_LIMITS " in
    *" $gas_limit "*) ;;
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
  echo "no required high-gas EIP-8037 rows selected" >&2
  exit 1
fi
if [[ "$high_results" -eq 0 ]]; then
  echo "no required high-gas EIP-8037 rows produced results" >&2
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

echo "==> PASS: EIP-8037 high-gas rows full-match selected=$high_selected ran=$high_results full=$high_full layout_errors=0"
