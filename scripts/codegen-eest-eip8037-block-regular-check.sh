#!/usr/bin/env bash
# codegen-eest-eip8037-block-regular-check.sh -- focused EIP-8037 diagnostic.
#
# Regression for the block_regular_gas_limit rows. The guest must reject the
# row whose parsed transactions exceed the execution-spec block gas reservoir.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_EIP8037_BLOCK_REGULAR_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP8037_BLOCK_REGULAR_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP8037_BLOCK_REGULAR_RUN_DIR:-gen-out/eest-eip8037-block-regular}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP8037_BLOCK_REGULAR_FILTER:-state_gas_reservoir/block_regular_gas_limit.json}"
REQUIRED="eip8037_state_creation_gas_cost_increase/state_gas_reservoir/block_regular_gas_limit.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip8037-block-regular-count"
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

if [[ "$COUNT" -ne 2 ]]; then
  echo "expected two EIP-8037 block_regular_gas_limit rows, selected $COUNT" >&2
  exit 1
fi
if ! awk -F'\t' -v required="$REQUIRED" '$7 ~ required { found += 1 } END { exit found == 2 ? 0 : 1 }' "$manifest"; then
  echo "required EIP-8037 fixture rows not selected by $FILTER: $REQUIRED" >&2
  exit 1
fi

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures "$COUNT" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

baseline="$RUN_DIR/eest-baseline.txt"
[[ -s "$baseline" ]] || { echo "missing EEST baseline: $baseline" >&2; exit 1; }

baseline_value() {
  local label="$1"
  awk -F: -v label="$label" '$1 ~ label { gsub(/^[ \t]+|[ \t]+$/, "", $2); split($2, a, /[ \t]+/); print a[1]; exit }' "$baseline"
}

selected="$(baseline_value "selected")"
errored="$(baseline_value "errored")"
budget="$(baseline_value "budget")"
ran="$(baseline_value "ran")"
full="$(baseline_value "full match")"
root="$(baseline_value "root match")"
succ="$(baseline_value "succ match")"
tail="$(baseline_value "tail match")"
fail="$(baseline_value "fail")"

[[ "$selected" == "2" ]] || { echo "expected selected=2, got $selected" >&2; exit 1; }
[[ "$errored" == "0" ]] || { echo "expected errored=0, got $errored" >&2; exit 1; }
[[ "$budget" == "0" ]] || { echo "expected budget=0, got $budget" >&2; exit 1; }
[[ "$ran" == "2" ]] || { echo "expected ran=2, got $ran" >&2; exit 1; }
[[ "$full" == "2" ]] || { echo "expected full=2, got $full" >&2; exit 1; }
[[ "$root" == "2" ]] || { echo "expected root=2, got $root" >&2; exit 1; }
[[ "$succ" == "2" ]] || { echo "expected succ=2, got $succ" >&2; exit 1; }
[[ "$tail" == "2" ]] || { echo "expected tail=2, got $tail" >&2; exit 1; }
[[ "$fail" == "0" ]] || { echo "expected fail=0, got $fail" >&2; exit 1; }

echo "==> PASS: EIP-8037 block-regular-gas-limit rows full-matched"
