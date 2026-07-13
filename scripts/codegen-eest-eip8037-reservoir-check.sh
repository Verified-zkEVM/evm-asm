#!/usr/bin/env bash
# Run the EIP-8037 state-gas reservoir cumulative-limit EEST frontier.
#
# This is a full-match gate for the high-gas cumulative-reservoir row.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.1}"
JOBS="${EEST_EIP8037_RESERVOIR_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP8037_RESERVOIR_STEPS:-${EEST_STEPS:-12000000000}}"
RUN_DIR="${EEST_EIP8037_RESERVOIR_RUN_DIR:-gen-out/eest-eip8037-reservoir}"
FILTER="${EEST_EIP8037_RESERVOIR_FILTER:-block_2d_gas_valid_when_cumulative_exceeds_limit}"

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-eip8037-reservoir-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count EIP-8037 state-reservoir fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no EIP-8037 state-reservoir stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> EIP-8037 state-reservoir selected: $TOTAL"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$TOTAL" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures "$TOTAL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

BASELINE="$RUN_DIR/eest-baseline.txt"
[[ -s "$BASELINE" ]] || { echo "missing baseline: $BASELINE" >&2; exit 1; }

baseline_value() {
  local label="$1"
  awk -F: -v label="$label" \
    '$1 ~ label { gsub(/^[ \t]+|[ \t]+$/, "", $2); split($2, a, /[ \t]+/); print a[1]; exit }' \
    "$BASELINE"
}

selected="$(baseline_value "selected")"
ran="$(baseline_value "ran")"
errored="$(baseline_value "errored")"
budget="$(baseline_value "budget")"
root="$(baseline_value "root match")"
succ="$(baseline_value "succ match")"
tail="$(baseline_value "tail match")"
full="$(baseline_value "full match")"
fail="$(baseline_value "fail")"

[[ "$selected" == "$TOTAL" ]] || { echo "expected selected=$TOTAL, got ${selected:-missing}" >&2; exit 1; }
[[ "$ran" == "$TOTAL" ]] || { echo "expected ran=$TOTAL, got ${ran:-missing}" >&2; exit 1; }
[[ "${errored:-missing}" == "0" ]] || { echo "expected errored=0, got ${errored:-missing}" >&2; exit 1; }
[[ "${budget:-missing}" == "0" ]] || { echo "expected budget=0, got ${budget:-missing}" >&2; exit 1; }
[[ "$root" == "$TOTAL" ]] || { echo "expected root match=$TOTAL, got ${root:-missing}" >&2; exit 1; }
[[ "$succ" == "$TOTAL" ]] || { echo "expected succ match=$TOTAL, got ${succ:-missing}" >&2; exit 1; }
[[ "$tail" == "$TOTAL" ]] || { echo "expected tail match=$TOTAL, got ${tail:-missing}" >&2; exit 1; }
[[ "$full" == "$TOTAL" ]] || { echo "expected full match=$TOTAL, got ${full:-missing}" >&2; exit 1; }
[[ "${fail:-missing}" == "0" ]] || { echo "expected fail=0, got ${fail:-missing}" >&2; exit 1; }

echo "==> PASS: EIP-8037 state-reservoir frontier full-matched ($TOTAL case(s))"
