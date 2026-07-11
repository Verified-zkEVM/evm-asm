#!/usr/bin/env bash
# Run the EIP-7825 maximum_gas_refund stateless EEST frontier.
#
# This is currently a diagnostic gate: the selected blocks launch and agree on
# NPR root/tail, but the guest rejects transactions that Python execution-specs
# accepts. Keep the wrapper complete by discovering every matching row in the
# active EEST tag instead of hard-coding today's count.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.0}"
JOBS="${EEST_EIP7825_MAX_REFUND_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7825_MAX_REFUND_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7825_MAX_REFUND_RUN_DIR:-gen-out/eest-eip7825-maximum-gas-refund}"
FILTER="${EEST_EIP7825_MAX_REFUND_FILTER:-maximum_gas_refund}"

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-eip7825-maximum-gas-refund-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count EIP-7825 maximum_gas_refund fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no EIP-7825 maximum_gas_refund stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> EIP-7825 maximum_gas_refund selected: $TOTAL"

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
tail="$(baseline_value "tail match")"

[[ "$selected" == "$TOTAL" ]] || { echo "expected selected=$TOTAL, got ${selected:-missing}" >&2; exit 1; }
[[ "$ran" == "$TOTAL" ]] || { echo "expected ran=$TOTAL, got ${ran:-missing}" >&2; exit 1; }
[[ "${errored:-missing}" == "0" ]] || { echo "expected errored=0, got ${errored:-missing}" >&2; exit 1; }
[[ "${budget:-missing}" == "0" ]] || { echo "expected budget=0, got ${budget:-missing}" >&2; exit 1; }
[[ "$root" == "$TOTAL" ]] || { echo "expected root match=$TOTAL, got ${root:-missing}" >&2; exit 1; }
[[ "$tail" == "$TOTAL" ]] || { echo "expected tail match=$TOTAL, got ${tail:-missing}" >&2; exit 1; }

echo "==> PASS: EIP-7825 maximum_gas_refund frontier launches with root/tail parity ($TOTAL case(s))"
