#!/usr/bin/env bash
# Run the EIP-150 SELFDESTRUCT-to-system-contract EEST frontier.
#
# This is currently a diagnostic gate: some rows still false-reject on the
# successful_validation bit, but the guest launches and preserves root/tail
# parity. Count rows from the active EEST tag so future fixture additions are
# covered automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_EIP150_SELFDESTRUCT_SYSTEM_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP150_SELFDESTRUCT_SYSTEM_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP150_SELFDESTRUCT_SYSTEM_RUN_DIR:-gen-out/eest-eip150-selfdestruct-system}"
FILTER="${EEST_EIP150_SELFDESTRUCT_SYSTEM_FILTER:-selfdestruct_to_system_contract}"

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-eip150-selfdestruct-system-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count EIP-150 SELFDESTRUCT system-contract fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no EIP-150 SELFDESTRUCT system-contract stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> EIP-150 SELFDESTRUCT system-contract selected: $TOTAL"

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

echo "==> PASS: EIP-150 SELFDESTRUCT system-contract frontier launches with root/tail parity ($TOTAL case(s))"
