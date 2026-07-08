#!/usr/bin/env bash
# codegen-eest-eip7002-withdrawal-fee-increments-check.sh -- focused EIP-7002 b44 gate.
#
# Protects the multiple_block_fee_increments__b44 row where system-storage
# side-capture failure used to false-reject before request-hash completion.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_EIP7002_WITHDRAWAL_FEE_JOBS:-${EEST_JOBS:-1}}"
STEPS="${EEST_EIP7002_WITHDRAWAL_FEE_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7002_WITHDRAWAL_FEE_RUN_DIR:-gen-out/eest-eip7002-withdrawal-fee-increments}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="withdrawal_requests"
TARGET="multiple_block_fee_increments__b44"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7002-withdrawal-fee-increments-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  --verify-input-parity \
  >/dev/null

manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for $FILTER" >&2; exit 1; }

row="$(awk -F'\t' -v target="$TARGET" '$1 ~ target { print NR; exit }' "$manifest")"
[[ -n "$row" ]] || { echo "target row not found in $FILTER manifest: $TARGET" >&2; exit 1; }
skip=$((row - 1))

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --skip "$skip" \
  --limit 1 \
  --jobs "$JOBS" \
  --max-failures 1 \
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
fail="$(baseline_value "fail")"

[[ "$selected" == "1" ]] || { echo "expected selected=1, got $selected" >&2; exit 1; }
[[ "$errored" == "0" ]] || { echo "expected errored=0, got $errored" >&2; exit 1; }
[[ "$budget" == "0" ]] || { echo "expected budget=0, got $budget" >&2; exit 1; }
[[ "$ran" == "1" ]] || { echo "expected ran=1, got $ran" >&2; exit 1; }
[[ "$full" == "1" ]] || { echo "expected full=1 for $TARGET, got $full" >&2; exit 1; }
[[ "$fail" == "0" ]] || { echo "expected fail=0, got $fail" >&2; exit 1; }

echo "==> PASS: EIP-7002 withdrawal fee-increments b44 full-match gate"
