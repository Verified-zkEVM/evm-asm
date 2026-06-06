#!/usr/bin/env bash
# codegen-eest-eip7778-block-gas-check.sh -- EIP-7778 block-gas frontier.
#
# This wrapper is intentionally a diagnostic frontier today: current main still
# has known succ-bit mismatches in multi_transaction_gas_accounting.json because
# the RISC-V guest does not yet account block gas like execution-specs. The
# script derives its default limit from the converted manifest so future matching
# rows are included automatically, then stops after a small failure sample by
# default. Set EEST_EIP7778_MIN_FULL to turn the same wrapper into a hard
# full-match gate once the gas-accounting implementation lands.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EIP7778_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_EIP7778_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7778_RUN_DIR:-gen-out/eest-eip7778-block-gas}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7778_FILTER:-eip7778_block_gas_accounting_without_refunds}"
LIMIT_OVERRIDE="${EEST_EIP7778_LIMIT:-}"
MAX_FAILURES="${EEST_EIP7778_MAX_FAILURES:-5}"
MIN_FULL="${EEST_EIP7778_MIN_FULL:-}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7778-block-gas-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null
manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for EIP-7778 filter: $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"
LIMIT="${LIMIT_OVERRIDE:-$COUNT}"

args=(
  --filter "$FILTER"
  --limit "$LIMIT"
  --jobs "$JOBS"
  --quiet-passes
  --steps "$STEPS"
  --run-dir "$RUN_DIR"
)

if [[ -n "$MAX_FAILURES" ]]; then
  args+=(--max-failures "$MAX_FAILURES")
fi
if [[ -n "$MIN_FULL" ]]; then
  args+=(--min-full "$MIN_FULL")
fi

scripts/codegen-eest-stateless-check.sh "${args[@]}" "$@"

echo "==> PASS: EIP-7778 block-gas frontier completed selected=$COUNT limit=$LIMIT"
