#!/usr/bin/env bash
# codegen-eest-eip7843-slotnum-check.sh -- focused EIP-7843 SLOTNUM EEST gate.
#
# The full 2026-06-04 EEST log showed SLOTNUM ERROR(exit) rows. Current
# runtime support passes the focused frontier with the larger default step
# budget, so keep this as a small regression gate over every row selected by
# the SLOTNUM fixture directory.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.1}"
JOBS="${EEST_EIP7843_SLOTNUM_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7843_SLOTNUM_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7843_SLOTNUM_RUN_DIR:-gen-out/eest-eip7843-slotnum}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7843_SLOTNUM_FILTER:-eip7843_slotnum/slotnum}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7843-slotnum-count"
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

for required in \
  "eip7843_slotnum/slotnum/slotnum_gas_cost.json" \
  "eip7843_slotnum/slotnum/slotnum_value.json"; do
  if ! awk -F'\t' -v required="$required" '$7 ~ required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
    echo "required SLOTNUM fixture not selected by $FILTER: $required" >&2
    exit 1
  fi
done

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$COUNT" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-7843 SLOTNUM frontier full-matched $COUNT row(s)"
