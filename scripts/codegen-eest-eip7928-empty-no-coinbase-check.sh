#!/usr/bin/env bash
# codegen-eest-eip7928-empty-no-coinbase-check.sh -- focused EIP-7928 BAL gate.
#
# This compact BAL fixture full-matches on current main with the larger default
# step budget. Keep it covered while broader EIP-7928 BAL cases are repaired.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.1}"
JOBS="${EEST_EIP7928_EMPTY_NO_COINBASE_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7928_EMPTY_NO_COINBASE_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7928_EMPTY_NO_COINBASE_RUN_DIR:-gen-out/eest-eip7928-empty-no-coinbase}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7928_EMPTY_NO_COINBASE_FILTER:-bal_empty_block_no_coinbase.json}"
REQUIRED="eip7928_block_level_access_lists/block_access_lists/bal_empty_block_no_coinbase.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7928-empty-no-coinbase-count"
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

if [[ "$COUNT" -ne 1 ]]; then
  echo "expected exactly one EIP-7928 empty-block row, selected $COUNT" >&2
  exit 1
fi
if ! awk -F'\t' -v required="$REQUIRED" '$7 ~ required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
  echo "required EIP-7928 fixture not selected by $FILTER: $REQUIRED" >&2
  exit 1
fi

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$COUNT" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-7928 BAL empty-block no-coinbase full-matched $COUNT row(s)"
