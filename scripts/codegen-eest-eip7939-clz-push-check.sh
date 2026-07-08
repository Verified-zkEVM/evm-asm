#!/usr/bin/env bash
# codegen-eest-eip7939-clz-push-check.sh -- focused EIP-7939 CLZ EEST gate.
#
# The CLZ runtime handler landed in PR #7917. This keeps the concrete EEST
# failure that motivated the bead covered at the stateless fixture level.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_EIP7939_CLZ_PUSH_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7939_CLZ_PUSH_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7939_CLZ_PUSH_RUN_DIR:-gen-out/eest-eip7939-clz-push}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7939_CLZ_PUSH_FILTER:-clz_push_operation_same_value.json}"
REQUIRED="eip7939_count_leading_zeros/count_leading_zeros/clz_push_operation_same_value.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7939-clz-push-count"
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
  echo "expected exactly one CLZ push fixture row, selected $COUNT" >&2
  exit 1
fi
if ! awk -F'\t' -v required="$REQUIRED" '$7 ~ required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
  echo "required CLZ fixture not selected by $FILTER: $REQUIRED" >&2
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

echo "==> PASS: EIP-7939 CLZ push frontier full-matched $COUNT row(s)"
