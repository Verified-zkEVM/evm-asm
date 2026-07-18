#!/usr/bin/env bash
# codegen-eest-eip7939-clz-jump-check.sh -- EIP-7939 CLZ/JUMP EEST gate.
#
# The CLZ runtime handler landed in PR #7917. This wrapper keeps the
# clz_jump_operation frontier covered with a future-proof filter so newly added
# fixture rows are selected automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
JOBS="${EEST_EIP7939_CLZ_JUMP_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7939_CLZ_JUMP_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7939_CLZ_JUMP_RUN_DIR:-gen-out/eest-eip7939-clz-jump}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7939_CLZ_JUMP_FILTER:-eip7939_count_leading_zeros/count_leading_zeros/clz_jump_operation.json}"
LIMIT_OVERRIDE="${EEST_EIP7939_CLZ_JUMP_LIMIT:-}"
MIN_FULL_OVERRIDE="${EEST_EIP7939_CLZ_JUMP_MIN_FULL:-}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7939-clz-jump-count"
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
LIMIT="${LIMIT_OVERRIDE:-$COUNT}"
MIN_FULL="${MIN_FULL_OVERRIDE:-$LIMIT}"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$MIN_FULL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-7939 CLZ/JUMP frontier completed selected=$COUNT limit=$LIMIT min_full=$MIN_FULL"
