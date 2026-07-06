#!/usr/bin/env bash
# codegen-eest-eip7934-all-typed-rlp-limit-check.sh -- focused EIP-7934 step-budget guard.
#
# This wrapper keeps the all-typed-transactions max_block_rlp_size row from
# silently regressing to BUDGET(steps). It is intentionally a semantic-outcome
# gate: PASS/FAIL/ERROR rows are reported by the underlying harness, but a
# step-budget row is a tooling regression for this frontier.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EIP7934_ALL_TYPED_JOBS:-${EEST_JOBS:-1}}"
STEPS="${EEST_EIP7934_ALL_TYPED_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7934_ALL_TYPED_RUN_DIR:-gen-out/eest-eip7934-all-typed-rlp-limit}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7934_ALL_TYPED_FILTER:-eip7934_block_rlp_limit/max_block_rlp_size/block_rlp_size_at_limit_with_all_typed_transactions.json}"
LIMIT_OVERRIDE="${EEST_EIP7934_ALL_TYPED_LIMIT:-}"
MAX_FAILURES="${EEST_EIP7934_ALL_TYPED_MAX_FAILURES:-1}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7934-all-typed-count"
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

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures "$MAX_FAILURES" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

baseline="$RUN_DIR/eest-baseline.txt"
[[ -s "$baseline" ]] || { echo "missing baseline: $baseline" >&2; exit 1; }
budget="$(awk '/^  budget:/ {print $2}' "$baseline")"
if [[ "${budget:-}" != "0" ]]; then
  echo "EIP-7934 all-typed RLP-limit row still hit BUDGET(steps): budget=${budget:-missing}" >&2
  exit 1
fi

echo "==> PASS: EIP-7934 all-typed RLP-limit reached semantic outcome(s), selected=$COUNT limit=$LIMIT steps=$STEPS"
