#!/usr/bin/env bash
# codegen-eest-eip7954-max-code-check.sh -- focused EIP-7954 EEST gate.
#
# The broad 2026-06-04 EEST log showed this fork-transition row as ERROR(exit).
# Current main full-matches it with the larger default step budget; keep this
# concrete max-code-size row covered while wider EIP-7954 coverage is expanded.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EIP7954_MAX_CODE_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7954_MAX_CODE_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7954_MAX_CODE_RUN_DIR:-gen-out/eest-eip7954-max-code}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7954_MAX_CODE_FILTER:-max_code_size_fork_transition.json}"
REQUIRED="eip7954_increase_max_contract_size/fork_transition/max_code_size_fork_transition.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7954-max-code-count"
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
  echo "expected exactly one EIP-7954 max-code row, selected $COUNT" >&2
  exit 1
fi
if ! awk -F'\t' -v required="$REQUIRED" '$7 ~ required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
  echo "required EIP-7954 fixture not selected by $FILTER: $REQUIRED" >&2
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

echo "==> PASS: EIP-7954 max-code-size fork-transition full-matched $COUNT row(s)"
