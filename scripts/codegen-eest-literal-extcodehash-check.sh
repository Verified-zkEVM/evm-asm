#!/usr/bin/env bash
# Run filter-driven EEST regressions for literal PUSH20;EXTCODEHASH code
# omission cases. The selected fixture counts are discovered from the active
# EEST tag so future additions to these groups are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_LITERAL_EXTCODEHASH_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_LITERAL_EXTCODEHASH_STEPS:-${EEST_STEPS:-1000000000}}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_filter() {
  local filter="$1"
  local count_dir
  count_dir="$(pwd)/gen-out/eest-literal-extcodehash-count-$filter"
  rm -rf "$count_dir"
  mkdir -p "$count_dir"
  python3 scripts/eest-stateless-to-input.py \
    --fixtures-dir "$FX" \
    --out-dir "$count_dir" \
    --filter "$filter" \
    >/dev/null
  local manifest="$count_dir/manifest.tsv"
  [[ -s "$manifest" ]] || { echo "no stateless blocks selected for filter: $filter" >&2; exit 1; }
  wc -l < "$manifest" | tr -d ' '
}

run_filter() {
  local filter="$1"
  local count
  shift
  count="$(count_filter "$filter")"
  echo "==> literal EXTCODEHASH filter=$filter count=$count"
  scripts/codegen-eest-stateless-check.sh \
    --all \
    --filter "$filter" \
    --jobs "$JOBS" \
    --quiet-passes \
    --max-failures 1 \
    --min-full "$count" \
    --steps "$STEPS" \
    "$@"
}

run_filter witness_codes_extcodehash_only "$@"
run_filter witness_codes_extcode_delegated_eoa "$@"

echo "==> PASS: literal EXTCODEHASH EEST filters full-match"
