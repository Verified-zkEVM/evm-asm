#!/usr/bin/env bash
# Probe the EIP-2929 precompile-warming frontier.
#
# This wrapper derives the default run limit from the converted manifest and
# requires every selected row to full-match, so future parameter rows for the
# fixture are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_PRECOMPILE_WARMING_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_PRECOMPILE_WARMING_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_PRECOMPILE_WARMING_RUN_DIR:-gen-out/eest-precompile-warming}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_PRECOMPILE_WARMING_FILTER:-precompile_warming}"
LIMIT_OVERRIDE="${EEST_PRECOMPILE_WARMING_LIMIT:-}"
MAX_FAILURES="${EEST_PRECOMPILE_WARMING_MAX_FAILURES:-5}"
MIN_FULL_OVERRIDE="${EEST_PRECOMPILE_WARMING_MIN_FULL:-}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-precompile-warming-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null
manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for precompile-warming filter: $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"
LIMIT="${LIMIT_OVERRIDE:-$COUNT}"
MIN_FULL="${MIN_FULL_OVERRIDE:-$LIMIT}"

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

echo "==> PASS: precompile-warming frontier completed selected=$COUNT limit=$LIMIT"
