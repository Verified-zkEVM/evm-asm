#!/usr/bin/env bash
# codegen-eest-exp-frontier-check.sh -- full-match the current EXP EEST frontier.
#
# This is the broader companion to codegen-eest-exp-power256-check.sh. It
# discovers the active fixture tag's opcode EXP stateless blocks and then
# requires every selected block to full-match. The manifest loop makes the check
# complete for newly added matching fixtures instead of pinning a fixed
# skip/limit window. The default filter is path-specific so it does not pick up
# MODEXP precompile or memory-expansion fixtures.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EXP_FRONTIER_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_EXP_FRONTIER_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EXP_FRONTIER_RUN_DIR:-gen-out/eest-exp-frontier}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EXP_FRONTIER_FILTER:-opcodes/exp/}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-exp-frontier-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null
manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for EXP filter: $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  --min-full "$COUNT" \
  "$@"

echo "==> PASS: EXP EEST frontier full-matches selected=$COUNT"
