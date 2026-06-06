#!/usr/bin/env bash
# codegen-eest-push-frontier-check.sh -- focused frontier PUSH EEST gate.
#
# The default selection covers every stateless row selected by the frontier
# push.json fixture. It derives the run limit from the converted manifest so new
# PUSH rows added to the fixture are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_PUSH_FRONTIER_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_PUSH_FRONTIER_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_PUSH_FRONTIER_RUN_DIR:-gen-out/eest-push-frontier}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_PUSH_FRONTIER_FILTER:-blockchain_tests/for_amsterdam/frontier/opcodes/push/push.json}"
LIMIT_OVERRIDE="${EEST_PUSH_FRONTIER_LIMIT:-}"
REQUIRED="blockchain_tests/for_amsterdam/frontier/opcodes/push/push.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-push-frontier-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null

manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for PUSH filter: $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"
LIMIT="${LIMIT_OVERRIDE:-$COUNT}"

if ! awk -F'\t' -v required="$REQUIRED" '$7 == required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
  echo "required PUSH fixture not selected by $FILTER: $REQUIRED" >&2
  exit 1
fi

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$LIMIT" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: PUSH frontier full-matched selected=$LIMIT of available=$COUNT"
