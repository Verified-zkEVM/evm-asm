#!/usr/bin/env bash
# Regression gate for transaction_collision_to_empty_but_code stateless
# fixtures. Count the active fixture tag dynamically so future additions to
# this family are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_TRANSACTION_COLLISION_EMPTY_CODE_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_TRANSACTION_COLLISION_EMPTY_CODE_STEPS:-${EEST_STEPS:-1000000000}}"
FILTER="transaction_collision_to_empty_but_code"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-transaction-collision-empty-code-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no stateless blocks selected for filter: $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$MANIFEST" | tr -d ' ')"

scripts/codegen-eest-stateless-check.sh \
  --all \
  --filter "$FILTER" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --min-full "$COUNT" \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: transaction_collision_to_empty_but_code full-matched ($COUNT/$COUNT)"
