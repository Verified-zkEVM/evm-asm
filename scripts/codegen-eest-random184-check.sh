#!/usr/bin/env bash
# Run the random_statetest184 stateless EEST regression.
#
# Count rows from the active EEST tag so future parameter rows for this fixture
# are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_RANDOM184_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_RANDOM184_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_RANDOM184_RUN_DIR:-gen-out/eest-random184}"
FILTER="${EEST_RANDOM184_FILTER:-random_statetest184}"

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-random184-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count random_statetest184 fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no random_statetest184 stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> random_statetest184 selected: $TOTAL"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$TOTAL" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$TOTAL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: random_statetest184 rows full-match ($TOTAL case(s))"
