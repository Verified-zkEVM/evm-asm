#!/usr/bin/env bash
# Run the EEST random_statetest stateless-guest regression windows.
#
# Discover the current random_statetest count and run every selected block in
# fixed-size windows. This keeps the gate complete if new random_statetest
# fixtures are added to a future EEST tag.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_RANDOM_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_RANDOM_STEPS:-${EEST_STEPS:-1000000000}}"
WINDOW="${EEST_RANDOM_WINDOW:-200}"

if ! [[ "$WINDOW" =~ ^[0-9]+$ ]] || [[ "$WINDOW" -lt 1 ]]; then
  echo "EEST_RANDOM_WINDOW must be a positive integer (got: $WINDOW)" >&2
  exit 1
fi

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-random-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count random_statetest fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter random_statetest \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no random_statetest stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> random_statetest selected: $TOTAL"

run_window() {
  local name="$1"
  local skip="$2"
  local limit="$3"
  shift 3

  echo "==> random_statetest ${name}: skip=${skip} limit=${limit}"
  scripts/codegen-eest-stateless-check.sh \
    --filter random_statetest \
    --skip "$skip" \
    --limit "$limit" \
    --jobs "$JOBS" \
    --quiet-passes \
    --max-failures 1 \
    --min-full "$limit" \
    --steps "$STEPS" \
    "$@"
}

skip=0
window_index=1
while [[ "$skip" -lt "$TOTAL" ]]; do
  remaining=$((TOTAL - skip))
  limit="$WINDOW"
  [[ "$remaining" -lt "$limit" ]] && limit="$remaining"
  run_window "window-$window_index" "$skip" "$limit" "$@"
  skip=$((skip + limit))
  window_index=$((window_index + 1))
done

echo "==> PASS: random_statetest EEST regression windows full-match ($TOTAL case(s))"
