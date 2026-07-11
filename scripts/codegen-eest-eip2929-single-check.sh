#!/usr/bin/env bash
# Run the EIP-2929 stEIP150singleCodeGasPrices stateless EEST frontier.
#
# The wrapper derives the run size from the converted manifest so future rows
# in the fixture are covered without editing the script.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.0}"
JOBS="${EEST_EIP2929_SINGLE_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP2929_SINGLE_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP2929_SINGLE_RUN_DIR:-gen-out/eest-eip2929-single}"
FILTER="${EEST_EIP2929_SINGLE_FILTER:-stEIP150singleCodeGasPrices/eip2929/eip2929.json}"

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-eip2929-single-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count EIP-2929 single-code-gas fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no EIP-2929 single-code-gas stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> EIP-2929 single-code-gas selected: $TOTAL"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$TOTAL" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$TOTAL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-2929 single-code-gas rows full-match ($TOTAL case(s))"
