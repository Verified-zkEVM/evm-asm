#!/usr/bin/env bash
# Run the EIP-7685 valid_multi_type_requests stateless EEST regression.
#
# Use the exact path suffix so invalid_multi_type_requests is not selected by
# substring matching. Count rows from the active EEST tag so future parameter
# rows are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.1}"
JOBS="${EEST_VALID_MULTI_TYPE_REQUESTS_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_VALID_MULTI_TYPE_REQUESTS_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_VALID_MULTI_TYPE_REQUESTS_RUN_DIR:-gen-out/eest-valid-multi-type-requests}"
FILTER="${EEST_VALID_MULTI_TYPE_REQUESTS_FILTER:-multi_type_requests/valid_multi_type_requests.json}"

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

COUNT_DIR="$(pwd)/gen-out/eest-valid-multi-type-requests-count"
rm -rf "$COUNT_DIR"
mkdir -p "$COUNT_DIR"

echo "==> count EIP-7685 valid multi-type request fixtures (tag=$TAG)"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$COUNT_DIR" \
  --filter "$FILTER" \
  >/dev/null

MANIFEST="$COUNT_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no EIP-7685 valid multi-type request stateless blocks selected" >&2; exit 1; }
TOTAL="$(wc -l < "$MANIFEST" | tr -d ' ')"
echo "==> EIP-7685 valid multi-type requests selected: $TOTAL"

if awk -F'\t' '$7 ~ /invalid_multi_type_requests[.]json$/ { found = 1 } END { exit found ? 0 : 1 }' "$MANIFEST"; then
  echo "filter unexpectedly selected invalid_multi_type_requests rows" >&2
  exit 1
fi

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$TOTAL" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$TOTAL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-7685 valid multi-type request rows full-match ($TOTAL case(s))"
