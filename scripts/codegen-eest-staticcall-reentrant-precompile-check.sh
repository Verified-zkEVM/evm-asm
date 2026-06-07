#!/usr/bin/env bash
# codegen-eest-staticcall-reentrant-precompile-check.sh -- focused STATICCALL/precompile EEST gate.
#
# The default filter selects the reentrant STATICCALL-to-precompile fixture and
# derives the run limit from the converted manifest so future rows in the same
# fixture are covered automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_STATICCALL_REENTRANT_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_STATICCALL_REENTRANT_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_STATICCALL_REENTRANT_RUN_DIR:-gen-out/eest-staticcall-reentrant-precompile}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_STATICCALL_REENTRANT_FILTER:-staticcall_reentrant_call_to_precompile.json}"
LIMIT_OVERRIDE="${EEST_STATICCALL_REENTRANT_LIMIT:-}"
MIN_FULL_OVERRIDE="${EEST_STATICCALL_REENTRANT_MIN_FULL:-}"
REQUIRED="staticcall_reentrant_call_to_precompile.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-staticcall-reentrant-precompile-count"
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
LIMIT="${LIMIT_OVERRIDE:-$COUNT}"
MIN_FULL="${MIN_FULL_OVERRIDE:-$LIMIT}"

if ! awk -F'\t' -v required="$REQUIRED" '$7 ~ required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
  echo "required STATICCALL/precompile fixture not selected by $FILTER: $REQUIRED" >&2
  exit 1
fi

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --min-full "$MIN_FULL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: STATICCALL reentrant precompile frontier completed selected=$COUNT limit=$LIMIT min_full=$MIN_FULL"
