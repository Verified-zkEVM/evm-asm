#!/usr/bin/env bash
# codegen-eest-eip4844-excess-blob-gas-check.sh -- focused EIP-4844 EEST gate.
#
# Keep the observed excess_blob_gas fixture files covered after the Amsterdam
# blob-gas schedule and blob-tx precharge fixes. Each JSON file is counted from
# the manifest first, so new rows inside those files are covered automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EIP4844_EXCESS_BLOB_GAS_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_EIP4844_EXCESS_BLOB_GAS_STEPS:-${EEST_STEPS:-1000000000}}"
LIMIT_OVERRIDE="${EEST_EIP4844_EXCESS_BLOB_GAS_LIMIT:-}"
BASE_RUN_DIR="${EEST_EIP4844_EXCESS_BLOB_GAS_RUN_DIR:-gen-out/eest-eip4844-excess-blob-gas}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

run_fixture_file() {
  local name="$1"
  local filter="$2"
  local count_dir="$(pwd)/gen-out/eest-eip4844-excess-blob-gas-count-$name"
  local run_dir="$BASE_RUN_DIR/$name"
  local manifest total limit
  shift 2

  rm -rf "$count_dir"
  mkdir -p "$count_dir"

  echo "==> count EIP-4844 excess-blob-gas fixtures: $filter (tag=$TAG)"
  python3 scripts/eest-stateless-to-input.py \
    --fixtures-dir "$FX" \
    --out-dir "$count_dir" \
    --filter "$filter" \
    >/dev/null

  manifest="$count_dir/manifest.tsv"
  [[ -s "$manifest" ]] || { echo "no EIP-4844 stateless blocks selected for $filter" >&2; exit 1; }
  total="$(wc -l < "$manifest" | tr -d ' ')"
  echo "==> EIP-4844 $name selected: $total"
  limit="$total"
  if [[ -n "$LIMIT_OVERRIDE" ]]; then
    if ! [[ "$LIMIT_OVERRIDE" =~ ^[0-9]+$ ]] || [[ "$LIMIT_OVERRIDE" -lt 1 ]]; then
      echo "EEST_EIP4844_EXCESS_BLOB_GAS_LIMIT must be a positive integer (got: $LIMIT_OVERRIDE)" >&2
      exit 1
    fi
    limit="$LIMIT_OVERRIDE"
    if [[ "$limit" -gt "$total" ]]; then
      limit="$total"
    fi
  fi

  if ! awk -F'\t' -v required="$filter" '$7 ~ required { found = 1 } END { exit found ? 0 : 1 }' "$manifest"; then
    echo "required EIP-4844 fixture not selected by $filter" >&2
    exit 1
  fi

  scripts/codegen-eest-stateless-check.sh \
    --filter "$filter" \
    --limit "$limit" \
    --jobs "$JOBS" \
    --quiet-passes \
    --min-full "$limit" \
    --steps "$STEPS" \
    --run-dir "$run_dir" \
    "$@"

  echo "==> PASS: EIP-4844 $filter full-matched $limit/$total selected row(s)"
}

run_fixture_file "correct-calculation" \
  "eip4844_blobs/excess_blob_gas/correct_excess_blob_gas_calculation.json" \
  "$@"
run_fixture_file "invalid-negative" \
  "eip4844_blobs/excess_blob_gas/invalid_negative_excess_blob_gas.json" \
  "$@"

echo "==> PASS: EIP-4844 observed excess-blob-gas rows full-match"
