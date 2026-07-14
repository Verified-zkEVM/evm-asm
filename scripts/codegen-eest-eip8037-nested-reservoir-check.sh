#!/usr/bin/env bash
# codegen-eest-eip8037-nested-reservoir-check.sh -- EIP-8037 reservoir reset frontier.
#
# These fixtures exercise nested call/create failures that must reset EIP-8037
# state-gas reservoir usage correctly. Keep this wrapper filter-driven so newly
# added nested_failure_resets_to_tx_reservoir rows are selected automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
JOBS="${EEST_EIP8037_NESTED_RESERVOIR_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP8037_NESTED_RESERVOIR_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP8037_NESTED_RESERVOIR_RUN_DIR:-gen-out/eest-eip8037-nested-reservoir}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP8037_NESTED_RESERVOIR_FILTER:-eip8037_state_creation_gas_cost_increase/state_gas_reservoir/nested_failure_resets_to_tx_reservoir.json}"
SKIP="${EEST_EIP8037_NESTED_RESERVOIR_SKIP:-0}"
LIMIT_OVERRIDE="${EEST_EIP8037_NESTED_RESERVOIR_LIMIT:-}"
MIN_FULL_OVERRIDE="${EEST_EIP8037_NESTED_RESERVOIR_MIN_FULL:-}"
MAX_FAILURES="${EEST_EIP8037_NESTED_RESERVOIR_MAX_FAILURES:-1}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip8037-nested-reservoir-count"
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

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --skip "$SKIP" \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures "$MAX_FAILURES" \
  --min-full "$MIN_FULL" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

echo "==> PASS: EIP-8037 nested-reservoir frontier completed selected=$COUNT skip=$SKIP limit=$LIMIT min_full=$MIN_FULL"
