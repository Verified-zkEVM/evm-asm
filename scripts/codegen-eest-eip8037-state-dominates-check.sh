#!/usr/bin/env bash
# Probe the EIP-8037 state-dominated block-gas accounting frontier.
#
# These fixtures exercise valid blocks whose final block gas used is dominated
# by state gas. The stateless guest should not reject them from the conservative
# transaction inclusion gate before full execution gas accounting is available.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.1}"
JOBS="${EEST_EIP8037_STATE_DOMINATES_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP8037_STATE_DOMINATES_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP8037_STATE_DOMINATES_RUN_DIR:-gen-out/eest-eip8037-state-dominates}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh )" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip8037-state-dominates-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter block_gas_used_state_dominates \
  >/dev/null
manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for block_gas_used_state_dominates" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"

scripts/codegen-eest-stateless-check.sh \
  --filter block_gas_used_state_dominates \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  --min-full "$COUNT" \
  "$@"

echo "==> PASS: EIP-8037 state-dominates frontier matched $COUNT fixture(s)"
