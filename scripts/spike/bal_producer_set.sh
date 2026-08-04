#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "usage: $0 <guest.elf> <manifest.tsv> [out-dir]" >&2
  exit 2
fi

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
GUEST_ELF=$(realpath "$1")
MANIFEST=$(realpath "$2")
OUT_DIR=${3:-/tmp/bal-producer-diff-set}
OUT_DIR=$(realpath -m "$OUT_DIR")
mkdir -p "$OUT_DIR"
SPIKE=${SPIKE:-$ROOT/scripts/spike/spike_run}
EXECUTION_SPECS=${EXECUTION_SPECS:-$ROOT/execution-specs}
PROGRAM_SOURCE=$ROOT/EvmAsm/Codegen/Programs/BlockAccessListBuilder.lean
CODE_SOURCE=$ROOT/EvmAsm/Codegen/Programs/CreateCodeEffectLog.lean
PARAMS_SOURCE=$ROOT/EvmAsm/Codegen/Programs/BlockVerdictParams.lean

run_case() {
  local label=$1 expectation=$2
  uv run --directory "$EXECUTION_SPECS" --quiet python3 \
    "$ROOT/scripts/spike/bal_producer_diff.py" \
    --spike "$SPIKE" \
    --guest-elf "$GUEST_ELF" \
    --manifest "$MANIFEST" \
    --label "$label" \
    --expectation "$ROOT/scripts/spike/$expectation" \
    --execution-specs "$EXECUTION_SPECS" \
    --program-source "$PROGRAM_SOURCE" \
    --code-source "$CODE_SOURCE" \
    --params-source "$PARAMS_SOURCE" \
    --out-dir "$OUT_DIR/${label%%_*}"
}

run_case \
  00318_test_bal_balance_changes_fork_Amsterdam-blockchain_test__b0 \
  bal-balance-changes.expectation.json
run_case \
  00289_test_bal_2930_slot_listed_and_unlisted_writes_fork_Amsterdam-blockchain_test__b0 \
  bal-storage-writes.expectation.json
run_case \
  00321_test_bal_code_changes_fork_Amsterdam-blockchain_test__b0 \
  bal-code-changes.expectation.json
run_case \
  00317_test_bal_all_transaction_types_fork_Amsterdam-blockchain_test__b0 \
  bal-all-transaction-types.expectation.json
