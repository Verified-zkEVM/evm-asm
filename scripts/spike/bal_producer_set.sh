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
run_case \
  00327_test_bal_cross_tx_balance_dependency_fork_Amsterdam-blockchain_test-funding_method_selfdestruct_ \
  bal-cross-tx-balance-dependency.expectation.json
run_case \
  00505_test_bal_selfdestruct_to_coinbase_fork_Amsterdam-blockchain_test_from_state_test-pre_deploy__b0 \
  bal-selfdestruct-to-coinbase.expectation.json
run_case \
  01114_test_bal_create_storage_op_then_selfdestruct_same_tx_fork_Amsterdam-create_opcode_CREATE-blockch \
  bal-create-storage-selfdestruct.expectation.json
run_case \
  00613_test_bal_7702_delegated_storage_access_fork_Amsterdam-blockchain_test__b0 \
  bal-7702-delegated-storage.expectation.json
run_case \
  00620_test_bal_7702_delegation_create_fork_Amsterdam-blockchain_test-self_funded__b0 \
  bal-7702-delegation-create.expectation.json
run_case \
  00511_test_bal_system_contract_noop_filtering_fork_Amsterdam-blockchain_test__b0 \
  bal-system-noop.expectation.json
run_case \
  00609_test_bal_system_dequeue_consolidations_eip7251_fork_Amsterdam-blockchain_test-single_block_max_c \
  bal-system-dequeue-consolidations.expectation.json
# N=0 withdrawal: exact coverage only, not a discriminator for N+1.
run_case \
  00568_test_bal_withdrawal_no_evm_execution_fork_Amsterdam-blockchain_test__b0 \
  bal-withdrawal-no-evm.expectation.json
# N=1 plus withdrawal: distinguishes post-exec N+1 from per-tx BAI.
run_case \
  00564_test_bal_withdrawal_and_transaction_fork_Amsterdam-blockchain_test__b0 \
  bal-withdrawal-and-transaction.expectation.json
# Zero-value CREATE: exact coverage only; no created-account balance row.
run_case \
  00323_test_bal_create_transaction_empty_code_fork_Amsterdam-blockchain_test__b0 \
  bal-create-transaction-empty.expectation.json
# Nonzero-value top-level CREATE: created-account balance row is present.
run_case \
  21086_test_create_transaction_success_fork_Amsterdam-blockchain_test_from_state_test__b0 \
  bal-create-transaction-success.expectation.json
run_case \
  00356_test_bal_intra_tx_sstores_same_slot_net_zero_fork_Amsterdam-blockchain_test-empty_pre_ephemeral_ \
  bal-net-zero-storage-empty-pre.expectation.json
run_case \
  00357_test_bal_intra_tx_sstores_same_slot_net_zero_fork_Amsterdam-blockchain_test-nonzero_pre_returns_ \
  bal-net-zero-storage-nonzero-pre.expectation.json
run_case \
  00364_test_bal_nested_delegatecall_storage_writes_net_zero_fork_Amsterdam-blockchain_test-depth_1__b0 \
  bal-net-zero-nested-delegatecall.expectation.json
