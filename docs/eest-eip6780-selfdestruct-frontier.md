# EEST EIP-6780 SELFDESTRUCT Frontier

This note records the `eip6780_selfdestruct` failure cluster reported on
2026-06-02. No harness run was performed for this triage; the fixture surface
below comes from the checked-out `execution-specs` submodule.

Owning bead: `evm-asm-fhsxz.2.4.2.60.6.2`.

## Source Semantics

Executable-spec source of truth:

- `execution-specs/src/ethereum/forks/cancun/vm/instructions/system.py`
- `execution-specs/src/ethereum/forks/amsterdam/vm/instructions/system.py`
- `execution-specs/src/ethereum/forks/*/vm/interpreter.py`
- `execution-specs/src/ethereum/forks/*/state_tracker.py`

Post-Cancun SELFDESTRUCT does all of the following:

- Pops one beneficiary address and halts successfully.
- Charges base gas plus cold-beneficiary access gas, and conditionally the
  new-account surcharge.
- Transfers the originator balance to the beneficiary.
- Deletes the originator only when the originator was created in the same
  transaction.
- Clears the originator balance when same-transaction deletion applies; if the
  beneficiary is the originator, the balance is burned.
- Rolls back balance transfers, logs, touched accounts, and deletion marks for
  reverted frames.
- In Amsterdam and later, emits transfer/burn log side effects for
  SELFDESTRUCT value movement.

The existing Lean surface has useful pieces but is incomplete for this cluster:

- `EvmAsm/EL/SelfdestructEffects.lean` models only the non-deleting
  post-Cancun transfer/touched-account path.
- `EvmAsm/EL/MessageCallExecution.lean` already clears side effects on
  revert/failure.
- `EvmAsm/Codegen/Programs/Noop.lean` currently treats the concrete
  SELFDESTRUCT handler as a pop-and-halt placeholder.

## Fixture Families

Fixture directory:
`execution-specs/tests/cancun/eip6780_selfdestruct`.

Known test functions in that directory:

- `test_create_selfdestruct_same_tx`
- `test_self_destructing_initcode`
- `test_self_destructing_initcode_create_tx`
- `test_recreate_self_destructed_contract_different_txs`
- `test_selfdestruct_pre_existing`
- `test_selfdestruct_created_same_block_different_tx`
- `test_calling_from_new_contract_to_pre_existing_contract`
- `test_calling_from_pre_existing_contract_to_new_contract`
- `test_create_selfdestruct_same_tx_increased_nonce`
- `test_create_and_destroy_multiple_contracts_same_tx`
- `test_create_multiple_contracts_destroy_one_then_destroy_other_next_tx`
- `test_parent_creates_child_selfdestruct_one`
- `test_recursive_contract_creation_and_selfdestruct`
- `test_selfdestruct_created_in_same_tx_with_revert`
- `test_selfdestruct_not_created_in_same_tx_with_revert`
- `test_reentrancy_selfdestruct_revert`
- `test_selfdestruct_balance_transfer_reverted`
- `test_dynamic_create2_selfdestruct_collision`
- `test_dynamic_create2_selfdestruct_collision_two_different_transactions`
- `test_dynamic_create2_selfdestruct_collision_multi_tx`

## Root-Cause Buckets

1. Same-transaction deletion tracking:
   the guest needs a transaction-local created-account set and must schedule
   SELFDESTRUCT deletion only when the originator is in that set.

2. Pre-existing account semantics:
   pre-existing contracts must not be deleted after Cancun; only their balance
   is transferred. This is distinct from the same-block/different-transaction
   case, where a contract may be new to the block but not new to the current
   transaction.

3. Revert journaling:
   SELFDESTRUCT balance transfers, touched accounts, accounts-to-delete, and
   Amsterdam transfer/burn logs must be discarded when the containing frame
   reverts.

4. CREATE/CREATE2 collision and recreation:
   fixtures exercise storage destruction, nonce/code changes, and whether an
   address can be recreated after a same-transaction SELFDESTRUCT.

5. Concrete opcode handler:
   the current generated handler pops the beneficiary and exits. It does not
   charge warm/cold gas, access state, transfer balance, emit side effects, or
   produce post-state descriptors.

6. Post-state and receipts integration:
   passing the fixtures requires account deletion, balance/code/nonce/storage
   changes, logs, receipts, and block access list side effects to feed the
   existing post-state-root and receipt pipelines.

## Suggested Work Order

1. Extend `SelfdestructEffects` with a fork-aware result shape that distinguishes
   same-transaction-created originators from pre-existing originators.
2. Add a call-frame/revert bridge proving SELFDESTRUCT side effects disappear
   under reverted frames.
3. Thread created-account tracking through CREATE/CREATE2 and transaction
   execution before wiring concrete SELFDESTRUCT.
4. Replace the concrete SELFDESTRUCT pop-and-halt handler with gas/state/effect
   plumbing once state writes and call frames are available.
5. Run a focused EEST selection with a filter such as `eip6780_selfdestruct`
   and split remaining failures by the buckets above.
