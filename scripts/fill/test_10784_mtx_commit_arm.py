"""GH #10784 regression-gate fixtures: SELFDESTRUCT inside a transaction that
then FAILS AT TOP LEVEL after post-preparation.

Defect under test (BlockVerdictMtxRuntime.lean:615): the per-tx account-state
epilogue takes the COMMIT arm when the tx status is nonzero OR
runtime_tx_post_preparation_reached is set; only the fall-through arm clears
account_state_pending/created/delete_count. A destroy queued by a transaction
that later fails at top level is therefore CONSUMED BY THE COMMIT ARM.

Measured direction (scripts/gate-10784-mtx-commit-arm.py): LATENT. The arm
fires on every failing post-preparation tx, but the post-state root is
unaffected because of two load-bearing latency conditions:

  1. Delete-queue insertion (NoopHalt.lean:520-600) is gated on the target
     being created in the SAME transaction (EIP-6780 semantics), and
  2. the depth-0 rollback removes everything a failed tx created, so the
     only accounts the delete queue can ever name are already absent when
     the commit arm consumes the queue.

If either condition changes, committing a destroy becomes observable in the
post-state root. These fixtures exist to pin the mechanism, not the symptom:
the gate asserts the instrumented-probe numbers (arm marker, counts at
commit-arm entry) together with byte-exact root agreement.

Fixtures (all VALID blocks; fill must pass):

  fx1  test_selfdestruct_created_same_tx_top_level_revert
       One tx: driver CREATEs A (same tx), CALLs A, A executes
       SELFDESTRUCT(beneficiary) and halts normally, driver then REVERTs at
       top level. Spec: A absent, driver storage reverted, beneficiary
       absent. Guest probe: commit arm taken, created=1 delete=1 at
       commit-arm entry (the destroy IS queued and consumed), root unaffected
       (latency condition 2).

  fxA  test_preexisting_selfdestruct_top_level_revert
       Pre-existing A (balance 7, storage {1:1}) called by a driver that then
       REVERTs at top level. Spec: A intact. Guest probe: delete=0 at
       commit-arm entry (latency condition 1 gating works).

  fxB  test_created_earlier_tx_selfdestruct_top_level_revert
       tx1 deploys A (value 9, storage {1:1}); tx2 CALLs A (SELFDESTRUCT
       executes) then REVERTs at top level. Spec: A intact (fresh
       TransactionState per tx, fork.py:1043). Guest probe: delete=0 at
       commit-arm entry (gating is per-tx, not block-scoped).

Fill (from the repo root):

    uv run --directory execution-specs fill \\
        "$PWD/scripts/fill/test_10784_mtx_commit_arm.py" \\
        --fork Amsterdam --output <workdir>/fixtures --clean --no-html

(The fill file must be passed as a positional argument with an absolute
path; --filler-path does not restrict collection.)
"""

import pytest
from execution_testing import (
    Account,
    Address,
    Alloc,
    Block,
    BlockchainTestFiller,
    EOA,
    Environment,
    Initcode,
    Op,
    StateTestFiller,
    Transaction,
    compute_create_address,
)

BENEFICIARY = Address(0xBEEF1E0000000000000000000000000000000000)

# Runtime code of the selfdestructing contract A: SELFDESTRUCT(BENEFICIARY).
A_RUNTIME = Op.SELFDESTRUCT(BENEFICIARY) + Op.STOP

# Initcode for tx1 of fxB: SSTORE(1, 1) during construction, then deploy.
A_INITCODE = Initcode(deploy_code=A_RUNTIME, initcode_prefix=Op.SSTORE(1, 1))


@pytest.mark.valid_from("Cancun")
def test_selfdestruct_created_same_tx_top_level_revert(
    state_test: StateTestFiller,
    pre: Alloc,
    sender: EOA,
    env: Environment,
) -> None:
    """fx1: selfdestruct of a same-tx-created contract, then top-level revert."""
    beneficiary = Address(0xBEEF1EF1EF1EF1EF1EF1EF1EF1EF1EF1EF1EF1EF)
    deploy_code = Op.SELFDESTRUCT(beneficiary) + Op.STOP
    initcode = Initcode(deploy_code=deploy_code)
    initcode_bytes = bytes(initcode)

    carrier = pre.deploy_contract(code=initcode_bytes)
    driver_code = (
        Op.EXTCODECOPY(carrier, 0, 0, len(initcode_bytes))
        + Op.SSTORE(0, Op.CREATE(0, 0, len(initcode_bytes)))
        + Op.POP(Op.CALL(Op.GASLIMIT, Op.SLOAD(0), 0, 0, 0, 0, 0))
        + Op.REVERT(0, 0)
    )
    driver = pre.deploy_contract(code=driver_code)
    created = compute_create_address(address=driver, nonce=1)

    tx = Transaction(
        sender=sender,
        to=driver,
        gas_limit=500_000,
    )

    post = {
        driver: Account(storage={0: 0}),
        created: Account.NONEXISTENT,
        beneficiary: Account.NONEXISTENT,
    }

    state_test(env=env, pre=pre, tx=tx, post=post)


@pytest.mark.valid_from("Cancun")
def test_preexisting_selfdestruct_top_level_revert(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
) -> None:
    """fxA: pre-existing A selfdestructs in a tx that reverts at top level."""
    sender = pre.fund_eoa()
    contract_a = pre.deploy_contract(A_RUNTIME, balance=7, storage={1: 1})
    driver_code = (
        Op.POP(Op.CALL(Op.GASLIMIT, contract_a, 0, 0, 0, 0, 0))
        + Op.SSTORE(0, 0xDEAD)
        + Op.REVERT(0, 0)
    )
    driver = pre.deploy_contract(driver_code)
    tx = Transaction(
        sender=sender,
        to=driver,
        gas_limit=1_000_000,
    )
    post = {
        contract_a: Account(balance=7, storage={1: 1}),
        driver: Account(storage={0: 0}),
        BENEFICIARY: Account.NONEXISTENT,
    }
    blockchain_test(pre=pre, blocks=[Block(txs=[tx])], post=post)


@pytest.mark.valid_from("Cancun")
def test_created_earlier_tx_selfdestruct_top_level_revert(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
) -> None:
    """fxB: A created in successful tx1; selfdestruct in tx2 which reverts."""
    sender = pre.fund_eoa()
    # CREATE-type transactions from an EOA use the sender's PRE-TX nonce.
    created = compute_create_address(address=sender, nonce=0)
    driver_code = (
        Op.POP(Op.CALL(Op.GASLIMIT, created, 0, 0, 0, 0, 0))
        + Op.SSTORE(0, 0xBEEF)
        + Op.REVERT(0, 0)
    )
    driver = pre.deploy_contract(driver_code)
    tx1 = Transaction(
        sender=sender,
        to=None,
        data=A_INITCODE,
        value=9,
        gas_limit=1_000_000,
    )
    tx2 = Transaction(
        sender=sender,
        to=driver,
        gas_limit=1_000_000,
    )
    post = {
        created: Account(balance=9, storage={1: 1}),
        driver: Account(storage={0: 0}),
        BENEFICIARY: Account.NONEXISTENT,
    }
    blockchain_test(pre=pre, blocks=[Block(txs=[tx1, tx2])], post=post)
