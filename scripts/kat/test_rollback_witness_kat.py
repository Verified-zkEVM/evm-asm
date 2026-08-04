"""Rollback witnesses for GH #11256.

Both cases use ``DELEGATECALL`` so the child executes with the parent's
storage context.  The child reads the read-only sentinel slot ``1`` and then
writes slot ``0``.  The parent ignores the child status, reads slot ``0`` and
returns it successfully.

The under-restore case makes the child revert, so the write must disappear
while both the child's read of slot ``1`` and the parent's read of slot ``0``
remain visible in the block access list.  The over-restore case lets the child
stop successfully, so the write must persist while the independent sentinel
read remains visible.  Slot ``1`` is deliberately distinct from slot ``0``:
the BAL excludes a read that is also present in ``storage_changes``.

The generated JSON is consumed directly by the repository's stateless guest
KAT harness.  Run the fill command from the ``execution-specs`` checkout
with, for example:

    .venv/bin/fill /path/to/EvmAsm/scripts/kat/test_rollback_witness_kat.py \
        --fork=Amsterdam \
        -m blockchain_test --output=/tmp/rollback-witness-kat \
        --no-html --clean
"""

from typing import Any

import pytest
from execution_testing import (
    Account,
    Alloc,
    BalAccountExpectation,
    BalNonceChange,
    BalStorageChange,
    BalStorageSlot,
    Block,
    BlockAccessListExpectation,
    BlockchainTestFiller,
    Op,
    Transaction,
)


pytestmark = pytest.mark.valid_from("Amsterdam")


def _scenario(pre: Alloc, child_reverts: bool) -> tuple[Any, Any, Any]:
    """Build the child, parent, and sender for one witness case."""
    child_code = (
        Op.SLOAD(1)
        + Op.POP
        + Op.SSTORE(0, 1)
        + (Op.REVERT(0, 0) if child_reverts else Op.STOP)
    )
    child = pre.deploy_contract(code=child_code)

    parent_code = (
        Op.DELEGATECALL(
            gas=1_000_000,
            address=child,
            args_offset=0,
            args_size=0,
            ret_offset=0,
            ret_size=0,
        )
        + Op.POP
        + Op.MSTORE(0, Op.SLOAD(0))
        + Op.RETURN(0, 32)
    )
    parent = pre.deploy_contract(code=parent_code)
    sender = pre.fund_eoa()
    return child, parent, sender


@pytest.mark.parametrize(
    "child_reverts",
    [
        pytest.param(True, id="under_restore_child_reverts"),
        pytest.param(False, id="over_restore_child_succeeds"),
    ],
)
def test_rollback_witness(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    child_reverts: bool,
) -> None:
    """Exercise write rollback while keeping shared reads outside the snapshot."""
    child, parent, sender = _scenario(pre, child_reverts)

    parent_expectation = BalAccountExpectation(
        storage_reads=[0, 1] if child_reverts else [1],
        storage_changes=(
            []
            if child_reverts
            else [
                BalStorageSlot(
                    slot=0,
                    slot_changes=[
                        BalStorageChange(block_access_index=1, post_value=1),
                    ],
                )
            ]
        ),
    )

    block = Block(
        txs=[Transaction(sender=sender, to=parent, gas_limit=1_000_000)],
        expected_block_access_list=BlockAccessListExpectation(
            account_expectations={
                sender: BalAccountExpectation(
                    nonce_changes=[BalNonceChange(block_access_index=1, post_nonce=1)],
                ),
                parent: parent_expectation,
                child: BalAccountExpectation.empty(),
            }
        ),
    )

    blockchain_test(
        pre=pre,
        blocks=[block],
        post={
            parent: Account(storage={} if child_reverts else {0: 1}),
        },
    )
