"""
Tx-count KAT v2: EIP-7778/8037 sequential REGULAR-gas inclusion gate beyond
16 transactions, with the probe tx's recipient kept resolvable in the
witness (Amsterdam).

Mechanism (verified against the vendored reference):

* ``check_transaction`` (fork.py:583-596) rejects a tx at inclusion when
  ``min(TX_MAX_GAS_LIMIT, tx.gas) > block_gas_limit - block_gas_used``
  (regular dimension; strict greater-than fails). ``block_gas_used``
  accumulates per-tx regular increments over PRIOR txs. A plain successful
  value transfer contributes exactly 21000.

v1 finding: the guest's ``eip8037_tx_gas_gate`` skips the sequential gate
when tx_count > 16 (BlockVerdictGasGate.lean:171), but the v1 edge block
(fresh recipient for tx17) was still rejected via bv_fail=47 (mtx tx
recipient unresolvable at pre-state root): the invalid-block witness omits
the rejected tx's recipient node. This v2 keeps tx17's recipient
resolvable: tx17 is a SELF-SEND (sender == recipient), and the sender is
always in the witness. The self-send touches only the sender's account, so
BAL-independence is preserved.

Fixture design (block gas limit 500000, 17 txs per block): tx0..tx15 are
plain value transfers with gas 21000 each on mutually disjoint account
lanes (cumulative block_gas_used after 16 txs = 336000). tx16 is a
self-send whose gas limit probes the regular gate at the 17th slot:

* edge (expected INVALID): tx16.gas = 164001 -- one above
  ``500000 - 336000 = 164000``; ``min(16777216, 164001) = 164001 >
  164000`` so the reference REJECTS tx16 at inclusion
  (GasUsedExceedsLimitError), block invalid. Aggregate header gas_used
  would be only 336000 + 12000 = 348000 <= 500000, so no aggregate check
  can catch it. Expect successful_validation = 0.
* control (expected VALID): tx16.gas = 164000 -- exactly the remaining
  budget; strict ``>`` accepts. Expect successful_validation = 1, header
  gas_used = 348000.
"""

from execution_testing import (
    Alloc,
    Block,
    BlockchainTestFiller,
    BlockException,
    Environment,
    Fork,
    Header,
    RecipientType,
    Transaction,
    TransactionException,
    TransactionReceipt,
)

import pytest

pytestmark = pytest.mark.valid_from("Amsterdam")

BLOCK_GAS_LIMIT = 500_000

# Plain value transfer EOA -> distinct EOA, value 1:
#   intrinsic = TX_BASE 12000 + COLD_ACCOUNT_ACCESS 3000
#               + TRANSFER_LOG_COST 1756 + TX_VALUE_COST 4244 = 21000
TRANSFER_GAS = 21_000

# Self-send value transfer (sender == recipient), value 1: Amsterdam
# (transactions.py:687-702) waives COLD_ACCOUNT_ACCESS, TRANSFER_LOG_COST
# and TX_VALUE_COST for self-transfers, so intrinsic = TX_BASE = 12000.
SELF_SEND_GAS = 12_000

# Number of successful 21000-gas transfers before the probe tx.
NUM_FILLER_TXS = 16
CUMULATIVE_AFTER_FILLERS = NUM_FILLER_TXS * TRANSFER_GAS  # 336000
REGULAR_AVAILABLE_AT_TX17 = BLOCK_GAS_LIMIT - CUMULATIVE_AFTER_FILLERS
assert REGULAR_AVAILABLE_AT_TX17 == 164_000
TX17_GAS_EDGE = REGULAR_AVAILABLE_AT_TX17 + 1  # 164001 -> strict > rejects
TX17_GAS_CONTROL = REGULAR_AVAILABLE_AT_TX17  # strict > accepts

# Aggregate gas actually burned: 16 * 21000 + the self-send's 12000.
# (The gate arithmetic at tx17 inclusion depends only on the fillers'
# cumulative 336000, not on tx17's own burn.)
TOTAL_GAS_USED = CUMULATIVE_AFTER_FILLERS + SELF_SEND_GAS  # 348000
assert TOTAL_GAS_USED <= BLOCK_GAS_LIMIT


def _plain_transfer_tx(
    pre: Alloc,
    *,
    gas_limit: int,
    cumulative_gas_used: int | None,
) -> Transaction:
    """Build a plain value transfer on its own account lane."""
    return Transaction(
        sender=pre.fund_eoa(),
        to=pre.fund_eoa(),
        value=1,
        gas_limit=gas_limit,
        max_fee_per_gas=10,
        max_priority_fee_per_gas=0,
        expected_receipt=(
            TransactionReceipt(status=1, cumulative_gas_used=cumulative_gas_used)
            if cumulative_gas_used is not None
            else None
        ),
        error=(
            TransactionException.GAS_ALLOWANCE_EXCEEDED
            if cumulative_gas_used is None
            else None
        ),
    )


def _self_send_tx(
    pre: Alloc,
    *,
    gas_limit: int,
    cumulative_gas_used: int | None,
) -> Transaction:
    """Build the probe tx: a self-send (sender == recipient).

    The sender is always in the witness, so the recipient resolves at the
    pre-state root even for the invalid block; the guest's bv_fail=47
    witness-completeness check cannot fire on this tx.
    """
    sender = pre.fund_eoa()
    return Transaction(
        sender=sender,
        to=sender,
        value=1,
        gas_limit=gas_limit,
        max_fee_per_gas=10,
        max_priority_fee_per_gas=0,
        expected_receipt=(
            TransactionReceipt(status=1, cumulative_gas_used=cumulative_gas_used)
            if cumulative_gas_used is not None
            else None
        ),
        error=(
            TransactionException.GAS_ALLOWANCE_EXCEEDED
            if cumulative_gas_used is None
            else None
        ),
    )


def _txcount_gate2_scenario(
    pre: Alloc,
    fork: Fork,
    tx17_gas_limit: int,
) -> list[Transaction]:
    """Build 16 successful 21000-gas transfers plus the 17th self-send."""
    intrinsic_cost_calc = fork.transaction_intrinsic_cost_calculator()
    assert (
        intrinsic_cost_calc(
            calldata=b"",
            sends_value=True,
            recipient_type=RecipientType.EOA,
        )
        == TRANSFER_GAS
    )
    assert (
        intrinsic_cost_calc(
            calldata=b"",
            sends_value=True,
            recipient_type=RecipientType.SELF,
        )
        == SELF_SEND_GAS
    )

    txs = [
        _plain_transfer_tx(
            pre,
            gas_limit=TRANSFER_GAS,
            cumulative_gas_used=(i + 1) * TRANSFER_GAS,
        )
        for i in range(NUM_FILLER_TXS)
    ]
    tx17 = _self_send_tx(
        pre,
        gas_limit=tx17_gas_limit,
        cumulative_gas_used=(
            TOTAL_GAS_USED if tx17_gas_limit == TX17_GAS_CONTROL else None
        ),
    )
    txs.append(tx17)
    return txs


@pytest.mark.exception_test
def test_txcount_gate2_edge(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    Edge: 17 txs, tx17 (self-send) gas_limit 164001 is one above the
    regular budget remaining after 16 successful transfers
    (500000 - 336000 = 164000). The reference REJECTS tx17 at inclusion
    (GasUsedExceedsLimitError) and the block is invalid. The aggregate
    header gas_used (348000) is well below the limit, and tx17's recipient
    (its sender) is in the witness, so neither the aggregate check nor the
    witness-completeness check can catch this -- only the per-tx
    sequential gate can.

    Expect successful_validation = 0.
    """
    txs = _txcount_gate2_scenario(pre, fork, TX17_GAS_EDGE)

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=txs,
                gas_limit=BLOCK_GAS_LIMIT,
                exception=[
                    BlockException.GAS_USED_OVERFLOW,
                    TransactionException.GAS_ALLOWANCE_EXCEEDED,
                ],
                expected_stateless_validation_success=False,
            )
        ],
        post={},
    )


def test_txcount_gate2_control(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    Control: identical 17-tx block but tx17 (self-send) gas_limit is
    exactly the remaining regular budget (164000); the strict-greater gate
    accepts. The reference ACCEPTS the block.

    Expect successful_validation = 1. Header gas_used pins the sixteen
    21000 burns plus the self-send's 12000 (348000).
    """
    txs = _txcount_gate2_scenario(pre, fork, TX17_GAS_CONTROL)

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=txs,
                gas_limit=BLOCK_GAS_LIMIT,
                header_verify=Header(gas_used=TOTAL_GAS_USED),
                expected_stateless_validation_success=True,
            )
        ],
        post={},
    )
