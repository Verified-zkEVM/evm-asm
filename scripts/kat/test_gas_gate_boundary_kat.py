"""
Boundary KAT: EIP-7778/8037 sequential REGULAR-gas inclusion gate and the
EIP-7623/7976 calldata-floor clamp (Amsterdam).

Mechanism (verified against the vendored reference):

* ``check_transaction`` (fork.py:583-596) rejects a tx at inclusion when
  ``min(TX_MAX_GAS_LIMIT, tx.gas) > block_gas_limit - block_gas_used``
  (regular dimension; strict greater-than fails). ``block_gas_used``
  accumulates per-tx regular increments
  ``max(tx_gas_used_before_refund - max(0, tx_state_gas), calldata_floor)``
  (fork.py:1177-1181) over PRIOR txs. A tx whose execution fails still
  contributes its full regular burn (gas_left = 0 on exceptional halt, so
  ``tx_gas_used_before_refund = tx.gas``, fork.py:1149-1159).

* Calldata floor (transactions.py:638-757): under EIP-7976 every calldata
  byte counts ``TX_DATA_TOKEN_STANDARD`` (4) floor tokens uniformly, so
  ``calldata_floor = len(data) * 4 * TX_DATA_TOKEN_FLOOR(16)
  + base_regular_gas``, where ``base_regular_gas = TX_BASE(12000)
  + COLD_ACCOUNT_ACCESS(3000)`` for a non-self call (plus
  ``TRANSFER_LOG_COST(1756) + TX_VALUE_COST(4244)`` when sending value).
  ``validate_transaction`` (transactions.py:620-621) rejects when
  ``calldata_floor > tx.gas``; ``process_transaction`` clamps the charged
  gas to ``max(tx_gas_used_after_refund, calldata_floor)`` (fork.py:1159).

Fixture A (2-tx blocks, block gas limit 500000): tx0 is a plain value
transfer (gas 21000, success, contributes exactly 21000 regular). tx1 is a
plain value transfer whose gas limit probes the regular gate:

* A1 control: tx1.gas = 479000 -- exactly ``500000 - 21000``; strict ``>``
  accepts. Reference-valid; expect successful_validation = 1.
* A2 edge: tx1.gas = 479001 -- one above; the reference REJECTS tx1 at
  inclusion (GasUsedExceedsLimitError), block invalid, expect
  successful_validation = 0.
* A3 failed-tx accumulation: tx0 calls an infinite-loop contract with
  gas 100000 and OOGs (status 0), burning all 100000 into block regular;
  tx1.gas = 400001 -- one above ``500000 - 100000``; the reference
  rejects tx1, expect successful_validation = 0. (A "transfer with
  insufficient balance" cannot serve here: check_transaction raises
  InsufficientBalanceError BEFORE execution, so such a tx never enters the
  block and burns nothing; an executed-then-halted tx is the only shape
  that contributes a full regular burn.)

Fixture B (1-tx blocks, block gas limit 500000): a single valueless tx to
a plain funded account with 1000 zero calldata bytes.
  intrinsic regular = 15000 + 4*1000 = 19000
  calldata_floor    = 15000 + 64*1000 = 79000  (floor dominates:
  used-after-refund would be only 19000)

* B1 control: tx.gas = 79000 -- exactly the floor; the reference accepts
  and the block-regular charge clamps to the floor (79000). Expect
  successful_validation = 1.
* B2 edge: tx.gas = 78999 -- one below the floor; the reference rejects
  at the intrinsic floor check (InsufficientTransactionGasError), block
  invalid, expect successful_validation = 0.
"""

from execution_testing import (
    Alloc,
    Block,
    BlockchainTestFiller,
    BlockException,
    Environment,
    Fork,
    Header,
    Op,
    RecipientType,
    Transaction,
    TransactionException,
    TransactionReceipt,
)

import pytest

pytestmark = pytest.mark.valid_from("Amsterdam")

BLOCK_GAS_LIMIT = 500_000

# --- Fixture A arithmetic (regular gate) --------------------------------
# Plain value transfer EOA -> pre-funded EOA, value 1:
#   intrinsic = TX_BASE 12000 + COLD_ACCOUNT_ACCESS 3000
#               + TRANSFER_LOG_COST 1756 + TX_VALUE_COST 4244 = 21000
TRANSFER_GAS = 21_000

# tx0 (A1/A2): successful plain transfer, contributes exactly 21000.
REGULAR_AVAILABLE_AFTER_TX0 = BLOCK_GAS_LIMIT - TRANSFER_GAS  # 479000
TX1_GAS_CONTROL = REGULAR_AVAILABLE_AFTER_TX0  # strict > accepts
TX1_GAS_EDGE = REGULAR_AVAILABLE_AFTER_TX0 + 1  # strict > rejects

# tx0 (A3): call to an infinite-loop contract, gas 100000, OOG.
#   intrinsic = TX_BASE 12000 + COLD_ACCOUNT_ACCESS 3000 = 15000
#   execution gas = 85000, all burned; gas_left = 0 -> full 100000
#   regular burn (status 0, no refund, floor 15000 < 100000).
FAILED_TX0_GAS_LIMIT = 100_000
FAILED_TX0_INTRINSIC = 15_000
REGULAR_AVAILABLE_AFTER_FAILED_TX0 = BLOCK_GAS_LIMIT - FAILED_TX0_GAS_LIMIT
TX1_GAS_FAILED_TX0_EDGE = REGULAR_AVAILABLE_AFTER_FAILED_TX0 + 1  # 400001
assert REGULAR_AVAILABLE_AFTER_FAILED_TX0 == 400_000

# --- Fixture B arithmetic (calldata floor clamp) -------------------------
FLOOR_ZERO_BYTES = 1_000
# EIP-7976: uniform 4 floor tokens per byte * TX_DATA_TOKEN_FLOOR 16.
CALLDATA_FLOOR = 15_000 + 4 * 16 * FLOOR_ZERO_BYTES  # 79000
CALLDATA_INTRINSIC_REGULAR = 15_000 + 4 * FLOOR_ZERO_BYTES  # 19000
assert CALLDATA_FLOOR == 79_000
assert CALLDATA_INTRINSIC_REGULAR == 19_000
# The floor dominates: used-after-refund (no code at recipient) is the
# intrinsic regular gas, far below the floor.
assert CALLDATA_INTRINSIC_REGULAR < CALLDATA_FLOOR
FLOOR_TX_GAS_CONTROL = CALLDATA_FLOOR  # exact floor -> accepted
FLOOR_TX_GAS_EDGE = CALLDATA_FLOOR - 1  # one below -> rejected


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


def _regular_gate_scenario(
    pre: Alloc,
    fork: Fork,
    tx1_gas_limit: int,
) -> list[Transaction]:
    """Build the two-tx regular-gate scenario (tx0 successful transfer)."""
    intrinsic_cost_calc = fork.transaction_intrinsic_cost_calculator()
    assert (
        intrinsic_cost_calc(
            calldata=b"",
            sends_value=True,
            recipient_type=RecipientType.EOA,
        )
        == TRANSFER_GAS
    )

    tx0 = _plain_transfer_tx(
        pre,
        gas_limit=TRANSFER_GAS,
        cumulative_gas_used=TRANSFER_GAS,
    )
    tx1 = _plain_transfer_tx(
        pre,
        gas_limit=tx1_gas_limit,
        cumulative_gas_used=(
            TRANSFER_GAS + TRANSFER_GAS
            if tx1_gas_limit == TX1_GAS_CONTROL
            else None
        ),
    )
    return [tx0, tx1]


def test_regular_gate_control(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    A1 control: tx1 gas_limit exactly equals the regular budget remaining
    after tx0 (500000 - 21000 = 479000). The gate is strict-greater-fail
    (fork.py:592), so the reference ACCEPTS the block.

    Expect successful_validation = 1. Header gas_used pins the two 21000
    burns (42000).
    """
    txs = _regular_gate_scenario(pre, fork, TX1_GAS_CONTROL)

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=txs,
                gas_limit=BLOCK_GAS_LIMIT,
                header_verify=Header(gas_used=2 * TRANSFER_GAS),
                expected_stateless_validation_success=True,
            )
        ],
        post={},
    )


@pytest.mark.exception_test
def test_regular_gate_edge(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    A2 edge: tx1 gas_limit is one above the remaining regular budget
    (479001 > 500000 - 21000), so the reference REJECTS tx1 at inclusion
    (GasUsedExceedsLimitError) and the block is invalid.

    The state dimension is not the cause (479001 <= 500000 - 0). Expect
    successful_validation = 0.
    """
    txs = _regular_gate_scenario(pre, fork, TX1_GAS_EDGE)

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


@pytest.mark.exception_test
def test_regular_gate_failed_tx_accumulation(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    A3: tx0 calls an infinite-loop contract with gas 100000 and OOGs
    (status 0). The exceptional halt zeroes gas_left, so the full 100000
    lands in block regular gas (fork.py:1149-1159, 1177-1181: floor 15000
    does not bind, no state gas). tx1 gas_limit = 400001 is one above the
    remaining regular budget (500000 - 100000 = 400000), so the reference
    REJECTS tx1 at inclusion and the block is invalid.

    Verifies failed-tx contributions accumulate into the regular gate.
    Expect successful_validation = 0.
    """
    intrinsic_cost_calc = fork.transaction_intrinsic_cost_calculator()
    assert (
        intrinsic_cost_calc(
            calldata=b"",
            sends_value=False,
            recipient_type=RecipientType.CONTRACT,
        )
        == FAILED_TX0_INTRINSIC
    )

    loop_contract = pre.deploy_contract(code=Op.JUMPDEST + Op.JUMP(0))
    tx0 = Transaction(
        sender=pre.fund_eoa(),
        to=loop_contract,
        gas_limit=FAILED_TX0_GAS_LIMIT,
        max_fee_per_gas=10,
        max_priority_fee_per_gas=0,
        expected_receipt=TransactionReceipt(
            status=0,
            cumulative_gas_used=FAILED_TX0_GAS_LIMIT,
        ),
    )
    tx1 = _plain_transfer_tx(
        pre,
        gas_limit=TX1_GAS_FAILED_TX0_EDGE,
        cumulative_gas_used=None,
    )

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=[tx0, tx1],
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


def _floor_scenario(
    pre: Alloc,
    fork: Fork,
    tx_gas_limit: int,
) -> Transaction:
    """Build the single calldata-floor-clamped transaction."""
    data_floor_calc = fork.transaction_data_floor_cost_calculator()
    data = bytes(FLOOR_ZERO_BYTES)
    assert (
        data_floor_calc(
            data=data,
            sends_value=False,
            recipient_type=RecipientType.EOA,
        )
        == CALLDATA_FLOOR
    )

    return Transaction(
        sender=pre.fund_eoa(),
        to=pre.fund_eoa(),
        data=data,
        gas_limit=tx_gas_limit,
        max_fee_per_gas=10,
        max_priority_fee_per_gas=0,
        expected_receipt=(
            TransactionReceipt(status=1, cumulative_gas_used=CALLDATA_FLOOR)
            if tx_gas_limit == FLOOR_TX_GAS_CONTROL
            else None
        ),
        error=(
            TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST
            if tx_gas_limit < CALLDATA_FLOOR
            else None
        ),
    )


def test_calldata_floor_control(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    B1 control: tx.gas exactly equals the calldata floor (79000 for 1000
    zero bytes). The reference ACCEPTS: intrinsic regular (19000) and the
    floor (79000) both fit tx.gas, execution uses nothing beyond
    intrinsic, and the charged gas clamps up to the floor
    (fork.py:1159). Expect successful_validation = 1; header gas_used
    pins the floor-dominated charge (79000).
    """
    tx = _floor_scenario(pre, fork, FLOOR_TX_GAS_CONTROL)

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=[tx],
                gas_limit=BLOCK_GAS_LIMIT,
                header_verify=Header(gas_used=CALLDATA_FLOOR),
                expected_stateless_validation_success=True,
            )
        ],
        post={},
    )


@pytest.mark.exception_test
def test_calldata_floor_edge(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    B2 edge: tx.gas is one below the calldata floor (78999 < 79000), so
    ``validate_transaction`` raises InsufficientTransactionGasError
    ("Insufficient calldata floor", transactions.py:620-621) and the
    block is invalid. Expect successful_validation = 0.
    """
    tx = _floor_scenario(pre, fork, FLOOR_TX_GAS_EDGE)

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=[tx],
                gas_limit=BLOCK_GAS_LIMIT,
                exception=(
                    TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST
                ),
                expected_stateless_validation_success=False,
            )
        ],
        post={},
    )
