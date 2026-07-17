"""
Adversarial KAT: a type-4 tx that PREP-HALTS inside ``set_delegation``
contributes ZERO state gas to the block state-gas inclusion gate
(Amsterdam: EIP-2780 + EIP-8037 + EIP-7702).

Mechanism (verified against the vendored reference, e5a8caf1b):

* ``process_message`` runs the whole top-frame preparation --
  ``set_delegation`` AND ``prepare_dispatch`` -- under one ``try``
  (interpreter.py:359-365). An ``ExceptionalHalt`` anywhere in that
  preparation lands in the same handler (interpreter.py:366-378) which
  rolls the state back to the pre-preparation snapshot, sets
  ``evm.auth_state_gas_used = 0`` (interpreter.py:373), refills the frame
  state gas, and burns all remaining regular gas. The tx output then
  carries ``state_gas_used = 0`` (interpreter.py:172), so the failed tx
  adds 0 to ``block_output.block_state_gas_used`` (fork.py:1174-1182)
  while its full gas limit lands in ``block_output.block_gas_used``
  (fork.py:1149-1159, 1177-1181).

* tx0 is a type-4 set-code tx with ONE authorization whose authority is a
  fresh, never-before-seen address (no pre-state leaf). Its execution gas
  after intrinsic (200000 - 22816 = 177184) is smaller than the first
  state charge of ``set_delegation`` -- ``StateGasCosts.NEW_ACCOUNT``
  (120 * 1530 = 183600, eoa_delegation.py:258-259 via
  vm/gas.py:331-339) -- so the tx OOGs at that charge with the state
  reservoir empty (tx.gas < TX_MAX_GAS_LIMIT 16777216,
  transactions.py:63, so ``state_gas_reservoir = 0``, fork.py:1098-1101).
  The would-be auth state gas (NEW_ACCOUNT 183600 + AUTH_BASE 23 * 1530
  = 35190, total 218790, eoa_delegation.py:278-279) is never reached in
  full and -- per the zeroing above -- contributes NOTHING to the block
  state dimension. Receipt: status 0, cumulative 200000.

* Halt-point choice (deviation from the naive "halt in prepare_dispatch"
  shape, with the arithmetic): ``prepare_dispatch`` does charge regular
  gas after ``set_delegation`` -- WARM_ACCESS 100 / COLD_ACCOUNT_ACCESS
  3000 to resolve a delegated recipient (interpreter.py:294-300,
  vm/gas.py:69-70) -- so an OOG there is possible, but only for
  tx0.gas >= 22816 + 8000 + 218790 = 249606 (surviving set_delegation).
  A prep-halt burns the WHOLE tx0.gas as regular, leaving
  500000 - tx0.gas <= 250394 < 281210 = 500000 - 218790 of regular
  budget: the reference's own regular gate (fork.py:592) then rejects the
  probe tx before the guest's state gate can diverge -- the FR window
  ``(500000 - 218790, 500000 - tx0.gas]`` is non-empty iff
  tx0.gas < 218790, which forces the halt INSIDE ``set_delegation``.
  (253000 would even survive prepare_dispatch with 3394 left and OOG in
  execution instead -- the retained-auth shape of
  test_auth_retention_kat.py, i.e. the opposite 0-FA direction.)

* After tx0: block regular gas used = 200000, block state gas used = 0.
  Reference remaining budgets for tx1: regular 300000, state 500000
  (fork.py:583-596). A guest that unconditionally charges the block for
  tx0's 218790 auth state gas instead sees only 281210 of state budget:
  the FR window is (281210, 300000].

* tx1 is a plain value transfer on a disjoint account lane
  (BAL-independent), gas used 21000 (= 12000 TX_BASE + 3000
  COLD_ACCOUNT_ACCESS + 1756 TRANSFER_LOG_COST + 4244 TX_VALUE_COST,
  transactions.py:698-703).

  * CONTROL: tx1.gas = 281210 -- exactly the over-counting guest's
    shrunk state budget; the gate is strict-greater-fail
    (fork.py:595-596), so even such a guest accepts. Reference accepts
    (281210 <= 300000 regular, <= 500000 state). Expect succ = 1.
  * OVERCOUNT: tx1.gas = 300000 -- exactly the reference's remaining
    regular budget (accepted), strictly inside the FR window. Reference
    accepts -> expected succ = 1. A guest that over-counts the failed
    tx0's auth state gas rejects tx1 (300000 > 281210) -> succ = 0,
    i.e. FALSE-REJECT. A guest that zeroes the rolled-back preparation
    (as the reference does) accepts -> full match.

Header gas_used pin: max(block_gas_used, block_state_gas_used)
(fork.py:370-373) = max(221000, 0) = 221000, and receipts pin tx0's
failure (status 0, cumulative 200000) and tx1's success (cumulative
221000). No reference patching: the FR direction means the honest
fixture itself is the probe.
"""

from execution_testing import (
    Account,
    Address,
    Alloc,
    AuthorizationTuple,
    Block,
    BlockchainTestFiller,
    Environment,
    Fork,
    Header,
    Op,
    Transaction,
    TransactionReceipt,
)

import pytest

pytestmark = pytest.mark.valid_from("Amsterdam")

# --- Gas arithmetic (Amsterdam constants, see module docstring) --------
AUTH_STATE_GAS_WOULD_BE = 218_790  # NEW_ACCOUNT 183600 + AUTH_BASE 35190
NEW_ACCOUNT_STATE_GAS = 183_600  # eoa_delegation.py:259 first charge

BLOCK_GAS_LIMIT = 500_000

# tx0 (type 4, one fresh-authority auth, empty calldata, value 0):
#   intrinsic regular = TX_BASE 12000 + COLD_ACCOUNT_ACCESS 3000
#                       + REGULAR_PER_AUTH_BASE_COST 7816 = 22816
#   execution gas     = 200000 - 22816 = 177184 < 183600 = NEW_ACCOUNT
#                       -> OutOfGasError at the first set_delegation
#                       charge (state reservoir 0), prep-halt.
TX0_GAS_LIMIT = 200_000
TX0_INTRINSIC_REGULAR = 22_816
assert (
    TX0_GAS_LIMIT - TX0_INTRINSIC_REGULAR == 177_184 < NEW_ACCOUNT_STATE_GAS
)
TX0_CUMULATIVE_GAS = TX0_GAS_LIMIT  # prep-halt burns everything

# Reference budgets after tx0 (state contribution zeroed, full regular burn).
REGULAR_AVAILABLE_AFTER_TX0 = BLOCK_GAS_LIMIT - TX0_GAS_LIMIT  # 300000
STATE_AVAILABLE_AFTER_TX0 = BLOCK_GAS_LIMIT  # state used = 0
# Over-counting guest's state budget: 500000 - 218790 = 281210.
GUEST_STATE_AVAILABLE_IF_OVERCOUNTING = BLOCK_GAS_LIMIT - AUTH_STATE_GAS_WOULD_BE
assert GUEST_STATE_AVAILABLE_IF_OVERCOUNTING == 281_210

# tx1 (plain value transfer EOA -> pre-funded EOA): gas used 21000.
TX1_GAS_USED = 21_000
TX1_GAS_CONTROL = GUEST_STATE_AVAILABLE_IF_OVERCOUNTING  # 281210
TX1_GAS_OVERCOUNT = REGULAR_AVAILABLE_AFTER_TX0  # 300000, in the FR window
assert GUEST_STATE_AVAILABLE_IF_OVERCOUNTING < TX1_GAS_OVERCOUNT

BLOCK_REGULAR_GAS = TX0_GAS_LIMIT + TX1_GAS_USED  # 221000
BLOCK_STATE_GAS = 0  # the point of the KAT: prep-halt zeroes tx0's auth gas
BLOCK_HEADER_GAS_USED = max(BLOCK_REGULAR_GAS, BLOCK_STATE_GAS)  # 221000
TX1_CUMULATIVE_GAS = TX0_CUMULATIVE_GAS + TX1_GAS_USED  # 221000


def _scenario(
    pre: Alloc,
    fork: Fork,
    tx1_gas_limit: int,
) -> tuple[list[Transaction], Address, Address]:
    """Build the shared two-tx KAT scenario."""
    # Delegation target of tx0's authorization. The delegated code never
    # runs: tx0 halts at the first set_delegation charge, before the
    # delegation is even written.
    halt_contract = pre.deploy_contract(
        code=Op.JUMPDEST + Op.PUSH1(1) + Op.PUSH1(0) + Op.SSTORE + Op.JUMP(0)
    )

    # Fresh, never-before-seen authority (zero-balance empty account:
    # no leaf pre-tx -> NEW_ACCOUNT would be charged first at
    # set_delegation -- the charge tx0 cannot afford).
    authority = pre.fund_eoa(amount=0)
    authorization_list = [
        AuthorizationTuple(
            address=halt_contract,
            nonce=0,
            signer=authority,
            creates_account=True,
            writes_delegation=True,
        )
    ]

    # Pin the would-be charge schedule to the fork calculators.
    top_frame_state = fork.transaction_top_frame_state_gas(
        authorizations=authorization_list
    )
    assert top_frame_state == AUTH_STATE_GAS_WOULD_BE, (
        f"top-frame state gas {top_frame_state} != {AUTH_STATE_GAS_WOULD_BE}"
    )

    tx0 = Transaction(
        ty=4,
        sender=pre.fund_eoa(),
        to=authority,
        gas_limit=TX0_GAS_LIMIT,
        max_fee_per_gas=10,
        max_priority_fee_per_gas=0,
        authorization_list=authorization_list,
        expected_receipt=TransactionReceipt(
            status=0,
            cumulative_gas_used=TX0_CUMULATIVE_GAS,
        ),
    )

    # tx1 must not share any account with tx0 (BAL-independent).
    recipient = pre.fund_eoa()
    tx1 = Transaction(
        sender=pre.fund_eoa(),
        to=recipient,
        value=1,
        gas_limit=tx1_gas_limit,
        max_fee_per_gas=10,
        max_priority_fee_per_gas=0,
        expected_receipt=TransactionReceipt(
            status=1,
            cumulative_gas_used=TX1_CUMULATIVE_GAS,
        ),
    )
    return [tx0, tx1], authority, halt_contract


def test_prep_halt_auth_control(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    Control: tx1 gas_limit exactly equals the state-gas budget a guest
    that over-counts tx0's (zeroed) auth state gas would compute
    (500000 - 218790 = 281210). Strict-greater-fail means every correct
    or over-counting implementation accepts; the reference accepts with
    300000 regular and 500000 state to spare.

    Expect successful_validation = 1. Receipts pin tx0's prep-halt
    (status 0, full 200000 burn) and the header pin (221000) proves the
    block state-gas dimension stayed empty.
    """
    txs, authority, _ = _scenario(pre, fork, TX1_GAS_CONTROL)

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=txs,
                gas_limit=BLOCK_GAS_LIMIT,
                header_verify=Header(gas_used=BLOCK_HEADER_GAS_USED),
                expected_stateless_validation_success=True,
            )
        ],
        post={
            # The preparation rollback never materialized the authority.
            authority: Account.NONEXISTENT,
        },
    )


def test_prep_halt_auth_overcount(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    Probe: tx1 gas_limit = 300000 exactly equals the reference's
    remaining regular budget (500000 - 200000) and sits strictly inside
    the false-reject window (281210, 300000] that opens only if the
    guest charges the block for tx0's zeroed 218790 auth state gas.

    The reference ACCEPTS (300000 <= 300000 regular, <= 500000 state):
    expected_stateless_validation_success = True. A guest whose
    sequential inclusion gate retains the prep-halted tx's auth state
    gas rejects tx1 (300000 > 281210) -> succ mismatch (exp 1, act 0),
    confirming the false-reject. A guest that zeroes the rolled-back
    preparation matches the reference -> full match.
    """
    txs, authority, _ = _scenario(pre, fork, TX1_GAS_OVERCOUNT)

    blockchain_test(
        genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
        pre=pre,
        blocks=[
            Block(
                txs=txs,
                gas_limit=BLOCK_GAS_LIMIT,
                header_verify=Header(gas_used=BLOCK_HEADER_GAS_USED),
                expected_stateless_validation_success=True,
            )
        ],
        post={
            authority: Account.NONEXISTENT,
        },
    )
