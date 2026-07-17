"""
Adversarial KAT: a failed 7702 tx retains its authorization state gas in
the block state-gas inclusion gate (Amsterdam: EIP-2780 + EIP-8037).

Scenario (single block, two txs sharing no accounts):

* tx0 is a type-4 set-code tx with ONE authorization whose authority is a
  fresh, never-before-seen address. ``set_delegation`` charges
  ``NEW_ACCOUNT`` (183600) + ``AUTH_BASE`` (35190) = 218790 state gas at
  the top frame (fork.py -> eoa_delegation.py). The authority delegates to
  a contract whose code is an SSTORE loop that runs out of gas *after*
  ``set_delegation`` succeeded. The tx halts (status 0), the frame's own
  state gas is refilled, but ``evm.auth_state_gas_used`` = 218790 is
  folded into ``tx_output.state_gas_used`` (interpreter.py:172) and
  retained in ``block_output.block_state_gas_used`` (fork.py:1182).
* tx1 is a plain value transfer whose ``gas_limit`` G1 probes the
  state-dimension availability check in ``check_transaction``
  (fork.py:586-596):
  ``tx.gas > block_gas_limit - block_state_gas_used`` -> reject.

Block state gas limit: Amsterdam has no separate constant -- the state
dimension reuses ``block_env.block_gas_limit`` (fork.py:586-588), here
500000. After tx0: block_state_gas_used = 218790 (retained auth, tx0's
execution state gas was refilled on halt; intrinsic state gas = 0 under
EIP-2780), block_gas_used (regular) = 253000 - 218790 = 34210. Hence:
  * state-gate remaining   = 500000 - 218790 = 281210
  * regular-gate remaining = 500000 - 34210  = 465790
  * state-only rejection window: (281210, 465790]

* CONTROL: G1 = 281210 (exact boundary; strict ``>`` accepts).
  Reference accepts; expect successful_validation = 1. Header gas_used =
  max(55210, 218790) = 218790 pins the retained amount.
* EXPLOIT: G1 = 300000, strictly inside the window. The reference rejects
  tx1 (state dimension). The fixture is the ATTACKER-CRAFTED input: all
  derived data (state root, receipts root, BAL, bloom) computed AS IF tx1
  executed. Produced by monkey-patching ``check_transaction`` during the
  fill so its state-dimension comparison forgets the retained 218790
  (emulating a cheating prover's block builder), while forcing the
  canonical ``run_stateless_guest`` back to the strict reference check so
  the recorded statelessOutputBytes carry successful_validation = 0.

Reproduction (from a checkout of zksecurity/execution-specs at the v0.6.2
fill commit, e5a8caf1b, with this file copied to tests/kat_k3_3/):

    uv run fill tests/kat_k3_3/test_auth_retention_kat.py \
        --fork=Amsterdam -m blockchain_test --output=/tmp/kat-out --no-html --clean

produces
  blockchain_tests/for_amsterdam/kat_k3_3/auth_retention_kat/
    auth_retention_control.json / auth_retention_exploit.json
which are the two tracked fixtures under
fixtures/kat/eip8037-auth-retention/ in the evm-asm repo.
"""

import dataclasses
from typing import Any

import pytest
from execution_testing import (
    Account,
    Address,
    Alloc,
    AuthorizationTuple,
    Block,
    BlockchainTestFiller,
    Bytes,
    Environment,
    Fork,
    Header,
    Op,
    Transaction,
    TransactionReceipt,
)

import ethereum.forks.amsterdam.fork as amsterdam_fork
import ethereum.forks.amsterdam.stateless_guest as amsterdam_stateless_guest
import ethereum.forks.amsterdam.stateless_host as amsterdam_stateless_host
from ethereum_types.numeric import Uint

pytestmark = pytest.mark.valid_from("Amsterdam")

# --- Gas arithmetic (Amsterdam constants) --------------------------------
# StateGasCosts.NEW_ACCOUNT = 120 * 1530 = 183600
# StateGasCosts.AUTH_BASE   =  23 * 1530 =  35190
AUTH_STATE_GAS_RETAINED = 218_790  # NEW_ACCOUNT + AUTH_BASE

BLOCK_GAS_LIMIT = 500_000

# tx0 (type 4, one fresh-authority auth, empty calldata, value 0):
#   intrinsic regular  = TX_BASE 12000 + COLD_ACCOUNT_ACCESS 3000
#                        + REGULAR_PER_AUTH_BASE_COST 7816 = 22816
#   top-frame regular  = ACCOUNT_WRITE 8000 + delegation cold access 3000
#   top-frame state    = 218790 (all spill-funded from gas_left)
#   execution slack    = 394 (a few opcodes into the delegated SSTORE
#                        loop, then OOG)
TX0_GAS_LIMIT = 253_000
TX0_REGULAR_GAS = TX0_GAS_LIMIT - AUTH_STATE_GAS_RETAINED  # 34210
TX0_CUMULATIVE_GAS = TX0_GAS_LIMIT  # OOG: gas_left = 0, no refund

STATE_AVAILABLE_AFTER_TX0 = BLOCK_GAS_LIMIT - AUTH_STATE_GAS_RETAINED
REGULAR_AVAILABLE_AFTER_TX0 = BLOCK_GAS_LIMIT - TX0_REGULAR_GAS
assert STATE_AVAILABLE_AFTER_TX0 == 281_210
assert REGULAR_AVAILABLE_AFTER_TX0 == 465_790

# tx1 (plain value transfer EOA -> pre-funded EOA): intrinsic = 21000,
# no state gas (recipient alive), regular = 21000.
TX1_GAS_USED = 21_000
TX1_GAS_CONTROL = STATE_AVAILABLE_AFTER_TX0  # exact boundary -> accepted
TX1_GAS_EXPLOIT = 300_000  # in (281210, 465790] -> only state gate rejects

BLOCK_REGULAR_GAS = TX0_REGULAR_GAS + TX1_GAS_USED  # 55210
BLOCK_HEADER_GAS_USED = max(BLOCK_REGULAR_GAS, AUTH_STATE_GAS_RETAINED)
assert BLOCK_HEADER_GAS_USED == 218_790
TX1_CUMULATIVE_GAS = TX0_CUMULATIVE_GAS + TX1_GAS_USED  # 274000


_ORIG_CHECK_TRANSACTION = amsterdam_fork.check_transaction
_ORIG_RUN_STATELESS_GUEST = amsterdam_stateless_guest.run_stateless_guest
_ORIG_DESERIALIZE_STATELESS_OUTPUT = (
    amsterdam_stateless_host.deserialize_stateless_output
)


class _ForgetFailedTxAuthGas:
    """
    Monkey-patch scope emulating a cheating block builder whose
    state-dimension availability check forgets state gas retained from a
    failed tx's 7702 authorizations.

    ``check_transaction`` is wrapped so only the state-dimension
    comparison sees ``block_state_gas_used`` reduced by ``forgotten``;
    every other accounting step (state root, receipts, BAL, gas
    accumulators) stays reference-exact. ``run_stateless_guest`` is
    wrapped to force the strict reference check inside guest runs, so the
    canonical statelessOutputBytes record the true reference verdict.

    The EELS t8n has an internal sanity assert
    (evm_tools/t8n/t8n_types.py: ``assert result.successful_validation``)
    that fires on the crafted block -- it assumes every t8n-accepted
    block validates, exactly the invariant this attack breaks. The t8n
    records the RAW guest output bytes but asserts on the DECODED result,
    so a one-shot decode-lie (successful_validation=True) discharges only
    that self-check; the recorded bytes keep the strict succ=0 verdict.
    """

    def __init__(self, forgotten: int) -> None:
        """Record the retained amount the builder "forgets"."""
        self.forgotten = forgotten
        self.strict = False
        self.lie_succ_armed = False

    def _check_transaction(
        self,
        block_env: Any,
        block_output: Any,
        tx: Any,
        sender: Any,
        tx_state: Any,
    ) -> Any:
        """Relax only the state-dimension availability comparison."""
        if self.strict:
            return _ORIG_CHECK_TRANSACTION(
                block_env=block_env,
                block_output=block_output,
                tx=tx,
                sender=sender,
                tx_state=tx_state,
            )
        saved = block_output.block_state_gas_used
        block_output.block_state_gas_used = Uint(
            max(0, int(saved) - self.forgotten)
        )
        try:
            return _ORIG_CHECK_TRANSACTION(
                block_env=block_env,
                block_output=block_output,
                tx=tx,
                sender=sender,
                tx_state=tx_state,
            )
        finally:
            block_output.block_state_gas_used = saved

    def _run_stateless_guest(self, input_bytes: Any) -> Any:
        """Force the strict reference check during guest runs."""
        previous = self.strict
        self.strict = True
        try:
            output_bytes = _ORIG_RUN_STATELESS_GUEST(input_bytes)
        finally:
            self.strict = previous
        # Arm the one-shot decode-lie for the t8n's sanity assert, which
        # immediately follows this call inside Result.update.
        self.lie_succ_armed = True
        return output_bytes

    def _deserialize_stateless_output(self, data: Any) -> Any:
        """Discharge the t8n self-check once; raw bytes stay strict."""
        result = _ORIG_DESERIALIZE_STATELESS_OUTPUT(data)
        if self.lie_succ_armed:
            self.lie_succ_armed = False
            result = dataclasses.replace(
                result, successful_validation=True
            )
        return result

    def __enter__(self) -> "_ForgetFailedTxAuthGas":
        """Install all wrappers."""
        amsterdam_fork.check_transaction = self._check_transaction
        amsterdam_stateless_guest.run_stateless_guest = (
            self._run_stateless_guest
        )
        amsterdam_stateless_host.deserialize_stateless_output = (
            self._deserialize_stateless_output
        )
        return self

    def __exit__(self, *exc_info: Any) -> None:
        """Restore the reference implementations."""
        amsterdam_fork.check_transaction = _ORIG_CHECK_TRANSACTION
        amsterdam_stateless_guest.run_stateless_guest = (
            _ORIG_RUN_STATELESS_GUEST
        )
        amsterdam_stateless_host.deserialize_stateless_output = (
            _ORIG_DESERIALIZE_STATELESS_OUTPUT
        )


def _scenario(
    pre: Alloc,
    fork: Fork,
    tx1_gas_limit: int,
) -> tuple[list[Transaction], Address, Address]:
    """Build the shared two-tx KAT scenario."""
    # Delegated-to contract: an SSTORE loop that always runs out of gas
    # when entered with tx0's post-delegation slack (394 gas).
    halt_contract = pre.deploy_contract(
        code=Op.JUMPDEST + Op.PUSH1(1) + Op.PUSH1(0) + Op.SSTORE + Op.JUMP(0)
    )

    # Fresh, never-before-seen authority (zero-balance empty account:
    # no leaf pre-tx -> NEW_ACCOUNT + AUTH_BASE at set_delegation).
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

    # Pin the retained amount to the fork calculators.
    top_frame_state = fork.transaction_top_frame_state_gas(
        authorizations=authorization_list
    )
    assert top_frame_state == AUTH_STATE_GAS_RETAINED, (
        f"top-frame state gas {top_frame_state} != {AUTH_STATE_GAS_RETAINED}"
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


def test_auth_retention_control(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    Control: tx1 gas_limit exactly equals the state-gas budget remaining
    after tx0's retained 218790, so the reference ACCEPTS the block.

    A guest that correctly retains failed-tx auth state gas must output
    successful_validation = 1. The header gas_used pin (218790) proves
    tx0 failed yet its auth state gas was retained.
    """
    txs, authority, halt_contract = _scenario(pre, fork, TX1_GAS_CONTROL)

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
            authority: Account(
                nonce=1,
                balance=0,
                code=Bytes(b"\xef\x01\x00" + bytes(halt_contract)),
            )
        },
    )


def test_auth_retention_exploit(
    blockchain_test: BlockchainTestFiller,
    pre: Alloc,
    fork: Fork,
) -> None:
    """
    Exploit: tx1 gas_limit sits strictly inside the state-only rejection
    window (281210, 465790], so the reference REJECTS the block.

    The fixture is filled under a monkey-patch that forgets tx0's retained
    218790 in the state-dimension check only, so every derived value is
    computed as if tx1 had executed -- the input a cheating prover would
    submit to a guest that drops failed-tx auth state gas. The canonical
    reference guest still rejects it: statelessOutputBytes byte 32 == 0.
    A correct guest under test must also reject (succ match).
    """
    txs, _, _ = _scenario(pre, fork, TX1_GAS_EXPLOIT)

    with _ForgetFailedTxAuthGas(forgotten=AUTH_STATE_GAS_RETAINED):
        blockchain_test(
            genesis_environment=Environment(gas_limit=BLOCK_GAS_LIMIT),
            pre=pre,
            blocks=[
                Block(
                    txs=txs,
                    gas_limit=BLOCK_GAS_LIMIT,
                    header_verify=Header(gas_used=BLOCK_HEADER_GAS_USED),
                    expected_stateless_validation_success=False,
                )
            ],
            post={},
        )
