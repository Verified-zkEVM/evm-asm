"""Protected EEST generator for the account-builder running-baseline probe.

The BAL builder must use the block-cumulative account value when an address
was already written by an earlier transaction, falling back to parent state
only when the address is absent from the block map
(`block_access_lists.py:_get_pre_tx_account`).  Most simple fixtures are
baseline-agnostic: parent and running values both differ from the final tx
value, so they emit under either implementation.

This fixture is deliberately not baseline-agnostic.  tx1 sends 100 wei to
``target`` through a separate SELFDESTRUCTing funder, so target's parent
balance is 0 and its post-tx1 balance is 100.  tx2 sends 50 wei to target and
target forwards exactly CALLVALUE to recipient.  Target is written in tx2 but
its final balance remains 100.

Therefore the correct running baseline (100) suppresses a tx2 balance change;
a fixed parent baseline (0) spuriously emits one.  Do not remove this awkward
two-transaction control when trimming fixtures: it protects the only
discriminating balance cell for the running-baseline rule.

Reproduce from the execution-specs submodule:

  uv run fill scripts/kat/test_account_builder_prior_baseline_kat.py \
      --fork=Amsterdam -m blockchain_test --output=/tmp/account-builder-kat \
      --no-html --clean
"""

import pytest

from execution_testing import (
    Alloc,
    AuthorizationTuple,
    Block,
    BlockchainTestFiller,
    Op,
    Transaction,
)


pytestmark = pytest.mark.valid_from("Amsterdam")


def test_prior_block_touched_equal_balance(
    pre: Alloc, blockchain_test: BlockchainTestFiller
) -> None:
    alice = pre.fund_eoa()
    recipient = pre.fund_eoa(amount=0)
    target = pre.deploy_contract(
        code=(
            Op.SSTORE(0, Op.SELFBALANCE)
            + Op.CALL(0, recipient, Op.CALLVALUE, 0, 0, 0, 0)
            + Op.STOP
        ),
        balance=0,
    )
    funder = pre.deploy_contract(code=Op.SELFDESTRUCT(target), balance=0)

    blockchain_test(
        pre=pre,
        blocks=[
            Block(
                txs=[
                    Transaction(sender=alice, to=funder, value=100),
                    Transaction(nonce=1, sender=alice, to=target, value=50),
                ]
            )
        ],
        post={},
    )


def test_prior_block_touched_equal_delegation_code(
    pre: Alloc, blockchain_test: BlockchainTestFiller
) -> None:
    """Preserve the same-delegation code discriminator for #10741.

    Both authorizations are valid: authority nonce 0 is consumed by tx1 and
    nonce 1 by tx2.  Both install the same delegation designator.  Thus the
    code field is written in tx2 yet equals its post-tx1 running baseline, so
    the canonical BAL has one code change (BAI 1) rather than a spurious BAI 2
    entry.  The authority nonce is intentionally changed in both txs; nonce
    has no touched-equal discriminator because Amsterdam only increments it.
    """
    authority = pre.fund_eoa()
    relayer = pre.fund_eoa()
    recipient = pre.fund_eoa(amount=0)
    delegate = pre.deploy_contract(code=Op.STOP)

    blockchain_test(
        pre=pre,
        blocks=[
            Block(
                txs=[
                    Transaction(
                        sender=relayer,
                        to=recipient,
                        authorization_list=[
                            AuthorizationTuple(
                                address=delegate, nonce=0, signer=authority
                            )
                        ],
                    ),
                    Transaction(
                        nonce=1,
                        sender=relayer,
                        to=recipient,
                        authorization_list=[
                            AuthorizationTuple(
                                address=delegate, nonce=1, signer=authority
                            )
                        ],
                    ),
                ]
            )
        ],
        post={},
    )
