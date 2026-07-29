"""Protected EEST discriminator for #10764's N+1 withdrawal builder event.

One user transaction and one withdrawal credit the *same* account.  Amsterdam
therefore emits two balance changes for that address: BAI 1 has post balance 5,
and the post-transaction withdrawal at BAI 2 has post balance 10 gwei + 5.

This must not be simplified to a fresh withdrawal address: an address-only
event map would then look correct even though it collapses distinct BAI events.
The two post values are intentionally distinct from each other and from their
indices, so a field transposition cannot pass accidentally.

Reproduce from the execution-specs checkout:

  uv run fill scripts/kat/test_bai_nplus1_withdrawal_kat.py \
      --fork=Amsterdam -m blockchain_test --output=/tmp/bai-nplus1-kat \
      --no-html --clean
"""

import pytest

from execution_testing import (
    Alloc,
    BalAccountExpectation,
    BalBalanceChange,
    Block,
    BlockAccessListExpectation,
    BlockchainTestFiller,
    Transaction,
    Withdrawal,
)


pytestmark = pytest.mark.valid_from("Amsterdam")


def test_same_address_user_then_withdrawal_has_distinct_bais(
    pre: Alloc, blockchain_test: BlockchainTestFiller
) -> None:
    sender = pre.fund_eoa()
    target = pre.fund_eoa(amount=0)

    blockchain_test(
        pre=pre,
        blocks=[
            Block(
                txs=[Transaction(sender=sender, to=target, value=5)],
                withdrawals=[
                    Withdrawal(
                        index=0,
                        validator_index=0,
                        address=target,
                        amount=10,
                    )
                ],
                expected_block_access_list=BlockAccessListExpectation(
                    account_expectations={
                        target: BalAccountExpectation(
                            balance_changes=[
                                BalBalanceChange(
                                    block_access_index=1, post_balance=5
                                ),
                                BalBalanceChange(
                                    block_access_index=2,
                                    post_balance=10 * 10**9 + 5,
                                ),
                            ]
                        )
                    }
                ),
            )
        ],
        post={},
    )
