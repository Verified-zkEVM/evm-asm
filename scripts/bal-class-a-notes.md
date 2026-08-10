# Class-A allowlist annotations

<!-- annotation-count: 1 -->

<!-- #11183: retired guest jal bal_txs_independent (no spec counterpart; supplied
     BAL body read) and the deposit-capture-only route (spec has one tx loop;
     deposits from post-exec receipt logs). -->

## key: .Lbv_ret | bal_gas_valid_from_builder
- SETTLED NON-EDGE (genuine diagnostic, neither BIND nor CHECK). ReceiptsTail.lean:321 copies `bv_bal_len` into `bv_bal_shadow_supplied_len`; site comment: "neither value is a verdict input." Sole consumer is StatelessGuestEpilogue dump @ 0xa0010000+136. Zero reject branches on the cell. Nearby `bal_gas_valid_from_builder` is builder-only (fork.py:933-936; fail 7) and does not read this cell — KEEP. Retaining the Class-A reference deliberately; retiring it buys no equivalence. Do not drop without re-deriving consumers.
