# BMV Multi-Tx Full-Capacity Plan

This note records the capacity decision for the BMV multi-transaction verdict
path. The Amsterdam execution target is a 200,000,000 gas block. At the minimum
21,000 gas per transaction, a valid block can contain 9,523 transactions, so a
full-capacity path must not treat the current 16-entry multi-tx arena as a
semantic limit. The active loop cap has since been raised to 1,024, while some
older helper-local tables are still 16-entry and the full 9,523 target remains
unfinished.

## Current Limits

The current `main` implementation has several independent ceilings:

- `BlockVerdictFunction.lean` gates the multi-tx runtime loop at
  `bvMtxActiveTxCap = 1024` transactions before `bal_txs_independent`.
- The cheap runtime-result arrays in `BlockVerdictDataSection.lean` are now
  sized from `bvMtxFullTxCap = 9523`:
  `bv_mtx_gas_left`, `bv_mtx_refund`, `bv_mtx_calldata`,
  `bv_tx_status_arr`, `bv_tx_log_window`, `bvgr_tx_gas_limits`,
  `bvgr_block_gas_increments`, `bvgr_tx_state_gas`,
  `bvgr_tx_exec_state_gas`, and `bvgr_receipt_gas_increments`.
- Active-loop-only helpers, including the recipient-credit helper, remain tied
  to `bvMtxActiveTxCap = 1024` until their algorithm slices land. Sender count,
  sender balance, and the skip list now use full-capacity post-loop tables.
- The multi-tx skip list stores `2N+1` 32-byte addresses. At 9,523
  transactions this is 19,047 entries, about 610 KiB, which is acceptable as a
  fixed arena if it remains the only large per-transaction helper.
- The sender sequencing checks are currently quadratic scans over prior public
  keys / skip-list entries. That is acceptable for fixture-sized tests, but not
  for the full gas-limit target.
- The active block-level `storage_writes` map uses the canonical
  `STORAGE_WRITES_AREA` with `storageWritesCapacity = 16384` 128-byte rows.
  `write_sets_incorporate_tx` upserts cumulative `(recipient, slotKey)` state;
  duplicate writes update the existing entry in place. The per-tx
  `TX_STORAGE_WRITES_AREA` plus undo journal remains the rollback container.
- Receipt/log validation has separate windows and byte arenas. Per-tx receipt
  records, record bloom storage, and record log descriptors derive from
  `bvMtxFullTxCap = 9523`; block-log descriptors, log data bytes, log-list RLP,
  receipt-list scratch/RLP, and consensus receipt descriptors remain separately
  capped. The 200M block-log capture targets are gas-derived, not tx-derived:
  `bvBlockLogFullDescTarget = 533333` cheapest LOG0 descriptors and
  `bvBlockLogFullDataBytes = 25000000` copied LOG data bytes.

## Decision

Use a staged design:

1. Keep the near-term static tx arena cap at 1,024 while the current algorithms
   are still being generalized. This covers the largest cached EEST stateless
   block observed by the local histogram tool (`tx_count = 1021`) without
   pretending to solve the full gas-limit case.
2. Introduce a named full-capacity constant of 9,523 and convert the cheap,
   truly per-transaction arrays to derived sizes from that constant. These are
   u64 arrays, status arrays, and 16-byte log-window descriptors. This
   foundation slice is landed as `bvMtxFullTxCap`, while the active loop stays
   separately named as `bvMtxActiveTxCap`.
3. Replace quadratic sender counting with a deterministic per-sender aggregation
   table that is explicitly sized or chunked for 9,523 transactions. This table
   should serve both exact nonce sequencing and sender debit/balance aggregation.
4. Do not scale committed storage as `transactions * storage-writes`.
   The canonical block map counts unique `(recipient, slotKey)` entries, not
   raw writes, so duplicate-heavy blocks preserve latest-write-wins without a
   second cross-transaction cache. More than 16,384 unique keys remains
   conservative capacity debt for a later streaming design.
5. Treat receipt/log capacity separately from transaction count. Full-capacity
   receipt validation should consume per-tx windows plus a log/receipt stream or
   digest substrate instead of allocating a worst-case static log body per
   transaction.
6. Every capacity overflow must remain conservative: if a helper cannot prove
   the exact block property within its arena, it must leave the relevant gate
   inactive or reject only when the spec violation is already proven. It must
   never under-count gas, state gas, nonce increments, sender debits, storage
   writes, or logs.

This chooses a hybrid static/streaming strategy. Static arrays are acceptable
where the upper bound is exactly the tx count and the bytes are small. Tables
whose natural size is keyed by senders, storage writes, or logs need dedicated
algorithms and tests, because a 9,523-wide tx cap does not bound them tightly
enough to make a blind static allocation a maintainable interface.

## Canonical storage-map classification

The canonical block map is exact up to `storageWritesCapacity = 16384` unique
`(recipient, slotKey)` rows. It is populated by `write_sets_incorporate_tx` and
read by `storagePrestateResolveAsm` and BAL storage-change emission through
`storage_writes_block_latest_value`. The former cross-transaction duplicate
table was separately populated and consumed, so it is removed rather than kept
as a cache with an equality invariant.

## Implementation Beads

The follow-up work should land in separate PRs:

- Landed foundation: `bvMtxActiveTxCap = 1024` names the current loop cap,
  `bvMtxFullTxCap = 9523` names the 200M target, and cheap per-tx u64/status/
  log-window arenas derive their byte sizes from the full cap.
- Sender nonce aggregation stack: `evm-asm-vv4hr.1.3.1` sizes the B1
  sender-count table to the 9,523 full cap, `.1.3.2` removes the old
  16-entry exact nonce seen table, `.1.3.3` replaces the in-loop exact nonce
  scan with indexed sender-table lookup, and `.1.3.4` adds frontier evidence.
  The focused `scripts/codegen-zisk-b1-sender-count-table-check.sh` probe now
  covers repeated-sender sequencing, nonce reuse rejection, too-high nonce
  rejection, 17-entry survival, 1024/1025 boundaries, and a 9,523-entry
  lower-level frontier for the exact lookup/running-count substrate.
- Skip-list/nth-context stack: `evm-asm-vv4hr.1.5` sizes the multi-tx
  BAL skip-list from `bvMtxFullTxCap`, so `{sender_i, recipient_i}` plus
  coinbase has `2 * 9523 + 1` entries, and adds a focused
  `scripts/codegen-zisk-multi-tx-nth-context-check.sh` probe for 1024, 1025,
  9523, and `index == count` out-of-range behavior.
- Landed sender balance aggregation: `evm-asm-vv4hr.1.4` sizes the B2 running
  sender-balance table from `bvMtxSenderBalanceEntries = bvMtxFullTxCap`, so
  distinct-sender balance tracking no longer inherits the active loop cap.
- Landed canonical block-storage threading: `write_sets_incorporate_tx`
  populates `STORAGE_WRITES_AREA`, while
  `storage_writes_block_latest_value` serves prestate and BAL preload reads.
- Extend canonical storage beyond 16,384 unique `(recipient, slotKey)` entries
  with a streaming/indexed design if the execution-derived upper bound grows;
  do not reintroduce a separately populated committed-storage cache.
- Decouple the remaining receipt/log validation capacity from the tx cap and
  connect block-log capture, log-list RLP, receipt-list RLP, and consensus
  descriptor traversal to the log/receipt streaming or digest substrate. The
  first block-log capture target is static and gas-derived: `533333` descriptors
  (`200000000 / 375`) and `25000000` copied data bytes (`200000000 / 8`). The
  per-tx receipt record storage is already full-capacity.
- Full-capacity evidence wrapper: `scripts/codegen-bmvmx-full-capacity-probes.sh`
  now resolves both `bvMtxActiveTxCap` and `bvMtxFullTxCap`, scans available
  EEST fixtures for the observed 1,021-tx frontier, and generates synthetic
  block-body transaction-count probes for 1,021, 1,024, 1,025, and 9,523
  transactions. Its output intentionally distinguishes `within-active` from
  `above-active-within-full`: the sender nonce, sender balance, and nth-context
  substrates have lower-level 9,523 evidence, but end-to-end stateless execution
  above `bvMtxActiveTxCap` remains a separate active-loop migration item.
