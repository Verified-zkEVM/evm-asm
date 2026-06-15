# BMV Multi-Tx Full-Capacity Plan

This note records the capacity decision for the BMV multi-transaction verdict
path. The Amsterdam execution target is a 200,000,000 gas block. At the minimum
21,000 gas per transaction, a valid block can contain 9,523 transactions, so a
full-capacity path must not treat the current 16-entry multi-tx arena as a
semantic limit.

## Current Limits

The current `main` implementation has several independent ceilings:

- `BlockVerdictFunction.lean` gates the multi-tx runtime loop at 16
  transactions before `bal_txs_independent`.
- The runtime-result arrays in `BlockVerdictDataSection.lean` are 16-wide:
  `bv_mtx_gas_left`, `bv_mtx_refund`, `bv_mtx_calldata`,
  `bv_tx_status_arr`, `bv_tx_log_window`, `bvgr_tx_gas_limits`,
  `bvgr_block_gas_increments`, `bvgr_tx_state_gas`,
  `bvgr_tx_exec_state_gas`, and `bvgr_receipt_gas_increments`.
- The multi-tx skip list stores `2N+1` 32-byte addresses. At 9,523
  transactions this is 19,047 entries, about 610 KiB, which is acceptable as a
  fixed arena if it remains the only large per-transaction helper.
- The sender sequencing checks are currently quadratic scans over prior public
  keys / skip-list entries. That is acceptable for fixture-sized tests, but not
  for the full gas-limit target.
- `bv_mtx_committed` is a 128-entry table of 128-byte committed storage
  records. This is not a transaction-count cap. On the keyed-upsert path it is
  a unique `(recipient, slotKey)` cap: duplicate writes update the existing
  entry in place, while a 129th unique key remains conservative capacity debt.
- Receipt/log validation has separate windows and record arenas. Raising the tx
  cap alone does not cover blocks with many logs or large receipt material.

## Decision

Use a staged design:

1. Keep the near-term static tx arena cap at 1,024 while the current algorithms
   are still being generalized. This covers the largest cached EEST stateless
   block observed by the local histogram tool (`tx_count = 1021`) without
   pretending to solve the full gas-limit case.
2. Introduce a named full-capacity constant of 9,523 and convert the cheap,
   truly per-transaction arrays to derived sizes from that constant. These are
   u64 arrays, status arrays, and 16-byte log-window descriptors.
3. Replace quadratic sender counting with a deterministic per-sender aggregation
   table that is explicitly sized or chunked for 9,523 transactions. This table
   should serve both exact nonce sequencing and sender debit/balance aggregation.
4. Do not scale `bv_mtx_committed` as `transactions * storage-writes`.
   The current keyed-upsert design counts unique `(recipient, slotKey)` entries,
   not raw writes, so duplicate-heavy blocks can exceed the old 128-write shape
   while preserving latest-write-wins. More than 128 unique committed keys is
   still conservative debt for the streaming/chunked follow-up.
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

## Committed-Storage Classification

The committed-storage threading table now has a precise near-term model:

- Exact: up to `bvMtxCommittedCapacity = 128` unique `(recipient, slotKey)`
  entries. Each committed entry remains a 128-byte storage-log record.
- Exact above 128 raw writes when they collapse onto at most 128 unique keys.
  `bv_mtx_committed_snapshot_upsert` scans the existing table for the re-keyed
  recipient plus slot key and updates that entry in place, so later writes keep
  execution-specs last-write-wins behavior without consuming another slot.
- Conservative: more than 128 unique `(recipient, slotKey)` entries. The helper
  sets `bv_mtx_committed_overflow` and returns a nonzero status before writing
  past the table. A later streaming/chunked design is tracked by bead
  `evm-asm-bmvmx.5.5.7.4.4.4`.

Evidence lives in `scripts/codegen-zisk-mtx-committed-snapshot-upsert-check.sh`:
mode `highdup` writes 130 committed records to the same key and expects one
committed table entry with the latest value; mode `overflow` fills the table and
then attempts a new unique key, expecting conservative overflow and an unchanged
sentinel beyond capacity.

## Implementation Beads

The follow-up work should land in separate PRs:

- Define `bvMtxFullTxCap = 9523` and derive byte sizes for the cheap per-tx
  arrays; keep the current fixture cap separate until all consumers are ready.
- Replace the quadratic sender-count scans with a deterministic aggregation
  helper that handles 9,523 transactions.
- Extend the multi-tx sender debit / actual-balance checks to the same
  aggregation substrate.
- Landed keyed committed-storage upsert slices:
  `evm-asm-bmvmx.5.5.7.4.4.1` adds the helper/probe and
  `evm-asm-bmvmx.5.5.7.4.4.2` wires the multi-tx snapshot path through it.
- Extend committed-storage threading beyond 128 unique `(recipient, slotKey)`
  entries with a streaming or chunked design (`evm-asm-bmvmx.5.5.7.4.4.4`).
- Decouple receipt/log validation capacity from the tx cap and connect it to the
  log/receipt streaming or digest substrate.
- Add full-capacity probes: one fixture/regression for the observed 1,021-tx
  EEST case and one synthetic or generated near-9,523 transaction block.
