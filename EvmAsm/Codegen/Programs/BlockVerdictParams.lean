/-
  EvmAsm.Codegen.Programs.BlockVerdictParams

  Shared numeric parameters for the block-state-root / stateless-verdict-v2
  programs: static arena capacities and layout byte-widths.
  Extracted from BlockVerdict.lean so BlockVerdictDataSection.lean can share
  them without a circular import.
-/

import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmStorageAccessGas

namespace EvmAsm.Codegen

/-- Amsterdam's EIP-7928 `GasCosts.BLOCK_ACCESS_LIST_ITEM`.  This is the
    proven lower-bound divisor for an input-originated *distinct final state
    change*: `validate_block_access_list_gas_limit` charges one 2,000-gas BAL
    item per account and one per distinct storage slot (storage changes and
    reads are de-duplicated by slot).  It is deliberately not inferred from an
    EVM `SSTORE` price: BAL is the consensus-level accounting rule that bounds
    the final state-change input set. -/
def bsrBalGasCost : Nat := 2000

/-- Current Amsterdam resource target.  Keep capacities as functions of this
    value: changing the supported block gas limit must resize every fixed
    state-root builder arena rather than silently preserving a stale literal. -/
def bsrStateRootBlockGasLimit : Nat := 200000000

/-- Static BAL/state replay arena capacity.  EIP-7928 enforces
    `bal_items <= block_gas_limit / BLOCK_ACCESS_LIST_ITEM`, so a 200M block
    has at most 100,000 BAL items.  The later bounded builder accepts only the
    normalized distinct final changes plus the explicitly bounded auxiliary
    system/withdrawal changes below. -/
def bsrMaxBalItems : Nat := bsrStateRootBlockGasLimit / bsrBalGasCost
def bsrModeledSystemChanges : Nat := 2
def bsrMaxWithdrawalChanges : Nat := 16
def bsrMaxAuxChanges : Nat := bsrModeledSystemChanges + bsrMaxWithdrawalChanges
def bsrMaxStateChanges : Nat :=
  bsrMaxBalItems + bsrModeledSystemChanges + bsrMaxWithdrawalChanges

/-- State-trie keys are 32-byte hashes represented as 64 nibbles.  The sorted
    builder uses an in-place MSD partitioner: its only sort workspace is a
    bounded pending-range stack (one range per nibble fanout at each depth),
    never attacker-sized bucket arrays. -/
def bsrMptKeyNibbles : Nat := 64
def bsrMptRadixFanout : Nat := 16
def bsrMptSortRangeStackCapacity : Nat := bsrMptKeyNibbles * bsrMptRadixFanout
def bsrMptSortRangeFrameBytes : Nat := 32

/-- A Patricia trie has at most one active construction frame per consumed key
    nibble plus its root frame.  This is depth-derived, not input-count-derived. -/
def bsrMptBuilderFrameCapacity : Nat := bsrMptKeyNibbles + 1
/-- A builder frame records one Patricia depth, its input range, and all 17
    canonical child references (16 branch children plus the value slot).  Each
    reference may be an inline RLP item or a 33-byte hash reference, so this
    deliberately reserves a full 1 KiB frame rather than pretending that a
    handful of scalar words is enough.  The 65-frame array remains bounded by
    key depth only; it is never indexed by the number of untrusted changes. -/
def bsrMptBuilderFrameBytes : Nat := 1024
/-- The SSZ `ByteList[1024]` envelope caps every pre-state witness node.  The
    bounded builder also uses this as its maximum one-node re-encoding buffer;
    larger reconstructed nodes are rejected before they can reach a frame. -/
def bsrMptNodeMaxBytes : Nat := bsrMptBuilderFrameBytes
/-- Canonical pre-state branch-child references are at most 32 raw bytes:
    either an inline RLP encoding (<32) or a 32-byte hash.  A frontier frame
    stores the raw reference length followed by the bytes, rounded to 40 B;
    all sixteen branch children therefore consume 640 B of its 1 KiB budget.
    The remaining 384 B is reserved for the range/depth bookkeeping and the
    branch value/reference produced while unwinding. -/
def bsrMptFrameChildRefBytes : Nat := 32
def bsrMptFrameChildRefStride : Nat := 40
def bsrMptFrameBranchChildrenBytes : Nat := bsrMptRadixFanout * bsrMptFrameChildRefStride
/-- Frame metadata immediately follows the sixteen retained child references. -/
def bsrMptFrameNodePtrOffset : Nat := bsrMptFrameBranchChildrenBytes
def bsrMptFrameNodeLenOffset : Nat := bsrMptFrameNodePtrOffset + 8
def bsrMptFrameNodeKindOffset : Nat := bsrMptFrameNodeLenOffset + 8
/-- Sixteen `{start,end}` ranges for the current nibble partition live after
    root metadata.  They are frame-local, so their capacity is depth-derived
    rather than proportional to untrusted change count. -/
def bsrMptFrameRangeTableOffset : Nat := bsrMptFrameNodeKindOffset + 8
def bsrMptFrameRangeStride : Nat := 16
def bsrMptFrameRangeTableBytes : Nat := bsrMptRadixFanout * bsrMptFrameRangeStride
/-- Extension metadata occupies the frame tail after the branch-range table.
    The decoded path is at most the remaining 64 state-key nibbles; it is
    deliberately not the SSZ node's potentially 2047-nibble compact path. -/
def bsrMptFrameExtensionPathLenOffset : Nat := bsrMptFrameRangeTableOffset + bsrMptFrameRangeTableBytes
def bsrMptFrameExtensionChildPtrOffset : Nat := bsrMptFrameExtensionPathLenOffset + 8
def bsrMptFrameExtensionChildLenOffset : Nat := bsrMptFrameExtensionChildPtrOffset + 8
def bsrMptFrameExtensionPathOffset : Nat := bsrMptFrameExtensionChildLenOffset + 8
def bsrMptFrameExtensionPathBytes : Nat := bsrMptKeyNibbles
def bsrMptFrameUsedBytes : Nat := bsrMptFrameExtensionPathOffset + bsrMptFrameExtensionPathBytes
/-- One shared node buffer is enough for depth-first construction: every
    completed child is reduced to its raw reference before its next sibling is
    built. This is independent of the gas-derived descriptor count. -/
def bsrMptBuilderNodeScratchBytes : Nat := bsrMptNodeMaxBytes

#guard bsrMptFrameUsedBytes <= bsrMptBuilderFrameBytes
def bsrMaxAccessAccounts : Nat := runtimeAccessAccountOutcomeCapacity
def bsrMaxAccountAccessOutcomes : Nat := runtimeAccessAccountOutcomeCapacity
def bsrMaxStorageAccessOutcomes : Nat := storageAccessOutcomeMaxRecords

/-- Per-account storage-slot staging capacity for the BAL key/preload helpers
    (`bal_recipient_storage_keys`, `bal_recipient_storage_reads_keys`,
    `stage_predeploy_storage_preload` and their consumer buffers `sps_keys` /
    `bvcd_keys` / `csce_keys` / `c1_preload`). One account's changes+reads can
    absorb the entire gas-derived BAL budget (storage reads are the cheapest
    BAL item), so the only bound that avoids conservative rejects of legitimate
    200M blocks is `bsrMaxBalItems` itself. Counts above this make the helpers
    write nothing and return the true count; callers bail conservatively
    (fhsxz.2.4.2.66.1.2 — the former 512 cap false-rejected queue-heavy
    blocks far below 200M). -/
def bsrAccountSlotCap : Nat := bsrMaxBalItems

/-- Max per-slot change-tuple count staged by `bal_slot_tuple_sequence`
    (consumer buffers `sps_tuples` / `atsc_balbuf` / `atsc_execbuf`, 40 B per
    tuple). A slot receives at most one net-change tuple per tx (plus the
    block-end system write and a possible seed entry), and a 200M block holds
    at most 200,000,000 / 21,000 = 9,523 txs; 10,000 adds margin. Above this
    the helper writes nothing and returns the true count — callers bail
    conservatively (also closes the .66.1.1 unbounded-write corruption). -/
def bsrMaxTuplesPerSlot : Nat := 10000

/-- Conservative upper bound on `witness.state` byte length accepted by
    `block_state_root`. Beyond this the post-state recompute bails conservatively
    (bsr_fail=111). This is a coarse size guard, NOT a fixed-buffer limit: the
    witness is read in place and the real structural bound is the sorted witness
    index node cap (8192, `MptWitnessIndex`). The earlier 262144 value
    false-rejected legitimately large state-creation blocks (EIP-8037 state-gas
    reservoir fixtures push >256 KiB witnesses, e.g. evm-asm-zbvak's 336 KB row);
    512 KiB keeps a guard while accepting those blocks. -/
def bsrMaxWitnessBytes : Nat := 524288

/-- Active multi-transaction execution-loop capacity. The cached `zkevm@v0.4.0`
    stateless fixtures include blocks with more than the old 16-entry arena
    cap, topping out at 1021 transactions. Keep this as the conservative loop
    gate while sender aggregation, skip-list traversal, and other non-cheap
    algorithms are generalized to the full 200M target. -/
def bvMtxActiveTxCap : Nat := 1024

/-- Full Amsterdam transaction capacity target from the 200M block-gas limit and
    the 21,000 gas intrinsic floor: floor(200,000,000 / 21,000) = 9,523. -/
def bvMtxFullTxCap : Nat := 9523

/-- Compatibility alias for existing active-loop call sites. New code should
    choose `bvMtxActiveTxCap` or `bvMtxFullTxCap` explicitly. -/
def bvMtxArenaTxCap : Nat := bvMtxActiveTxCap

/-- Cheap per-transaction result arenas use the full tx-capacity target. They
    are indexed only by tx number and are small enough to make static sizing
    preferable to preserving the old 1024 fixture cap. -/
def bvMtxU64ArenaBytes : Nat := bvMtxFullTxCap * 8
def bvMtxLogWindowBytes : Nat := bvMtxFullTxCap * 16

/-- The multi-tx skip-list stores `{sender_i, recipient_i}` for every
    transaction plus the shared coinbase account. It is sized to the full 200M
    tx-count target so the post-loop BAL comparators do not inherit the active
    execution-loop cap. -/
def bvMtxSystemSkipEntries : Nat := 6
def bvMtxSkipListEntries : Nat := bvMtxFullTxCap * 2 + 1 + bvMtxSystemSkipEntries
def bvMtxSkipListBytes : Nat := bvMtxSkipListEntries * 32
/-- Sender-balance aggregation shares the full sender table capacity so the
    B2 running-balance check does not inherit the active execution-loop cap. -/
def bvMtxSenderBalanceEntries : Nat := bvMtxFullTxCap
def bvMtxSenderBalanceTableBytes : Nat := bvMtxSenderBalanceEntries * 64
def bvMtxCreatedRecipientBytes : Nat := bvMtxFullTxCap * 32
/-- Sender-count aggregation is a post-loop, keyed-by-sender table. It is sized
    to the full tx-count target so the B1 final-nonce check does not inherit the
    active execution-loop cap. -/
def bvMtxSenderCountEntries : Nat := bvMtxFullTxCap
def bvMtxSenderCountTableBytes : Nat := bvMtxSenderCountEntries * 40
def bvMtxSenderCountSortBytes : Nat := bvMtxSenderCountEntries * 32
def bvMtxSenderCountSkipBytes : Nat := bvMtxSenderCountEntries * 64

/-- Cross-transaction committed-storage threading table. This is a unique
    `(recipient, slotKey)` capacity, not a transaction-count or raw-write
    capacity: each tx snapshots 128-byte storage-log entries so later tx preloads
    can see earlier committed values, while duplicate keys update in place.
    Overflow is conservative and tracked separately from tx arena overflow. -/
def bvMtxCommittedEntryBytes : Nat := 128
def bvMtxCommittedPageCapacity : Nat := 128
/-- Current single-page committed-storage capacity used by the existing helper ABI. -/
def bvMtxCommittedCapacity : Nat := bvMtxCommittedPageCapacity
def bvMtxCommittedBytes : Nat := bvMtxCommittedCapacity * bvMtxCommittedEntryBytes

/-- Behavior-neutral chunked committed-storage substrate for the follow-up
    helpers. Each page preserves the current 128-entry layout; the active total
    capacity is the number of unique `(recipient, slotKey)` entries across the
    currently wired pages. -/
def bvMtxCommittedChunkPages : Nat := 4
def bvMtxCommittedChunkCapacity : Nat := bvMtxCommittedChunkPages * bvMtxCommittedPageCapacity
def bvMtxCommittedChunkBytes : Nat := bvMtxCommittedChunkCapacity * bvMtxCommittedEntryBytes

/-- Execution-specs runs each EIP-7002/EIP-7251 system transaction with
    `SYSTEM_TRANSACTION_GAS = 30,000,000`. The stateless verdict derives both
    withdrawal and consolidation requests, so side capture must be sized for two
    such calls. -/
def bvSystemTransactionGas : Nat := 30000000
def bvSystemRequestCallCount : Nat := 2

def bvSystemStorageMinSstoreGas : Nat := 100

/-- **Runtime persistent storage exec-log capacity** — the hard, fail-closed cap
    on how many rows the SSTORE opcode handler can append to the exec-log at
    `0xa0630000..0xa0830000` (`Storage.lean:380-382`:
    `li x14,16384; bgeu x15,x14,.exit_outofgas`; mirrored on the preload seed at
    `Dispatch.lean:2246-2247`). The 16385th append triggers an exceptional exit,
    so `evm_env+448` (persistentLogLength) can never exceed this. Kept in sync
    with `Evm64.StorageAssertions.STORAGE_LOG_CAPACITY = 16384` (which carries the
    in-bounds proof). -/
def bvPersistentStorageLogCapacity : Nat := 16384

/-- **Row bound for the system-call SSTORE side capture (`bv_system_storage_log`),
    tightened for `evm-asm-4ch8f.73`.** `capture_system_storage_exec_rows`
    (`BlockVerdictSystemStorageCapture.lean`) copies rows out of the runtime
    persistent exec-log at `0xa0630000` over `[cursor, evm_env+448)`. Because that
    source is hard-capped at `bvPersistentStorageLogCapacity` (fail-closed at
    SSTORE time), and the two end-of-block system txs share the same non-reset log
    (the cursor only advances, `BlockVerdictStateRoot.lean:457/510/555`; the length
    is restored, not reset, at `:556`), their combined captured rows are
    `≤ bvPersistentStorageLogCapacity`. The modeled EIP-2935/4788 startup
    descriptors (`appendModeledSystemStorageTupleRows`) add only a fixed handful
    (3). So `2 * bvPersistentStorageLogCapacity` is a sound ~2× over-approximation
    of the true `≤ 16387` worst case.

    This REPLACES the former gas-derived `600,000` reservation
    (`2 * 30M / 100`), which was unreachable: the 100-gas figure ignored the
    16384-row fail-closed source cap. The old `76.8 MiB` reservation was UNIONED
    into `call_frame_arena`'s front, where per-tx dispatch frames at depth ≥ 221
    physically zeroed it before the post-dispatch BAL validators read it (the
    `.73` clobber). At `2 * 16384` rows (4 MiB) the syslog is small enough to live
    in its OWN standalone `.data` region, fully outside the frame arena — see
    `syslog_disjoint_from_frameArena`. -/
def bvSystemStorageLogCapacity : Nat := 2 * bvPersistentStorageLogCapacity

/-- Full committed-storage unique-key target for the 200M resource work.

    This is keyed by unique `(recipient, slotKey)`, not by transaction count or
    raw duplicate writes. The active block-verdict path uses
    `bvMtxCommittedChunkCapacity`; follow-up slices migrate the upsert/lookup
    substrate to this full target or to an equivalent streaming design.
    (Independent of `bvSystemStorageLogCapacity` since `.73`: that syslog arena is
    a per-block system-call side buffer bounded by the runtime exec-log source
    cap, whereas this is a whole-block cross-tx unique-key capacity target.) -/
def bvMtxCommittedFullKeyCap : Nat := 600000
def bvMtxCommittedFullBytes : Nat :=
  bvMtxCommittedFullKeyCap * bvMtxCommittedEntryBytes
def bvSystemStorageLogBytes : Nat := bvSystemStorageLogCapacity * 128
def bvSystemStorageTxindexBytes : Nat := bvSystemStorageLogCapacity * 8

/-- Receipt/log arena capacities are deliberately separated by resource type.
    Receipt records are per transaction and therefore use the full Amsterdam
    200M intrinsic-floor transaction count target; log/RLP byte arenas remain
    independent capacity slices tracked under `evm-asm-vv4hr.3`. -/
def bvReceiptRecordCapacity : Nat := bvMtxFullTxCap
def bvReceiptRecordBytes : Nat := 64
def bvReceiptRecordsBytes : Nat := bvReceiptRecordCapacity * bvReceiptRecordBytes

/-- Current EEST resource target for Amsterdam/Prague/Osaka stateless blocks. -/
def bvResourceBlockGasLimit : Nat := 200000000

/-- EVM LOG base gas. A zero-topic, zero-data LOG0 is the cheapest way to
    increase the number of execution-derived receipt log descriptors. -/
def bvBlockLogMinGas : Nat := 375

/-- EVM LOG data gas per byte. Topic/base gas can only reduce the number of
    data bytes that fit inside the same block gas target. -/
def bvBlockLogDataByteGas : Nat := 8

/-- Worst-case execution-derived log COUNT in a 200M block. Each LOG opcode
    costs at least `bvBlockLogMinGas` (the zero-topic, zero-data LOG0 base), so
    the block holds at most `gas_limit / 375 = 533,333` log records. -/
def bvBlockLogFullDescTarget : Nat :=
  bvResourceBlockGasLimit / bvBlockLogMinGas

/-- FIXED-STRIDE descriptor byte target (the verbatim 256 B copy that
    `block_log_window_snapshot` performs today, one slot per log). NOTE: this is
    the INFEASIBLE upper bound -- 533,333 * 256 = ~136.5 MiB of descriptors
    alone. Combined with `bvBlockLogFullMetaBytes` + `bvBlockLogFullDataBytes`
    the fixed-stride arena is ~162 MiB, which is 2.76x the measured ~58.7 MiB of
    `.data` headroom before `.sszscratch` (0xbf500000). Kept only to document why
    the verbatim-copy layout cannot reach the 200M target; the actual
    implementation target is `bvBlockLogPackedDescBytes` below. -/
def bvBlockLogFullDescBytes : Nat := bvBlockLogFullDescTarget * 256
def bvBlockLogFullMetaBytes : Nat := bvBlockLogFullDescTarget * 16

/-- Full copied-log-data byte target for the 200M resource work. It deliberately
    uses a simple upper bound (`gas_limit / LOGDATA_GAS`) so the implementation
    target covers every execution-specs-valid mix of LOG base/topic/data gas. -/
def bvBlockLogFullDataBytes : Nat :=
  bvResourceBlockGasLimit / bvBlockLogDataByteGas

/-- vv4hr.3.4.1 capacity DERIVATION -- the FEASIBLE 200M log-arena target.

    The fixed-256 B stride (`bvBlockLogFullDescBytes`) over-allocates because it
    reserves room for four 32 B topics in EVERY descriptor even though most logs
    carry none. The gas schedule charges 375 per log base AND 375 per topic, so

        #logs + #topics  <=  gas_limit / 375  =  533,333   (one "gas unit" each)

    bounds the SUM of records and topics. A packed descriptor needs at most one
    gas unit's worth of bytes per unit: a log header (address 20 + data
    offset/len 8 + topic_count/flags) fits in 32 B, and each topic is 32 B. So a
    packed descriptor arena charged at 32 B per gas unit is a sound upper bound
    over every LOG0..LOG4 / data mix:

        packed desc <=  32 * (gas_limit / 375)  =  ~16.3 MiB

    With the count-scaled meta table (16 B/log -> ~8.1 MiB) and the gas/8 data
    bound (~23.8 MiB), the packed arena totals ~48.3 MiB, which DOES fit the
    ~58.7 MiB `.data` headroom (10+ MiB margin).

    Implementation (vv4hr.3.4.2): `block_log_window_snapshot` must REPACK on copy
    -- emit a variable-length packed record per log instead of the current
    verbatim 256 B `slli ..,8` memcpy -- and the descriptor readers
    (`block_receipt_logs_materialize`, `materialize_log_records`,
    `parse_deposit_requests`) must walk the packed stride. The runtime
    dispatcher's `evm_event_logs` 256 B source format is unchanged. Closing this
    keeps `bv_block_log_overflow` unreachable under 200M. If it is reached anyway,
    BlockVerdictReceiptsTail now fails visibly instead of accepting through a
    capacity skip, so class-D receipt enforcement and class-E deposit derivation do
    not normalize incomplete log materialization into success. -/
def bvBlockLogPackedUnitBytes : Nat := 32
def bvBlockLogPackedDescBytes : Nat :=
  bvBlockLogPackedUnitBytes * bvBlockLogFullDescTarget

-- vv4hr.3.4.2 PACK (2026-06-20): the active block-log DESCRIPTOR arena is the
-- PACKED layout (32 B per gas unit), not the fixed 256 B/log stride. The gas
-- schedule charges 375 per log base AND 375 per topic, so `#logs + #topics <=
-- gas/375 = 533,333`; a packed descriptor is a 32 B header (topic_count @+0,
-- canonical-BE address 20 B @+8) plus 32 B per ACTUAL topic, so a 32 B/gas-unit
-- arena (`bvBlockLogPackedDescBytes` = 32*533,333 = ~16.3 MiB) is a sound upper
-- bound over every LOG0..LOG4/data mix -- vs ~136.5 MiB for the old 256 B stride.
-- The descriptor records are VARIABLE length, so `block_log_window_snapshot`
-- repacks on copy and records each log's packed byte-offset in
-- `bv_block_log_meta[idx].desc_off` (+16; meta widened 16 -> 24 B). The lone
-- random-access reader (`block_receipt_logs_materialize`) jumps via that desc_off;
-- the sequential readers (`materialize_log_records`, `log_records_encode_rlp`)
-- walk `reclen = 32 + 32*topic_count`. The runtime dispatcher's `evm_event_logs`
-- 256 B SOURCE format is UNCHANGED. The data byte arena (gas/8 = 25,000,000) and
-- the count cap (533,333) are unchanged, so `bv_block_log_overflow` stays
-- UNREACHABLE under 200M -- preserving the #9043 class-D (receipts) / class-E
-- (deposit-derivation) no-skip property -- while reclaiming ~113 MiB of the
-- .data -> .sszscratch link-time window.
def bvBlockLogDescCapacity : Nat := bvBlockLogFullDescTarget
def bvBlockLogDescBytes : Nat := bvBlockLogPackedDescBytes
def bvBlockLogMetaBytes : Nat := bvBlockLogDescCapacity * 24
def bvBlockLogDataBytes : Nat := bvBlockLogFullDataBytes
def bvLogsRlpArenaBytes : Nat := 1048576
def bvRecordBloomBytes : Nat := 256
def bvRecordBloomsBytes : Nat := bvReceiptRecordCapacity * bvRecordBloomBytes
def bvRecordLogsDescBytes : Nat := bvReceiptRecordCapacity * 32
def bvReceiptsRlpBytes : Nat := 1048576
def bvReceiptEncodePayloadBytes : Nat := 1048576
def bvReceiptListPayloadBytes : Nat := 1048576
def bvReceiptConsensusDescCapacity : Nat := 128
def bvReceiptConsensusDescBytes : Nat := bvReceiptConsensusDescCapacity * 16

/-- Amsterdam SSZ execution-request capacity:
    deposits 8192*192, withdrawals 16*76, consolidations 2*116, plus the
    3-entry offset table used by the guest's flattened request-section body. -/
def bvMaxDepositRequestBodyBytes : Nat := 8192 * 192
def bvMaxExecutionRequestSectionBytes : Nat :=
  12 + bvMaxDepositRequestBodyBytes + 16 * 76 + 2 * 116

/-- One canonicalized EIP-6110 deposit log record has the common 80-byte
    log-record header plus the 576-byte DepositEvent ABI payload. -/
def bvDepositLogRecordBytes : Nat := 80 + 576

/-- Protocol target for execution-derived EIP-6110 deposit log-record staging
    before `parse_deposit_requests`. Upstream block-log descriptor/data capture
    has independent capacity work under `evm-asm-vv4hr.3`. -/
def bvMaxDepositLogRecordBytes : Nat := 8192 * bvDepositLogRecordBytes

/-- `c1_staging` (system-call payload buffer) byte size: must hold
    round8(predeploy codelen) + preload_count*64 + m29_count*32 + 584.
    Predeploy code comes from the witness and is NOT EIP-170-bounded, but the
    whole witness is <= `bsrMaxWitnessBytes`; preloads <= `bsrAccountSlotCap`;
    m29 <= 256 hashes (8 KiB) + 584 header fit in the 16 KiB slack. The
    `stage_system_call_payload` size guard uses this same constant (it bails
    soundly on anything larger instead of corrupting `.data`). -/
def c1StagingBytes : Nat := bsrMaxWitnessBytes + bsrAccountSlotCap * 64 + 16384
def bsrAccountRecordBytes : Nat := 24
def bsrPathBytes : Nat := 64
def bsrEncodedAccountBytes : Nat := 256
def bsrSystemAccountBytes : Nat := 128
def bsrStateChangeBytes : Nat := 40
def baapStorageDescBytes : Nat := 40

/-- Current static multi-transaction fixture arena capacity. The verdict guest's
    active per-tx u64/log-window buffers are still sized to this bound while the
    full-capacity migration lands in smaller slices. -/
def bmvFixtureTxCapacity : Nat := 16

def bmvFullTxCapacity : Nat := bvMtxFullTxCap

def bmvU64PerTxArenaBytes (txCapacity : Nat) : Nat := txCapacity * 8
def bmvLogWindowPerTxArenaBytes (txCapacity : Nat) : Nat := txCapacity * 16

def bmvFixtureU64PerTxArenaBytes : Nat :=
  bmvU64PerTxArenaBytes bmvFixtureTxCapacity

def bmvFixtureLogWindowArenaBytes : Nat :=
  bmvLogWindowPerTxArenaBytes bmvFixtureTxCapacity

def bmvFullU64PerTxArenaBytes : Nat :=
  bmvU64PerTxArenaBytes bmvFullTxCapacity

def bmvFullLogWindowArenaBytes : Nat :=
  bmvLogWindowPerTxArenaBytes bmvFullTxCapacity

#guard bvMtxSenderBalanceEntries = bvMtxFullTxCap
#guard bvMtxSenderBalanceTableBytes = bvMtxFullTxCap * 64
#guard bvMtxCreatedRecipientBytes = 304736
#guard bvMtxSkipListEntries = 19053
#guard bvMtxSkipListBytes = 609696
#guard bvMtxSenderCountEntries = 9523
#guard bvMtxSenderCountTableBytes = 380920
#guard bvMtxSenderCountSortBytes = 304736
#guard bvMtxSenderCountSkipBytes = 609472
#guard bvMtxActiveTxCap = 1024
#guard bvSystemTransactionGas = 30000000
#guard bvSystemRequestCallCount = 2
#guard bvSystemStorageMinSstoreGas = 100
#guard bvPersistentStorageLogCapacity = 16384
#guard bvSystemStorageLogCapacity = 32768
#guard bvSystemStorageLogBytes = 4194304
#guard bvSystemStorageTxindexBytes = 262144
#guard bvMtxFullTxCap = 9523
#guard bvMtxArenaTxCap = bvMtxActiveTxCap
#guard bvMtxU64ArenaBytes = 76184
#guard bvMtxLogWindowBytes = 152368
#guard bmvFixtureTxCapacity = 16
#guard bmvFullTxCapacity = 9523
#guard bmvFixtureU64PerTxArenaBytes = 128
#guard bmvFixtureLogWindowArenaBytes = 256
#guard bmvFullU64PerTxArenaBytes = 76184
#guard bmvFullLogWindowArenaBytes = 152368
#guard bvMtxCommittedBytes = 16384
#guard bvMtxCommittedChunkCapacity = 512
#guard bvMtxCommittedChunkBytes = 65536
#guard bvMtxCommittedFullKeyCap = 600000
#guard bvMtxCommittedFullBytes = 76800000
#guard bvReceiptRecordsBytes = 609472
#guard bvResourceBlockGasLimit = 200000000
#guard bsrStateRootBlockGasLimit = 200000000
#guard bsrBalGasCost = 2000
#guard bsrMaxBalItems = bsrStateRootBlockGasLimit / bsrBalGasCost
#guard bsrMaxBalItems = 100000
#guard bsrMaxStateChanges = 100018
#guard bsrMptSortRangeStackCapacity = 1024
#guard bsrMptBuilderFrameCapacity = 65
#guard bvBlockLogMinGas = 375
#guard bvBlockLogDataByteGas = 8
#guard bvBlockLogFullDescTarget = 533333
#guard bvBlockLogFullDescBytes = 136533248
#guard bvBlockLogFullMetaBytes = 8533328
#guard bvBlockLogFullDataBytes = 25000000
-- vv4hr.3.4.2 PACK: active descriptor arena = packed 32 B/gas-unit (~16.3 MiB)
-- and the meta table widened to 24 B/log (adds the packed desc byte-offset).
#guard bvBlockLogPackedDescBytes = 17066656
#guard bvBlockLogDescBytes = 17066656
#guard bvBlockLogMetaBytes = 12799992
#guard bvBlockLogDataBytes = 25000000
#guard bvLogsRlpArenaBytes = 1048576
#guard bvRecordBloomsBytes = 2437888
#guard bvRecordLogsDescBytes = 304736
#guard bvReceiptsRlpBytes = 1048576
#guard bvReceiptEncodePayloadBytes = 1048576
#guard bvReceiptListPayloadBytes = 1048576
#guard bvReceiptConsensusDescBytes = 2048
#guard bvMaxDepositRequestBodyBytes = 1572864
#guard bvMaxExecutionRequestSectionBytes = 1574324
#guard bvDepositLogRecordBytes = 656
#guard bvMaxDepositLogRecordBytes = 5373952

end EvmAsm.Codegen
