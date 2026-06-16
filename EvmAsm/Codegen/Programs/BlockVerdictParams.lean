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

def bsrBalGasCost : Nat := 2000
/-- Static BAL/state replay arena capacity, sized for the Amsterdam 200M
    block-gas target: `bal_items <= block_gas_limit / 2000` = 100,000 items at
    200,000,000 gas. (The former 500,000 value was the 1G worst case, which is
    out of scope — it cost ~349 MB of the fixed 512 MiB ziskemu RAM window.)
    High declared block gas is not itself a layout error: the guest first
    applies Amsterdam's gas-derived BAL rule, then checks actual decoded item
    counts against these arenas; blocks whose actual counts exceed the
    capacities take the conservative bsr_fail path. -/
def bsrMaxBalItems : Nat := 100000
def bsrModeledSystemChanges : Nat := 2
def bsrMaxWithdrawalChanges : Nat := 16
def bsrMaxAuxChanges : Nat := bsrModeledSystemChanges + bsrMaxWithdrawalChanges
def bsrMaxStateChanges : Nat :=
  bsrMaxBalItems + bsrModeledSystemChanges + bsrMaxWithdrawalChanges
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
def bvMtxSkipListEntries : Nat := bvMtxFullTxCap * 2 + 1
def bvMtxSkipListBytes : Nat := bvMtxSkipListEntries * 32
/-- Sender-balance aggregation shares the full sender table capacity so the
    B2 running-balance check does not inherit the active execution-loop cap. -/
def bvMtxSenderBalanceEntries : Nat := bvMtxFullTxCap
def bvMtxSenderBalanceTableBytes : Nat := bvMtxSenderBalanceEntries * 64
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
    helpers. Each page preserves the current 128-entry layout; the total capacity
    is the number of unique `(recipient, slotKey)` entries across all pages. -/
def bvMtxCommittedChunkPages : Nat := 4
def bvMtxCommittedChunkCapacity : Nat := bvMtxCommittedChunkPages * bvMtxCommittedPageCapacity
def bvMtxCommittedChunkBytes : Nat := bvMtxCommittedChunkCapacity * bvMtxCommittedEntryBytes

/-- Persistent storage exec-log row capacity:
    `(0xa0830000 - 0xa0630000) / 128 = 16384`.  The system-tuple side arena
    mirrors this maximum because it captures rows that temporarily append to the
    same runtime storage log before the verdict restores the user-log count. -/
def bvSystemStorageLogCapacity : Nat := 16384
def bvSystemStorageLogBytes : Nat := bvSystemStorageLogCapacity * 128
def bvSystemStorageTxindexBytes : Nat := bvSystemStorageLogCapacity * 8

/-- Receipt/log arena capacities are deliberately separated by resource type.
    Receipt records are per transaction and therefore use the full Amsterdam
    200M intrinsic-floor transaction count target; log/RLP byte arenas remain
    independent capacity slices tracked under `evm-asm-vv4hr.3`. -/
def bvReceiptRecordCapacity : Nat := bvMtxFullTxCap
def bvReceiptRecordBytes : Nat := 64
def bvReceiptRecordsBytes : Nat := bvReceiptRecordCapacity * bvReceiptRecordBytes
def bvBlockLogDescCapacity : Nat := 128
def bvBlockLogDescBytes : Nat := bvBlockLogDescCapacity * 256
def bvBlockLogMetaBytes : Nat := bvBlockLogDescCapacity * 16
def bvBlockLogDataBytes : Nat := 65536
def bvLogsRlpArenaBytes : Nat := 65536
def bvRecordBloomBytes : Nat := 256
def bvRecordBloomsBytes : Nat := bvReceiptRecordCapacity * bvRecordBloomBytes
def bvRecordLogsDescBytes : Nat := bvReceiptRecordCapacity * 32
def bvReceiptsRlpBytes : Nat := 65536
def bvReceiptEncodePayloadBytes : Nat := 16384
def bvReceiptListPayloadBytes : Nat := 32768
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
#guard bvMtxSkipListEntries = 19047
#guard bvMtxSkipListBytes = 609504
#guard bvMtxSenderCountEntries = 9523
#guard bvMtxSenderCountTableBytes = 380920
#guard bvMtxSenderCountSortBytes = 304736
#guard bvMtxSenderCountSkipBytes = 609472
#guard bvMtxActiveTxCap = 1024
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
#guard bvReceiptRecordsBytes = 609472
#guard bvBlockLogDescBytes = 32768
#guard bvBlockLogMetaBytes = 2048
#guard bvBlockLogDataBytes = 65536
#guard bvLogsRlpArenaBytes = 65536
#guard bvRecordBloomsBytes = 2437888
#guard bvRecordLogsDescBytes = 304736
#guard bvReceiptsRlpBytes = 65536
#guard bvReceiptEncodePayloadBytes = 16384
#guard bvReceiptListPayloadBytes = 32768
#guard bvReceiptConsensusDescBytes = 2048
#guard bvMaxDepositRequestBodyBytes = 1572864
#guard bvMaxExecutionRequestSectionBytes = 1574324
#guard bvDepositLogRecordBytes = 656
#guard bvMaxDepositLogRecordBytes = 5373952

end EvmAsm.Codegen
