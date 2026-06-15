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

/-- Multi-transaction verdict arena capacity. The cached `zkevm@v0.4.0`
    stateless fixtures include blocks with more than the old 16-entry arena
    cap, topping out at 1021 transactions. Use 1024 so the tx-count gate and
    every fixed per-tx arena have one shared current-fixture-sized bound.
    Full Amsterdam worst-case capacity (~9523 txs at 200M / 21000) still needs
    the separate streaming/dynamic design tracked by bmvmx.5.5.7. -/
def bvMtxArenaTxCap : Nat := 1024
def bvMtxU64ArenaBytes : Nat := bvMtxArenaTxCap * 8
def bvMtxLogWindowBytes : Nat := bvMtxArenaTxCap * 16
def bvMtxSkipListEntries : Nat := bvMtxArenaTxCap * 2 + 1
def bvMtxSkipListBytes : Nat := bvMtxSkipListEntries * 32
def bvMtxSenderCountEntries : Nat := bvMtxArenaTxCap
def bvMtxSenderCountTableBytes : Nat := bvMtxSenderCountEntries * 40
def bvMtxSenderCountSortBytes : Nat := bvMtxSenderCountEntries * 32

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

/-- Full Amsterdam transaction capacity target from the 200M block-gas limit and
    the 21,000 gas intrinsic floor: floor(200,000,000 / 21,000) = 9,523. -/
def bmvFullTxCapacity : Nat := 9523

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

#guard bvMtxSenderCountEntries = 1024
#guard bvMtxSenderCountTableBytes = 40960
#guard bvMtxSenderCountSortBytes = 32768
#guard bmvFixtureTxCapacity = 16
#guard bmvFullTxCapacity = 9523
#guard bmvFixtureU64PerTxArenaBytes = 128
#guard bmvFixtureLogWindowArenaBytes = 256
#guard bmvFullU64PerTxArenaBytes = 76184
#guard bmvFullLogWindowArenaBytes = 152368

end EvmAsm.Codegen
