/-
  EvmAsm.Codegen.RegionMap

  Authoritative, kernel-checked memory-region map for the stateless guest
  (bead `evm-asm-4ch8f.6`, mechanical half).

  This is the single source of truth reconciling the two address-space schemes
  that previously had no shared, machine-checked layout statement:

  * **Scheme A** — the working-RAM anchors in `EvmAsm/Stateless/MemoryLayout.lean`
    (`0xa0020000..0xa3000000`), the layout the *verified stateless port* under
    `EvmAsm/Stateless/` addresses. Historically these anchors had *no* fit or
    disjointness lemma and their sizes were only implicit in the gaps between
    successive anchors. Here every anchor gets an explicit extent (the gap to the
    next anchor) and a per-region evidence note.
  * **Scheme B** — the linked `.data` at `0xa3000000` (`-Tdata=`), the
    dedicated bounded `.committed_storage` NOBITS map at `0xa2000000`, the
    zero-initialized `.bss` at `0xa4000000`, plus `.text`
    (`-Ttext=0x80000000`) and the `.sszscratch` NOBITS region
    (`--section-start=.sszscratch=0xbf980000`). Sizes here are the ELF ground
    truth (`readelf -S`), cross-checked by `scripts/check-region-map.sh`.

  **Location rationale.** This module imports both `CallFrameLayout`
  (Codegen layer) and `MemoryLayout` (verified-core layer, under `Stateless/`).
  Only the Codegen layer may import both (the layering guard forbids
  core → Codegen), so the region map lives here rather than under `Stateless/`.

  **Aliasing (soundness-critical, deferred proof).** The guest has exactly one
  intentional physical overlap: `call_frame_arena` (~228 MiB, EVM call-frame
  overlay) coalesces six execution-dead Phase-H arenas into its front
  (`basr_values`, `basr_accounts`, `baap_storage_desc`,
  `baap_storage_paths`, `baap_storage_delete_paths`, `baap_storage_values`).
  (`bv_system_storage_log` was un-unioned in `4ch8f.73` — it is read
  post-dispatch, so it now lives standalone, `syslog_disjoint_from_frameArena`.)
  This file *documents* those overlaps precisely (`aliasedPairs` + the per-pair
  `_overlap` theorems) and proves the six coalesced children are mutually
  disjoint. It does **not** prove they are safe to share — the verified
  phase-ownership / separation-logic model is bead `.6`'s other (deferred) half.
  See `docs/4ch8f-region-map.md` §"Overlap inventory" and
  `docs/call-frame-memory-layout.md` §5.

  All statements use plain `Nat` (no `Word`/`BitVec`) so the pairwise and
  fit checks are closed by the kernel's GMP-backed `decide`. No
  `native_decide`/`bv_decide`. The `_matches_*` theorems pin each literal here
  to the real layout constant it mirrors, so a drift in either place is a
  kernel error.
-/

import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.Emit
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Codegen.RegionMap

open EvmAsm.Rv64 (RAM_MEM_START RAM_MEM_END INPUT_MEM_START INPUT_MEM_END)

/-! ## Region model -/

/-- Access mode / section kind of a guest region. -/
inductive RegionMode
  /-- Executable code (`.text`, `R E`). -/
  | rx
  /-- Read-write data materialized in the ELF (`.data`, working RAM). -/
  | rw
  /-- Read-only host-supplied input. -/
  | ro
  /-- Zero-initialized, not stored in the ELF file (`.sszscratch`, NOBITS). -/
  | nobits
  deriving DecidableEq, Repr

/-- Which top-level address-space zone a region is expected to live inside.
    Each zone is a half-open `[lo, hi)` byte range recognised (for the RAM /
    INPUT zones) by the verified `isValidMemAddr` predicate. -/
inductive RegionZone
  /-- Host input window `[INPUT_MEM_START, INPUT_MEM_END)`. -/
  | input
  /-- `.text`/`.rodata` window `[0x80000000, 0xa0000000)`. -/
  | text
  /-- Verified RAM window `[RAM_MEM_START, RAM_MEM_END)` = `0xa0000000..0xc0000000`. -/
  | ram
  deriving DecidableEq, Repr

def RegionZone.lo : RegionZone → Nat
  | .input  => INPUT_MEM_START
  | .text   => 0x80000000
  | .ram    => RAM_MEM_START

def RegionZone.hi : RegionZone → Nat
  | .input  => INPUT_MEM_END
  | .text   => 0xa0000000
  | .ram    => RAM_MEM_END

/-- One named guest region: `[base, base+size)`, its mode, the zone it must fit,
    and a short scheme/evidence tag (documentation, not used by the proofs). -/
structure GuestRegion where
  name     : String
  base     : Nat
  size     : Nat
  mode     : RegionMode
  zone     : RegionZone
  evidence : String
  deriving Repr

/-- Byte just past the region. -/
def GuestRegion.eend (r : GuestRegion) : Nat := r.base + r.size

/-- `a` and `b` occupy disjoint byte ranges. -/
def GuestRegion.disjoint (a b : GuestRegion) : Bool :=
  decide (a.base + a.size ≤ b.base) || decide (b.base + b.size ≤ a.base)

/-- `r` lies fully inside its declared zone. -/
def GuestRegion.fitsZone (r : GuestRegion) : Bool :=
  decide (r.zone.lo ≤ r.base) && decide (r.base + r.size ≤ r.zone.hi)

/-- `inner ⊆ outer` (inner's whole range sits within outer's). -/
def GuestRegion.subrange (inner outer : GuestRegion) : Bool :=
  decide (outer.base ≤ inner.base) && decide (inner.base + inner.size ≤ outer.base + outer.size)

/-! ## Booleans over region lists (kept `decide`-friendly). -/

/-- Every region fits its zone. -/
def allFitZones (rs : List GuestRegion) : Bool :=
  rs.all GuestRegion.fitsZone

/-- Every unordered pair of distinct list positions is disjoint. -/
def allPairwiseDisjoint : List GuestRegion → Bool
  | []      => true
  | r :: rs => rs.all (fun s => r.disjoint s) && allPairwiseDisjoint rs

/-! ## Scheme-A working-RAM anchors — ASPIRATIONAL port contract (`MemoryLayout.lean`).

    These are the layout the in-progress verified port under `EvmAsm/Stateless/`
    *intends* to use; they do NOT describe the currently-emitted `stateless_guest`
    (see `guestRegionMap`, the emitted-reality map, and the FINDING in the docs:
    only `state_tracker_area` is referenced today). They are kept here as a
    separate list because — as of this build — they are NOT disjoint from what the
    guest actually emits: the RV64 call stack (`guestStackRegion`, top pinned by
    `_start`'s `li sp, 0xa0050000`) grows down *through* `execution_witness_area`
    (see `guestStack_overlaps_executionWitnessArea`). Reflowing the scheme-A
    anchors clear of the stack/witness area before the port goes live is filed as
    a P1 divergence bead; until then the aspirational list must not be conflated
    with the emitted-reality map.

    Sizes are the gap to the next anchor (the reserved slab). The evidence note
    records the *measured* live extent where the emitted guest actually
    references the anchor, which may be smaller than the reserved slab. -/

/-- The working-RAM anchor sub-regions, `0xa0020000..0xa1fa0000` (the upper six are
    the GH #10619 read containers: three block-level, three per-transaction). Aspirational —
    see the section note; `schemeAAnchors_pairwise_disjoint` proves they are
    internally consistent, but they are NOT part of `guestRegionMap`. -/
def schemeAAnchors : List GuestRegion :=
  [ { name := "ssz_input_decoded",      base := 0xa0020000, size := 0x10000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout SSZ_INPUT_DECODED; 64 KiB slab (verified-port scheme A)" },
    { name := "execution_witness_area", base := 0xa0030000, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout EXECUTION_WITNESS_AREA; 1 MiB slab" },
    { name := "node_db_buckets",        base := 0xa0130000, size := 0x400000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout NODE_DB_BUCKETS; 4 MiB slab" },
    { name := "code_db_buckets",        base := 0xa0530000, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout CODE_DB_BUCKETS; 1 MiB slab" },
    { name := "state_tracker_area",     base := 0xa0630000, size := 0x400000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout STATE_TRACKER_AREA; 4 MiB slab. LIVE in emitted guest: "
        ++ "storage-log base 0xa0630000..0xa0830000 (2 MiB, 16384x128 rows) — the ONLY "
        ++ "scheme-A anchor the current stateless_guest references (see FINDING in docs)" },
    { name := "evm_frame_stack",        base := 0xa0a30000, size := 0x40000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout EVM_FRAME_STACK; 256 KiB slab" },
    { name := "evm_value_stack",        base := 0xa0a70000, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout EVM_VALUE_STACK; 1 MiB slab" },
    { name := "evm_memory_area",        base := 0xa0b70000, size := 0x1000000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout EVM_MEMORY_AREA; 16 MiB slab" },
    { name := "keccak_scratch",         base := 0xa1b70000, size := 0x10000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout KECCAK_SCRATCH; 64 KiB slab" },
    { name := "ecrecover_scratch",      base := 0xa1b80000, size := 0x10000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout ECRECOVER_SCRATCH; 64 KiB slab" },
    { name := "sha256_scratch",         base := 0xa1b90000, size := 0x10000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout SHA256_SCRATCH; 64 KiB slab" },
    -- GH #10619: the spec's THREE read sets, each with the BLOCK-long lifetime
    -- `restore_tx_state` gives them by restoring only the write structures
    -- (state_tracker.py:809-826; the TransactionState docstring at :90-93 calls
    -- them "shared references that survive rollback").  Separate regions rather
    -- than one merged set because the spec has three and looking-the-same is the
    -- point; separate from `state_tracker_area` because rollback truncates that
    -- one and must not reach these.
    { name := "storage_reads_area",     base := 0xa1ba0000, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout STORAGE_READS_AREA; 1 MiB = 16384x64 (addrHash++slotKey), "
        ++ "matching the write log's 16384 rows so reads cannot overflow first" },
    { name := "account_reads_area",     base := 0xa1ca0000, size := 0x80000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout ACCOUNT_READS_AREA; 512 KiB = 16384x32 (addrHash)" },
    { name := "code_reads_area",        base := 0xa1d20000, size := 0x80000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout CODE_READS_AREA; 512 KiB = 8192x64 (addrHash++codeHash); "
        ++ "consumer is the execution witness (stateless_host_exec_witness.py:182), NOT the BAL" },
    -- GH #10619 review gate 3: the TRANSACTION level of the same three sets.  The
    -- spec has two levels (TransactionState's fresh sets, merged up at
    -- state_tracker.py:858-861 and CLEARED at :879-881), and a block-level-only
    -- mirror has nowhere to express fork.py:745-752 -- a throwaway TransactionState
    -- whose reads are deliberately NOT promoted.
    { name := "tx_storage_reads_area",  base := 0xa1da0000, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_STORAGE_READS_AREA; per-tx storage_reads, merged up and cleared" },
    { name := "tx_account_reads_area",  base := 0xa1ea0000, size := 0x80000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_ACCOUNT_READS_AREA; per-tx account_reads" },
    { name := "tx_code_reads_area",     base := 0xa1f20000, size := 0x80000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_CODE_READS_AREA; per-tx code_reads" },
    -- r59nm S2: the WRITE side of the same two levels.  BlockState.storage_writes
    -- (state_tracker.py:74) and TransactionState.storage_writes (:101).  ONE map per
    -- level, not one per source: the spec has no system-specific write container --
    -- process_unchecked_system_transaction (fork.py:782) builds an ordinary
    -- TransactionState and incorporates at :858, regular txs at :1204, withdrawals
    -- at :1226.  These replace bv_system_storage_log and bv_user_storage_log, whose
    -- two-arena split mirrors nothing.
    { name := "storage_writes_area",    base := 0xa1fa0000, size := 0x200000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout STORAGE_WRITES_AREA; 2 MiB = 16384x128 "
        ++ "(addrHash++slotKey++value, 96 B used of the shared bvStorageLogRowBytes stride); "
        ++ "block level, filled only by write_sets_incorporate_tx" },
    { name := "tx_storage_writes_area", base := 0xa21a0000, size := 0x200000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_STORAGE_WRITES_AREA; per-tx storage_writes, "
        ++ "target of storage_write_record (mirrors set_storage, state_tracker.py:489)" },
    -- r59nm S5a: undo journal standing in for take_snapshot's dict copy
    -- (state_tracker.py:800-806) under the no-dynamic-allocation constraint --
    -- a per-frame copy would cost capacity x call depth.  Bounded by the SSTORE
    -- handler's own 16384-row cap, so it needs no overflow path.
    { name := "storage_writes_undo_area", base := 0xa23a0000, size := 0x500000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout STORAGE_WRITES_UNDO_AREA; 5 MiB = 32768x160 "
        ++ "(entryIndex, wasAbsent, prevValue|fullRow); reverse-replayed by write_sets_restore_frame; "
        ++ "160 B stride journals full 128 B row for destroy_storage wasAbsent=2" },
    -- #10695/#10699: the NONSTORAGE half of the same two levels -- BlockState
    -- .account_writes (state_tracker.py:75) and TransactionState.account_writes
    -- (:102).  Same shape as the storage trio above and for the same reasons, so the
    -- entries mirror them rather than inventing a second convention.
    --
    -- NOTE THE ROW-COUNT ASYMMETRY, which is deliberate (#10719): the BLOCK map is
    -- 20480 rows while the TX map is 16384.  The two levels are bounded by different
    -- things -- the block map by the distinct-account bound across a whole block
    -- (19047), the tx map by what one transaction can touch -- so sizing them
    -- together would either waste 2.5 MiB or cap the block level too low.
    -- Bases shifted +0x180000 when storage undo grew 64->160 B/entry (#10645 review).
    { name := "account_writes_area",    base := 0xa28a0000, size := 0x280000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout ACCOUNT_WRITES_AREA; 2.5 MiB = 20480x128 "
        ++ "(addr++nonce++present++balance++codeHash, 128 B stride); block level, "
        ++ "filled only by account_writes_incorporate_tx; 20480 covers the 19047 "
        ++ "distinct block-account bound" },
    { name := "tx_account_writes_area", base := 0xa2b20000, size := 0x200000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_ACCOUNT_WRITES_AREA; 2 MiB = 16384x128; per-tx "
        ++ "account_writes, target of account_write_record (mirrors the spec's "
        ++ "nonstorage setters, state_tracker.py:102)" },
    -- Same rationale as storage_writes_undo_area: the spec rolls a frame back by
    -- copying the dict (state_tracker.py:800-806), unaffordable at capacity x call
    -- depth, so the bounded equivalent is a reverse-replayed journal.
    { name := "account_writes_undo_area", base := 0xa2d20000, size := 0x200000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout ACCOUNT_WRITES_UNDO_AREA; 2 MiB = 16384x128 "
        ++ "(entryIndex, wasAbsent, prevNonce, prevPresent, prevBalance, prevCodeHash); "
        ++ "reverse-replayed by account_writes_restore_frame" } ]

/-! ## Section / I/O extents (ELF ground truth, `readelf -S`).

    `.text` and `.data` sizes are LINK-LAYOUT-DEPENDENT (they move whenever any
    function or data object changes size); `scripts/check-region-map.sh`
    re-derives them from the linked ELF on every CI run. INPUT/OUTPUT bases and
    the section bases are STABLE (pinned by the codegen constants and the
    `-Ttext=`/`-Tdata=`/`--section-start=` linker flags). -/

/-- ELF-measured `.text` size for the `stateless_guest` unit
    (`readelf -S`, `0x59318`). Link-layout-dependent; the drift guard re-derives it.
    Shrank by 4 B when the BLOBHASH handler's two early `ret`s merged into the
    shared tail (verified `evm_blobhash` body swap). Grew by `0x90` when exact
    EIP-8037 gas checking began deriving the regular-gas dimension in-guest.
    Shrunk by `0x3c` when child-error state-gas spill stopped being credited
    back to regular gas. Grew by `0x174` when the EIP-4788 fast path learned
    same-slot stale timestamp reverts. Grew again after EIP-7702 child calls
    began preferring same-block delegation markers over stale pre-state markers.
    Grew again when EIP-7702 dispatch began allowing same-block marker precedence
    for pointer-to-pointer code. Grew again when multi-tx direct deposits began
    being derived for EIP-6110 negative system requests. Shrank net
    `0x7b0` after CREATE2 selfdestruct-collision handling simplified
    `ChildFrameHandlers` dispatch. Grew by `0x58` when
    `account_extract_nonce`/`account_extract_balance` moved to the RlpWalk
    cursor helpers (bead evm-asm-22pwv.4). Grew by `0xc` when the
    precompile fast path began returning successful value-call stipends while
    emitting every EIP-7708 transfer log. Grew by `0x20` when both runtime
    payload staging paths began reversing PREVRANDAO into EVM word order. Grew
    by `0x64` when same-transaction CREATE code became available to delegated
    calls before EIP-6780 deletion is finalized. Shrank by `0x4` when same-block
    delegation code was rebased directly from the caller's staged codes base.
    Grew by `0x848` after the cross-transaction authorization-nonce validation
    landed (bead evm-asm-eip7702-cross-tx). Shrank by `0xc` when RETURNDATACOPY
    dropped its 256-byte cap guard (evm-asm-pwqhw). Grew further after EIP-8037
    prefix admission enforcement, parallel EEST worker result-file isolation,
    and the self-funded EIP-7702 authorization refund fix landed. Grew by
    `0x30` when EIP-2780 direct-authorization gas context started being
    preserved. Grew by `0x1cc` when depth-1+ RETURN/REVERT windows gained
    sparse materialization (`sparse_window_read`, evm-asm-0w05f.13), and by
    `0x3c8` more for the nested-caller OUT-window write-back
    (`sparse_window_write` + tail wiring, 0w05f.13 surface 2), by `0x7c`
    for the epoch-tag packing in the four sparse scans (evm-asm-m8pdu), and by
    `0x20` when RETURN/REVERT window routing adopted the pool-relative limit
    (evm-asm-ck36u), and by `0x4` for the settle-reverted-dispatcher-state-gas
    fix (`fix/dispatcher-revert-state-gas`). Regenerated after the bounded
    storage-root builder replaced the legacy one-slot mutation path. Grew by
    `0xa58` for the gas-sized bounded indexed transaction/receipt root
    builder. Grew by `0x128` for the batch-merge landing the chain-validate
    Fn.Spec siblings, misaligned-load fixes, and the SSZ envelope-cap check.
    Grew by `0x4` for the batch-merge landing the divmod cleanup and bounded
    extension direct-result ABI repair. Grew by `0x60` for the batch-merge
    landing the BAL delegation-codes-base fix and further divmod cleanup.
    Grew by `0x40` for the recipient-ownership filter in
    `bv_mtx_committed_chunked_snapshot_upsert` (`fix/committed-snapshot-recipient-filter`).
    Grew further to `0x5c688` for the combined batch-merge landing that fix
    together with the MPT bounded leaf-group delete-collapse fix
    (`fix/bounded-leaf-group-delete-collapse`), measured via a fresh
    `readelf -SW` on the relinked ELF after both land together. Grew again
    to `0x5c6b4` after merging main forward past #10394/#10395 (7702 auth
    state gas gate + EIP-8037 auth-retention 0-FA guard) into this same
    integration branch, re-measured via a fresh `readelf -SW`. Grew to
    `0x5cc58` for the sequential multi-tx lane (`k3-3/bmvmx-5.5.10-seq-threading`,
    #10391: fail-closed BAL storage whitelist gate, cross-tx CREATE-nonce
    threading, execution-derived storage arenas), re-measured after merging
    main forward. Grew to `0x5cc90` after merging main forward past #10385
    (SSTORE value-unchanged exec-log-append skip), re-measured again. Grew to
    `0x5ccd0` for the combined batch-merge landing the BAL-completeness
    0-FA fix (`k3-3/rgtkz-bal-completeness`, #10419) together with the
    withdrawal/BAL-overlap fail-closed guard (`fix/withdrawals-bal-completeness`,
    #10420), measured via a fresh `readelf -SW` after both land together.
    Grew to `0x5cf18` for the withdrawal-BAL-parity fix (`fix/withdrawal-bal-parity`,
    #10422: models every nonzero EIP-4895 body withdrawal as a standard
    non-storage effect via the existing BAL comparators, closing the
    withdrawal-drop false-accept without the fail-closed false-reject of
    valid withdrawal blocks). Grew to `0x5cf20` for the CREATE
    nonstorage-effect-nonce-lookup fix (`fix/receipts-root-eip150`, #10429:
    the caller restored saved x10 before testing the hit bit, discarding a
    real nonce-table hit on CREATE and emitting a Transfer log for the
    wrong address). Grew to `0x5cf24` for the EOA body-withdrawal-drop
    fix (`fix/body-op-state-completeness`, #10435: materializes EIP-4895
    withdrawal credits as authenticated non-storage effects before the
    existing BAL 44/45 reconciliation). Grew to `0x5cf6c` for the
    combined batch-merge landing the BAL bounded-storage-builder
    fallback fix (`fix/bal-descriptor-exact`, #10438) together with
    the withdrawal-BAL bailout removal (`fix/withdrawal-bal-bail-removal`,
    #10439), measured via a fresh `readelf -SW` after both land
    together. Grew to `0x5cf80` for the combined batch-merge landing
    the a4gbr s-reg/scratch-own strengthen (#10442), the
    zisk_stateless_verdict_v2 probe closure fix (#10446), the
    execCodeEffectLogCap raise (#10447), and the nonstorage-effect
    overflow guard (#10448). Grew to `0x5cff4` for the net-deleted
    BAL-storage marker-scan fix (`fix/bal-netdeleted-storage`, #10452:
    demotes raw storage writes only when the account is recorded in
    the transaction-scoped EIP-6780 same-tx deletion table). Grew to
    `0x5d078` for the nested-CREATE final-nonce retention fix
    (`fix/create-final-nonce`, #10453). Grew to `0x5d120` for the callable
    per-transaction auxiliary-journal resets, which prevent stale execution
    evidence from crossing a transaction boundary. Grew to `0x5d188`
    for the value-CALL net-nonce-preservation fix
    (`fix/call-effect-net-nonce`, #10455). Grew to `0x5d1bc` for the
    EIP-7702 authorization net-nonce threading fix
    (`fix/auth-net-nonce`, #10456), which also split the auth-effect
    emitter out into `TxIntrinsicAuthEffects.lean` to clear the
    1500-line file-size cap. Grew to `0x5d204` for the SELFDESTRUCT
    live-origin-balance fix (`fix/selfdestruct-live-origin-balance`,
    #10457), mirroring the earlier beneficiary-balance overlay to fix
    a phantom second-selfdestruct credit. Settled to `0x5d20c` after
    merging main forward past #10458 (multi-tx caller-context staging
    fix) and this PR's own baap=501 delete-walk bail removal, measured
    via a fresh `readelf -SW`. Grew to `0x5d2a4` for the C3 arena
    overflow-reject batch (#10460). Grew to `0x5d518` for the bounded
    storage-root delete-walk fix (`fix/bounded-storage-delete-walk`,
    #10461), clearing the 98-fixture EIP-7002/7251 code-1 cluster. Shrank
    to `0x5d508` when full-subtree delete propagation was generalized to the
    canonical empty-trie root. Grew to `0x5d87c` when EIP-7702 authorization
    effect rows began preserving a prior value-transfer balance. Grew to
    `0x5d920` for the SUICIDE-6 selfdestruct/create fix
    (`diagnose/suicide-code44`, #10467). Grew to `0x5db78` for the
    per-frame CREATE nonce undo journal. Grew to `0x5dc40` for the
    CALLCODE stopHandlerCF per-depth metadata restore fix
    (`fix/mtx-sender-skip`, #10469), fixing the STOP-vs-RETURN
    asymmetry. Grew to `0x5dc54` for the receipts-shape enforce=true
    fix (`fix/mtx-receipts-enforce`, #10470), closing a latent
    false-accept on multi-tx unsupported receipts shapes 60/61/62
    (bail-elimination doctrine, maintainer-approved intentional FR
    increase 19->2080 exposing hidden FAs, not a regression). Shrank to
    `0x5dc4c` for the unconditional mtx process_transaction fix
    (`measure/mtx-whitelist-bypass`, #10471: removes the whitelist-v0
    admission gate, matching spec apply_body:913-914). Grew to `0x5e1e8`
    for the guarded post-setup top-level CREATE nonce seed
    (`fix/nested-create-nonce-seed`), which preserves the live nonce for
    nested CREATE executed from initcode. Grew to `0x5e63c` for the
    same-transaction constructor-SELFDESTRUCT EXTCODEHASH empty-code fallback
    (`fix/extcodehash-selfdestruct-empty`). Grew by `8` to `0x61160` for the
    KECCAK256 `ceil32` wraparound guard in `keccakWordGasAsm`
    (`fix/keccak-word-gas-wrap-guard`): one added `bltu` (4 B) plus 4 B of
    realignment. Grew by `0x60` to `0x611c0` for the MLOAD/MSTORE fresh-zero-loop
    arena clamp (`fix/memsize-zero-loop-clamp`, #10522): 13 added instructions
    plus a `beq`→`bgeu` swap in each of the two sparse handlers, and in NEITHER
    of the other 15 `updateActiveMemorySizeAsm` call sites — they pass
    `clampToArena = false` and stay byte-identical. Composes additively with the
    keccak guard above: `0x61160 + 0x60`. Grew by `0x54` for GH #10619's tracked
    account accessor (`account_at_header_state_root_tracked`,
    `AccountReadLog.lean`): 21 instructions — an 8-slot save/restore of `ra` and
    `a0`-`a6` around one `account_read_record` call, then a tail `j` to the raw
    entry. The 11 execution call sites retargeted onto it contribute **zero**
    bytes: a retarget only lengthens a `jal`'s symbol *name*, not the instruction.

    Now `0x61da4` after merging `main`, and the merge is exactly additive:
    `0x61510` (merge-base) `+ 0x79c` (this branch's six read containers, three
    producers, two-level promotion and tracked accessor) `+ 0xf8` (what landed on
    `main` meanwhile, including the BLS MSM discounts). Measured from the relinked
    ELF, not computed — the sum is stated because it *reconciles*, which is the
    check that the merge composed rather than one side silently winning. `.data`
    and `.bss` are unchanged by this branch's merge resolution.

    Grew by `0x4` — a single instruction — for GH #10619's stride
    parameterisation of `bal_storage_reads_in_exec_log`: the routine now takes
    its entry stride in `a5` instead of baking 128 into a `slli`/`addi` pair, so
    a caller cannot re-point the scan at another log without also supplying that
    log's entry width. Inside the routine the change is byte-neutral
    (`slli`→`mul`, `addi`→`sub`, and `mv s5, a5` reusing a dead `mv s6, a1`
    slot); the 4 bytes are the one `li a5, 128` added at the guest's single call
    site in `BlockVerdictFunction.lean`. The two probe call sites are in the
    probe unit and contribute nothing here.

    Then SHRANK by `0x40` -- 16 instructions -- to `0x61d68` for GH #10619's
    net-zero deletion: the tx-abort path's `.Lbv_tx0_storage_revert` loop, which
    walked the aborted transaction's storage exec-log rows setting
    `current := original`, is replaced by a single four-instruction truncation of
    the row count. The loop existed to keep the rows so the slots stayed
    "accessed" for the recipient `storage_reads` check; that check now reads the
    `storage_reads` container, so the rows no longer have to survive. First
    net REMOVAL of emitted bytes on this branch, and the shrink is the
    measurement that the collapse actually went away rather than becoming a
    no-op.

    Shrank by `0x40` -- 16 instructions -- to `0x61e0c` for GH #10654: the SECOND
    instance of the tx-abort net-zero loop, on the deposit-exception path in
    `BlockVerdictCreationStage.lean`. Its own comment said it mirrored the
    depth-zero abort cleanup, and it did -- identical shape, identical retired
    justification, identical `0x40` saving as #10641's. That PR fixed the clause
    it was pointed at; enumerating the pattern found the other one.

    Grew by `0xc` on main (GH #10870's coinbase accumulator) and by `0xd0` -- 208
    bytes -- here for GH #10866: the N+1 storage phase,
    `replay_system_storage_writes_at_bai` plus its call and incorporate at BOTH
    post-exec sites (they are mutually exclusive at run time, so both must carry
    it).  ELF-MEASURED, not summed: `0x067318 + 0xd0` is the obvious arithmetic and
    is NOT how this literal was set.  The value is an INPUT to emission, so a
    hand-computed one gets reflected back by the next relink and looks confirmed --
    an earlier draft of this same change measured `0x14` for what is now `0xd0`. -/
-- ELF-MEASURED after the relink, combining GH #10887's code_changes pointer
-- change, #10911's guarded post-static-check CALL target account-read
-- restoration, #10913's creation-stage running creator nonce fix,
-- #10930's top-level creation-target account-read
-- (`utils/message.py:71`), and #10931's durable upfront-balance
-- publish plus credit-path guard removal, then #10957's shared
-- body-state snapshot slab migration.
def textSizeBytes : Nat := 0x063b80

/-- ELF-measured `.data` size for the `stateless_guest` unit
    (`readelf -S`, `0x195726d0`). Link-layout-dependent. Shrank by `0x40` (64 B)
    when t1iqb resized `bv_cdl_stage` `32→64` for the verified arena-free
    CALLDATALOAD (`window ++ 32-byte zero pad` footprint). Earlier it grew by
    `0x4010000` (~64 MiB) when the `.71` reconciliation raised `frameStride`
    `0x29000→0x39000` (the `call_frame_arena` trailing pad). Grew by `0x4fb00`
    (~318 KiB) when `evm_precompile_frame`'s returndata window was sized to
    `precompileFrameReturndataCapBytes` so RETURNDATACOPY sees the full child
    return (evm-asm-pwqhw). Grew by `0x40` (64 B) when the `.data`→`.bss`
    splitter was fixed to keep mixed zero/nonzero groups (`blsg_b_be`,
    `p256_one_be`) whole in `.data` (evm-asm-rowr9). -/
def dataSizeBytes : Nat := 0x5370

/-- ELF-measured `.bss` size for the `stateless_guest` unit. Grew by `0x77900`
    for the fixed, gas-sized bounded indexed-root builder arenas, then `0x1d320`
    when the transaction descriptor staging was raised to the same gas bound.
    Grew by `0xc0` for the withdrawal-BAL-parity fix's per-withdrawal
    non-storage effect modeling (#10422). Grew by `0x160000`
    (execCodeEffectLogCap 128 KiB -> 1.5 MiB, #10447) so a full
    200M-gas block can never over-reject on deployed-code volume. Grew by
    `0xe08000` when the bounded non-storage effect log capacity was raised
    from 32768 to 65536 entries. Grew by `0x3c680` when the per-creator
    CREATE nonce table was raised from 64 to its 200M-gas-derived 6,250-entry
    capacity. Grew by `0x19bfa0` for the fixed-capacity EIP-7702 authority
    state table (address, nonce delta, and header-delegated bit). Grew by
    `0x1a000` for #10957's 1025-by-13 u64 body-state snapshot slab, then `0x2000`
    for GH #10619's fourteenth slab field (`storage_writes_undo_count`).

    ⚠️ That last step is `0x2000` and **not** the slab's own `1025 * 8 = 0x2008` growth:
    the eight-byte remainder is absorbed by the `.balign 32` that already followed the
    slab. Derived from the emitted addresses, not from arithmetic —
    `body_state_snapshot_by_depth` stays at `0xbb3a5688` while its successor
    `b1sc_sort_a` moves `0xbb3bf700 -> 0xbb3c1700`, because the slab's end goes
    `0xbb3bf6f0 -> 0xbb3c16f8` and both round up to the same 32-byte boundary, cutting
    the padding from 16 bytes to 8. **Do not predict this pin by subtraction**; a
    removal absorbs in the same direction (#10986, #10988). -/
def bssSizeBytes : Nat := 0x1c101b60

/-- ELF-measured fixed NOBITS capacity for the cross-transaction committed
    storage map. It is kept outside `.data` so zero initialization does not
    materialize a multi-megabyte payload, and outside `.bss` so the existing
    frame/SSZ layout remains stable. -/
def committedStorageSizeBytes : Nat := 0xcd9800

/-- Host input window (`INPUT_ADDR = 0x40000000`, 8 KiB; SSZ body at `+16`). -/
def inputRegion : GuestRegion :=
  { name := "INPUT", base := 0x40000000, size := 0x2000, mode := .ro, zone := .input,
    evidence := "Programs INPUT_ADDR; 8 KiB host SSZ input; [+0..8] ZisK meta, [+8..16] len, [+16..] body" }

/-- Public output window (`OUTPUT_ADDR = 0xa0010000`, 64 KiB). -/
def outputRegion : GuestRegion :=
  { name := "OUTPUT", base := 0xa0010000, size := 0x10000, mode := .rw, zone := .ram,
    evidence := "Programs OUTPUT_ADDR; 64 KiB SszStatelessValidationResult" }

/-- `.text` section (`-Ttext=0x80000000`). -/
def textRegion : GuestRegion :=
  { name := ".text", base := 0x80000000, size := textSizeBytes, mode := .rx, zone := .text,
    -- GH #10619: the two ELF-measured sizes below INTERPOLATE their pins rather than
    -- restating them.  The `.bss` string hardcoded `0x1c105000` and had gone stale by
    -- THREE merged PRs: #10979 shrank the pin and left the prose, then #10986 and #10988
    -- shrank it again, leaving the string `0xa020` bytes wrong.  Updating the digit would
    -- only re-stale it on the next repin — and note the `.text` evidence just above never
    -- went stale precisely because it states NO NUMBER.  The `.data` string was correct
    -- when this change was made and is interpolated anyway: a literal duplicating a named
    -- value with no tripwire is the exposure, whether or not it currently agrees.
    evidence := "ELF -Ttext=0x80000000; size link-dependent (drift guard)" }

/-- `.data` section (`-Tdata=0xa3000000`). Contains every static/verdict arena,
    including the `call_frame_arena` union family enumerated in `dataUnionArenas`. -/
def dataRegion : GuestRegion :=
  { name := ".data", base := 0xa3000000, size := dataSizeBytes, mode := .rw, zone := .ram,
    evidence := "ELF -Tdata=0xa3000000; 0x" ++ natToHex dataSizeBytes ++ "-byte PROGBITS extent" }

/-- Fixed-size cross-transaction committed-storage map
    (`--section-start=.committed_storage=0xa2000000`). -/
def committedStorageRegion : GuestRegion :=
  { name := ".committed_storage", base := 0xa2000000,
    size := committedStorageSizeBytes, mode := .nobits, zone := .ram,
    evidence := "ELF --section-start=.committed_storage=0xa2000000; fixed gas-bounded NOBITS map" }

/-- `.bss` zero-initialized arena (`--section-start=.bss=0xa3110000`). The
    base moved down from `0xa4000000` into the `.data` slack (`.data` uses
    only 21,360 B of its 16 MiB reservation) to make room for the GH #10836
    BAL-arena resize; the `.data`/`.bss` sum budget proved at
    `CallFrameLayout.lean` (`≤ sszScratchBase - dataBase = 0x1c980000`) is
    unchanged since neither endpoint moves. -/
def bssRegion : GuestRegion :=
  { name := ".bss", base := 0xa3110000, size := bssSizeBytes, mode := .nobits, zone := .ram,
    evidence := "ELF --section-start=.bss=0xa3110000; 0x" ++ natToHex bssSizeBytes ++ "-byte NOBITS extent" }

/-- `.sszscratch` NOBITS merkleization scratch
    (`--section-start=.sszscratch=0xbf980000`). -/
def sszScratchRegion : GuestRegion :=
  { name := ".sszscratch", base := 0xbf980000, size := 0x680000, mode := .nobits, zone := .ram,
    evidence := "ELF --section-start=.sszscratch=0xbf980000; 6.5 MiB NOBITS; MemoryLayout SSZ_SCRATCH_BASE/SIZE" }

/-! ## Emitted-reality regions the section/anchor lists omit.

    These are addresses the *currently-emitted* `stateless_guest` provably touches
    (verified from the emitted `.s`, guarded by `check-region-map.sh`) but which
    neither the scheme-A anchors nor the ELF sections cover. They are part of
    `guestRegionMap` so it accounts for every byte the guest uses. -/

/-- ZisK host/system band `[0xa0000000, 0xa0010000)`. The guest reads/writes the
    ZisK MTVEC (trap-vector) memory slot `0xa0009828` to save/restore the trap
    vector around the verdict (`StatelessGuestEpilogue`, `li t0, 0xa0009828`). -/
def ziskSystemRegion : GuestRegion :=
  { name := "zisk_system", base := 0xa0000000, size := 0x10000, mode := .rw, zone := .ram,
    evidence := "guest reads/writes ZisK MTVEC slot 0xa0009828 (StatelessGuestEpilogue trap save/restore)" }

/-- Top of the RV64 call stack, pinned by `_start`'s `li sp, 0xa0050000` (the sole
    `sp` init in the image). The stack grows DOWN from here. -/
def guestStackTop : Nat := 0xa0050000

/-- RV64 call stack, growing DOWN from `guestStackTop = 0xa0050000`. Budget
    `[0xa0020000, 0xa0050000)` = 192 KiB — the space between OUTPUT's top and the
    `sp` init; anything below `0xa0020000` would corrupt OUTPUT. NOTE: the current
    guest has no explicit stack-depth guard, so this is the *safe budget*, not a
    proven max depth; a real guard is the port's responsibility. This region
    overlaps the ASPIRATIONAL `execution_witness_area`/`ssz_input_decoded` anchors
    (see `guestStack_overlaps_executionWitnessArea`) — the collision the port must
    reflow. -/
def guestStackRegion : GuestRegion :=
  { name := "guest_stack", base := 0xa0020000, size := 0x30000, mode := .rw, zone := .ram,
    evidence := "_start `li sp, 0xa0050000` (grows down); budget bottoms at OUTPUT top 0xa0020000" }

/-- The state-tracker storage-log window ACTUALLY used by the emitted guest:
    `[0xa0630000, 0xa0830000)` = 2 MiB (16384x128 rows). The one live scheme-A
    anchor (`STATE_TRACKER_AREA`), sized to its real extent rather than the 4 MiB
    aspirational slab. -/
def stateTrackerLiveRegion : GuestRegion :=
  { name := "state_tracker_live", base := 0xa0630000, size := 0x200000, mode := .rw, zone := .ram,
    evidence := "emitted guest storage-log base 0xa0630000..0xa0830000 (2 MiB); the sole live scheme-A anchor" }

/-! ## The authoritative EMITTED-REALITY region map.

    One list, one source of truth, describing what the *currently-emitted*
    `stateless_guest` actually touches — this is the map routine triples and wave
    `.9.3` frame against. It is GENUINELY pairwise disjoint with NO exception
    list: `zisk_system`→OUTPUT→`guest_stack` tile `[0xa0000000, 0xa0050000)`
    contiguously; `state_tracker_live` ends `0xa0830000` well below `.data`
    (`0xa3000000`); `.data` ends `0xa3005370`, `.bss` ends `0xbf215000`,
    both below `.sszscratch`; INPUT and `.text` sit in their own zones. The
    guest's one intentional overlap lives strictly inside the `.bss` member and
    is expanded — as its own inventory —
    in `dataUnionChildren`/`aliasedPairs` below. The scheme-A anchors are the
    separate, aspirational port contract (`schemeAAnchors`), deliberately NOT in
    this list because they collide with `guest_stack` in the current build. -/
def guestRegionMap : List GuestRegion :=
  [ inputRegion, ziskSystemRegion, outputRegion, guestStackRegion,
    stateTrackerLiveRegion, textRegion, committedStorageRegion, dataRegion,
    bssRegion, sszScratchRegion ]

/-! ## Fit + disjointness for the emitted-reality map (kernel-checked). -/

/-- Every region in the emitted-reality map lies inside its declared zone
    (RAM regions within `0xa0000000..0xc0000000`, `.text` within its window,
    INPUT within the host input window). -/
theorem guestRegionMap_fits_ram : allFitZones guestRegionMap = true := by decide

/-- The emitted-reality map is pairwise disjoint — with NO exception list. Every
    byte the emitted guest touches is accounted for by exactly one region; the
    one intentional overlap lives strictly inside the `.bss` member and is
    documented separately in `dataUnionChildren`/`aliasedPairs`. -/
theorem guestRegionMap_pairwise_disjoint : allPairwiseDisjoint guestRegionMap = true := by decide

/-- The scheme-A anchors are internally consistent (pairwise disjoint among
    themselves), so the aspirational port map is self-coherent even though it
    collides with the emitted-reality `guest_stack` (next theorem). -/
theorem schemeAAnchors_pairwise_disjoint : allPairwiseDisjoint schemeAAnchors = true := by decide

/-! ## Emitted-vs-aspirational collision (the divergence the bead exists to surface).

    The RV64 call-stack top pinned by `_start` sits INSIDE the aspirational
    `execution_witness_area` slab, and the stack budget also overlaps
    `ssz_input_decoded`. These are kernel-checked so the port cannot silently
    ship the scheme-A layout on top of a live stack. Filed as a P1 divergence
    bead; input to the deferred phase-ownership half. -/

/-- `guestStackTop = 0xa0050000` lies within `execution_witness_area`
    `[0xa0030000, 0xa0130000)` — the RV64 call stack grows down straight through
    the aspirational witness-area slab. -/
theorem guestStack_overlaps_executionWitnessArea :
    0xa0030000 ≤ guestStackTop ∧ guestStackTop < 0xa0130000 := by decide

/-- The `guest_stack` budget `[0xa0020000, 0xa0050000)` is NOT disjoint from the
    aspirational `ssz_input_decoded` anchor `[0xa0020000, 0xa0030000)` — the
    concrete witness that `guestRegionMap` (emitted) and `schemeAAnchors`
    (aspirational) cannot be merged into one disjoint list today. -/
theorem guestStack_not_disjoint_from_schemeA :
    guestStackRegion.disjoint
      { name := "ssz_input_decoded", base := 0xa0020000, size := 0x10000,
        mode := .rw, zone := .ram, evidence := "" } = false := by decide

/-! ## `_matches_*`: pin the literals above to the real layout constants.

    A drift in either the region map or the upstream constant is a kernel error. -/

theorem inputRegion_matches_zone :
    inputRegion.base = INPUT_MEM_START ∧ inputRegion.eend = INPUT_MEM_END := by decide

theorem sszScratch_matches_layout :
    sszScratchRegion.base = (EvmAsm.Stateless.SSZ_SCRATCH_BASE).toNat
      ∧ sszScratchRegion.size = EvmAsm.Stateless.SSZ_SCRATCH_SIZE := by decide

theorem schemeA_matches_layout :
    (schemeAAnchors.map GuestRegion.base) =
      [ (EvmAsm.Stateless.SSZ_INPUT_DECODED).toNat,
        (EvmAsm.Stateless.EXECUTION_WITNESS_AREA).toNat,
        (EvmAsm.Stateless.NODE_DB_BUCKETS).toNat,
        (EvmAsm.Stateless.CODE_DB_BUCKETS).toNat,
        (EvmAsm.Stateless.STATE_TRACKER_AREA).toNat,
        (EvmAsm.Stateless.EVM_FRAME_STACK).toNat,
        (EvmAsm.Stateless.EVM_VALUE_STACK).toNat,
        (EvmAsm.Stateless.EVM_MEMORY_AREA).toNat,
        (EvmAsm.Stateless.KECCAK_SCRATCH).toNat,
        (EvmAsm.Stateless.ECRECOVER_SCRATCH).toNat,
        (EvmAsm.Stateless.SHA256_SCRATCH).toNat,
        -- GH #10619: the spec's three read sets (state_tracker.py:67-77, :96-104).
        (EvmAsm.Stateless.STORAGE_READS_AREA).toNat,
        (EvmAsm.Stateless.ACCOUNT_READS_AREA).toNat,
        (EvmAsm.Stateless.CODE_READS_AREA).toNat,
        (EvmAsm.Stateless.TX_STORAGE_READS_AREA).toNat,
        (EvmAsm.Stateless.TX_ACCOUNT_READS_AREA).toNat,
        (EvmAsm.Stateless.TX_CODE_READS_AREA).toNat,
        -- r59nm: the write side of the same two levels (state_tracker.py:74 block,
        -- :101 transaction) plus S5a's undo journal.
        (EvmAsm.Stateless.STORAGE_WRITES_AREA).toNat,
        (EvmAsm.Stateless.TX_STORAGE_WRITES_AREA).toNat,
        (EvmAsm.Stateless.STORAGE_WRITES_UNDO_AREA).toNat,
        -- #10695: the nonstorage write side of the same two levels
        -- (account_writes, state_tracker.py:70 block, :97 transaction) plus its
        -- undo journal.
        (EvmAsm.Stateless.ACCOUNT_WRITES_AREA).toNat,
        (EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA).toNat,
        (EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA).toNat ] := by decide

/-! ## Within-`.bss` aliasing inventory (the `call_frame_arena` union).

    ELF ground truth (`readelf -s`, this build; post-`4ch8f.73` — six children,
    `bv_system_storage_log` un-unioned):
    ```
    af420780  call_frame_arena  == basr_values
    b0c8b980  basr_accounts          (+  S)
    b24f6b80  baap_storage_desc      (+ 2S)
    b28c7480  baap_storage_paths
    b2ee1c80  baap_storage_delete_paths
    b34fc480  baap_storage_values
    b5839780  call_frame_arena_end   (== base + frameArrayBytes)
    ```
    with `S = bsrMaxStateChanges * bsrEncodedAccountBytes`. These are relocatable
    symbols reached via independent `la`; only the *offsets within the arena* are
    layout-invariant, so this inventory uses arena-relative offsets, not the
    absolute build addresses. The absolute base is captured once for
    cross-checking. -/

/-- Absolute base of `call_frame_arena` (== `basr_values`) in this build.
    LINK-LAYOUT-DEPENDENT — recorded so the drift guard can anchor the union. -/
def callFrameArenaBase : Nat := 0xaf420780

/-- Absolute shared nested-frame EVM-memory pool, emitted immediately after
    `call_frame_arena`. Both endpoints are link-layout-dependent pins checked
    against the ELF. -/
def evmMemoryPoolRegion : GuestRegion :=
  { name := "evm_memory_pool", base := 0xb5839780, size := evmMemoryPoolBytes,
    mode := .rw, zone := .ram,
    evidence := "ELF evm_memory_pool..evm_memory_pool_end; 96 MiB shared LIFO frame memory" }

theorem evmMemoryPoolRegion_matches_elf :
    evmMemoryPoolRegion.base = 0xb5839780
      ∧ evmMemoryPoolRegion.base + evmMemoryPoolRegion.size = 0xbb839780 := by decide

/-- The two runtime frame allocations are adjacent, disjoint, fit RAM, and both
    lie inside `.bss`; this is the pool/slot non-aliasing soundness fence. -/
def frameRuntimeRegions : List GuestRegion :=
  [ { name := "call_frame_arena", base := callFrameArenaBase, size := frameArrayBytes,
      mode := .rw, zone := .ram, evidence := "ELF call_frame_arena..call_frame_arena_end" },
    evmMemoryPoolRegion ]

theorem frameRuntimeRegions_fit : allFitZones frameRuntimeRegions = true := by decide
theorem frameRuntimeRegions_pairwise_disjoint :
    allPairwiseDisjoint frameRuntimeRegions = true := by decide
theorem frameRuntimeRegions_within_data :
    frameRuntimeRegions.all (fun r =>
      decide (bssRegion.base ≤ r.base ∧ r.base + r.size ≤ bssRegion.base + bssRegion.size)) = true := by decide

/-- `S` — the `basr_values`/`basr_accounts` per-arena stride. -/
def basrArenaBytes : Nat := bsrMaxStateChanges * bsrEncodedAccountBytes

/-- One coalesced child of `call_frame_arena`: name + arena-relative `[off, off+size)`. -/
structure UnionChild where
  name : String
  off  : Nat
  size : Nat
  deriving Repr

/-- The six Phase-H arenas coalesced into the front of `call_frame_arena`,
    in layout order, as arena-relative offset/size pairs. Mirrors the emit in
    `BlockVerdictDataSection.lean` (the `basr_values`/`basr_accounts` pair, then
    the four `baap_storage_*` arenas). `bv_system_storage_log` was removed from
    the union in `4ch8f.73` (it is read post-dispatch, so a frame slot would
    clobber it — it now lives standalone, see `syslogRegion`). -/
def dataUnionChildren : List UnionChild :=
  [ { name := "basr_values",              off := 0,                                          size := basrArenaBytes },
    { name := "basr_accounts",            off := basrArenaBytes,                             size := basrArenaBytes },
    { name := "baap_storage_desc",        off := 2 * basrArenaBytes,
                                          size := bsrMaxBalItems * baapStorageDescBytes },
    { name := "baap_storage_paths",       off := 2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes,
                                          size := bsrMaxBalItems * bsrPathBytes },
    { name := "baap_storage_delete_paths",off := 2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes + bsrMaxBalItems * bsrPathBytes,
                                          size := bsrMaxBalItems * bsrPathBytes },
    { name := "baap_storage_values",      off := 2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes + 2 * (bsrMaxBalItems * bsrPathBytes),
                                          size := bsrMaxBalItems * bsrPathBytes } ]

/-- Two union children occupy disjoint arena-relative ranges. -/
def UnionChild.disjoint (a b : UnionChild) : Bool :=
  decide (a.off + a.size ≤ b.off) || decide (b.off + b.size ≤ a.off)

def unionChildrenPairwiseDisjoint : List UnionChild → Bool
  | []      => true
  | c :: cs => cs.all (fun d => c.disjoint d) && unionChildrenPairwiseDisjoint cs

/-- Each child's range fits inside the arena `[0, frameArrayBytes)`. -/
def unionChildFitsArena (c : UnionChild) : Bool := decide (c.off + c.size ≤ frameArrayBytes)

/-- **The six coalesced arenas are mutually disjoint** (each owns a distinct
    sub-range of `call_frame_arena`). This is the "no self-corruption *among the
    unioned arenas*" fact — NOT the phase-liveness fact that they may share bytes
    with the frame array (that is the deferred half). -/
theorem dataUnionChildren_pairwise_disjoint :
    unionChildrenPairwiseDisjoint dataUnionChildren = true := by decide

/-- Every coalesced arena fits within `call_frame_arena` (`[0, frameArrayBytes)`),
    i.e. the union does not run past the frame array. Matches the trailing pad in
    `BlockVerdictDataSection.lean` and `CallFrameLayout.frameArray_unions_*`. -/
theorem dataUnionChildren_fit_arena :
    dataUnionChildren.all unionChildFitsArena = true := by decide

/-- The `call_frame_arena` byte range `[base, base + frameArrayBytes)` sits inside
    the `.bss` section. (`call_frame_arena_end` lies below its end.) -/
theorem callFrameArena_within_data :
    bssRegion.base ≤ callFrameArenaBase
      ∧ callFrameArenaBase + frameArrayBytes ≤ bssRegion.base + bssRegion.size := by decide

/-! ## `bv_system_storage_log` standalone placement (`4ch8f.73`).

    Un-unioned from `call_frame_arena` because it is WRITTEN pre-dispatch
    (`capture_system_storage_exec_rows`) but READ post-dispatch by the BAL
    validators (`bal_storage_matches_exec_log` / `_covers_exec_log` /
    `account_tuple_sequences_consistent`), while per-tx dispatch frames zero every
    byte of the arena. It now lives in its own `.data` region, entirely BELOW the
    arena. Sized `bvSystemStorageLogBytes` (= `2 * 16384` rows), sound per the
    runtime-exec-log source cap — see `BlockVerdictParams.bvSystemStorageLogCapacity`. -/

/-- Standalone base of `bv_system_storage_log` in this build (post-`.73`).
    LINK-LAYOUT-DEPENDENT — read from the ELF, guarded by `check-region-map.sh`. -/
def syslogBase : Nat := 0xad2defe0

/-- **The `.73` clobber is closed (load-bearing).** The un-unioned
    `bv_system_storage_log` region `[syslogBase, syslogBase + bvSystemStorageLogBytes)`
    ends at or before `call_frame_arena`'s base — it is entirely disjoint from the
    arena. Under the OLD union placement the syslog sat at arena offset `[2S, 2S+L)`
    and per-tx dispatch frames at depth ≥ 221 zeroed it before the post-dispatch BAL
    validators read it (the bug). Now it cannot be reached by the frame array at all. -/
theorem syslog_disjoint_from_frameArena :
    syslogBase + bvSystemStorageLogBytes ≤ callFrameArenaBase := by decide

/-- **No frame slot can clobber the syslog, for any call depth.** Frame slot `d`
    occupies `[callFrameArenaBase + (d-1)*frameStride, + frameStride)`, which starts
    at or after `callFrameArenaBase`; the syslog ends at or before it
    (`syslog_disjoint_from_frameArena`). So every reachable dispatch frame
    (`1 ≤ d`, in fact all `d`) is strictly above the entire syslog extent — the
    captured system-storage rows survive the whole per-tx dispatch window. This is
    the property that FAILED under the union placement and now holds by
    construction, complementing `CallFrameLayout.frameArray_covers_all_depths`
    (which keeps every slot inside the arena). -/
theorem syslog_below_every_frame_slot (d : Nat) (_hd : 1 ≤ d) :
    syslogBase + bvSystemStorageLogBytes
      ≤ callFrameArenaBase + (d - 1) * frameStride := by
  have h := syslog_disjoint_from_frameArena
  have hmono : callFrameArenaBase ≤ callFrameArenaBase + (d - 1) * frameStride :=
    Nat.le_add_right _ _
  omega

/-! ## Explicit overlap inventory (`aliasedPairs`).

    These are the ONLY intentionally-overlapping region pairs in the guest.
    Each pair is `(call_frame_arena, <coalesced child>)`; the child's absolute
    range is a strict sub-range of the arena. The per-pair `_overlap` theorem
    states the overlap RANGE precisely (as arena-relative offsets). The verified
    phase-ownership model that shows these shared bytes are never live
    simultaneously is DEFERRED (bead `.6`, Fable's half) — see
    `docs/call-frame-memory-layout.md` §5 and `docs/4ch8f-region-map.md`. -/
def aliasedPairs : List (String × String) :=
  dataUnionChildren.map (fun c => ("call_frame_arena", c.name))

/-- Every aliased pair names `call_frame_arena` as the umbrella and a real
    coalesced child; there are exactly six, matching `dataUnionChildren`
    (`bv_system_storage_log` was un-unioned in `4ch8f.73`). -/
theorem aliasedPairs_shape :
    aliasedPairs = [ ("call_frame_arena", "basr_values"),
                     ("call_frame_arena", "basr_accounts"),
                     ("call_frame_arena", "baap_storage_desc"),
                     ("call_frame_arena", "baap_storage_paths"),
                     ("call_frame_arena", "baap_storage_delete_paths"),
                     ("call_frame_arena", "baap_storage_values") ] := by decide

/-- **Overlap ranges (precise).** Each coalesced child aliases the arena over
    exactly `[child.off, child.off + child.size)` (arena-relative). Stated as the
    full offset/size table so the exact overlapping byte range of every aliased
    pair is machine-checked, not prose. -/
theorem aliasedPairs_overlap_ranges :
    dataUnionChildren.map (fun c => (c.off, c.off + c.size)) =
      [ (0,          basrArenaBytes),
        (basrArenaBytes, 2 * basrArenaBytes),
        (2 * basrArenaBytes, 2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes),
        (2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes,
           2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes
             + bsrMaxBalItems * bsrPathBytes),
        (2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes
           + bsrMaxBalItems * bsrPathBytes,
           2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes
             + 2 * (bsrMaxBalItems * bsrPathBytes)),
        (2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes
           + 2 * (bsrMaxBalItems * bsrPathBytes),
           2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes
             + 3 * (bsrMaxBalItems * bsrPathBytes)) ] := by decide

/-! ## Linker-facts bridge (data arena bases derivable from the map).

    Wave `.9.3` distinguishes STABLE addresses (pinned constants) from
    LINK-LAYOUT-DEPENDENT ones (function entries and `.data` symbol addresses,
    which move on any size change). The STABLE arena/section bases are exactly
    the ones expressible from this map; the machine-readable per-symbol table
    (including link-dependent function entries) lives in
    `scripts/asm-fixtures/symbol-addresses.tsv`, regenerated from the ELF. -/

/-- STABLE guest bases: `(symbol, absolute base)` for addresses pinned by codegen
    constants / linker flags (NOT by link layout). These may be hardcoded by
    downstream `la`/address consumers; everything else must be read from the ELF. -/
def stableGuestBases : List (String × Nat) :=
  [ ("INPUT_ADDR",        inputRegion.base),
    ("OUTPUT_ADDR",       outputRegion.base),
    ("zisk_system",       ziskSystemRegion.base),
    ("guest_stack_top",   guestStackTop),
    (".text",             textRegion.base),
    (".committed_storage", committedStorageRegion.base),
    (".data",             dataRegion.base),
    (".bss",              bssRegion.base),
    (".sszscratch",       sszScratchRegion.base) ]
  ++ schemeAAnchors.map (fun r => (r.name, r.base))

-- 20 -> 23: the three read-container anchors added for GH #10619.
-- 23 -> 26: the three per-transaction read containers (GH #10619 gate 3).
-- 26 -> 29: the two storage_writes levels and S5a's undo journal (r59nm).
--            Lost in a merge resolution of #10679 and restored here; the
--            constants and the guest's use of the addresses were never removed,
--            so three in-use regions had no disjointness or fit proof.
theorem stableGuestBases_length : stableGuestBases.length = 32 := by decide

end EvmAsm.Codegen.RegionMap
