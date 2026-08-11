/-
  EvmAsm.Codegen.RegionMap

  Authoritative, kernel-checked memory-region map for the stateless guest
  (bead `evm-asm-4ch8f.6`, mechanical half).

  This is the single source of truth reconciling the two address-space schemes
  that previously had no shared, machine-checked layout statement:

  * **Scheme A** — the working-RAM anchors in `EvmAsm/Stateless/MemoryLayout.lean`
    (`0xa0020000..0xa0b00000`), the layout the *verified stateless port* under
    `EvmAsm/Stateless/` addresses. Historically these anchors had *no* fit or
    disjointness lemma and their sizes were only implicit in the gaps between
    successive anchors. Here every anchor gets an explicit extent (the gap to the
    next anchor) and a per-region evidence note.
  * **Scheme B** — the linked `.data` at `0xa0b00000` (`-Tdata=`), the
    zero-initialized `.bss` at `0xa0b70000`, plus `.text`
    (`-Ttext=0x80000000`) and the `.sszscratch` NOBITS region
    (`--section-start=.sszscratch=0xbf980000`). Sizes here are the ELF ground
    truth (`readelf -S`), cross-checked by `scripts/check-region-map.sh`.

  **Location rationale.** This module imports both `CallFrameLayout`
  (Codegen layer) and `MemoryLayout` (verified-core layer, under `Stateless/`).
  Only the Codegen layer may import both (the layering guard forbids
  core → Codegen), so the region map lives here rather than under `Stateless/`.

  **Aliasing (soundness-critical, deferred proof).** The guest has exactly one
  intentional physical overlap: `call_frame_arena` (104,960,000 B, about
  100.1 MiB, EVM call-frame
  overlay) coalesces five execution-dead Phase-H arenas into its front
  (`basr_values`, `basr_accounts`, `baap_storage_desc`,
  `baap_storage_paths`, and `baap_storage_values`).
  The retired storage-log probe arenas are not part of the linked guest image.
  This file *documents* those overlaps precisely (`aliasedPairs` + the per-pair
  `_overlap` theorems) and proves the five coalesced children are mutually
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
import EvmAsm.Codegen.RegionMapLinkPins
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
    the old persistent half of `state_tracker_area` is retired; the emitted
    guest keeps only the transient-log sibling). They are kept here as a
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

/-! ## Bounded storage structures: caps, failure modes, derivations, lifetimes

    GH #11187 / #11189. Recorded here because these facts were being carried in
    issue comments and messages, and because a stale rationale in this file cost a
    correct finding an hour: the undo-journal note below used to claim it "needs no
    overflow path".

    | structure | cap | enforced at | AT THE CAP |
    |---|---|---|---|
    | legacy persistent exec log | 16,384 rows | retired from the emitted guest | ⭐ **not allocated** |
    | storage-write undo journal | 32,768 entries | `storage_writes_undo_push` (`bgeu t1, t2, .Lswup_fail`) | ⭐ **FAILS CLOSED** — latches overflow and rejects |

    The persistent exec-log row cap is retained only by the legacy Option-A
    assertions and modeled-system staging constants. The emitted guest no longer
    allocates that arena or appends rows to it. The journal remains finite and
    may conservatively reject at its cap; it does not silently omit a rollback
    record.

    **LIFETIMES — the journal is per-transaction** and its count is **zeroed** by
    `write_sets_incorporate_tx` and `write_sets_discard_tx` — both the commit and
    discard paths. The retired persistent-log counter remains only as a zeroed
    env-layout compatibility cell.

    ⚠️ **And the converse trap, which is how the journal note went wrong:** a
    capacity cap bounds OCCUPANCY, not FLOW. `destroy_storage` decrements
    `tx_storage_writes_count`, so freed rows are refilled and the journal's inflow
    is not bounded by the map's size. **Do not bound a flow with a capacity.**

    ⛔ **OVER-RESERVING IS NOT FREE HERE.** The old 76.8 MiB gas-derived reservation
    was unioned into `call_frame_arena`'s front and **physically zeroed** by per-tx
    dispatch frames at depth ≥ 221 before the BAL validators read it — the historical
    `4ch8f.73` clobber. ⇒ an unreachable gas bound is not merely wasteful; it has
    already produced one real defect.

    The journal side is known to be reachable (fixture `00192` hits 32,768
    exactly); its sizing remains a separate concern from the retired log arena.
-/

/-- The working-RAM anchor sub-regions, `0xa0020000..0xa25349c0` (the upper six are
    the GH #10619 read containers: three block-level, three per-transaction). Aspirational —
    see the section note; `schemeAAnchors_pairwise_disjoint` proves they are
    internally consistent, but they are NOT part of `guestRegionMap`. -/
def schemeAAnchors : List GuestRegion :=
  [ { name := "ssz_input_decoded",      base := 0xa0020000, size := 0x10000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout SSZ_INPUT_DECODED; 64 KiB slab (verified-port scheme A)" },
    { name := "execution_witness_area", base := 0xa0030000, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout EXECUTION_WITNESS_AREA; 1 MiB slab" },
    -- GH #11995: NODE_DB_BUCKETS (0xa0130000, 4 MiB) and CODE_DB_BUCKETS
    -- (0xa0530000, 1 MiB) removed — aspirational anchors for the deleted
    -- Stateless/Witness/{NodeDb,CodeDb} scaffolds; no emitted instruction
    -- ever referenced either base.
    { name := "state_tracker_area",     base := 0xa0630000, size := 0x400000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout STATE_TRACKER_AREA; legacy 4 MiB port-contract slab. "
        ++ "The persistent 2 MiB arena at 0xa0630000 is retired; the emitted guest keeps only the transient log at 0xa0830000. "
        ++ "The retired base is absent from the final emitted image; other aspirational anchors remain a separate port-contract audit. " },
    { name := "evm_frame_stack",        base := 0xa0a30000, size := 0x40000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout EVM_FRAME_STACK; 256 KiB slab" },
    { name := "evm_value_stack",        base := 0xa0a70000, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout EVM_VALUE_STACK; 1 MiB slab" },
    -- GH #11186: EVM_MEMORY_AREA / KECCAK_SCRATCH / ECRECOVER_SCRATCH /
    -- SHA256_SCRATCH removed from scheme-A — reclaimed into linked `.bss`
    -- (base 0xa0b70000) and the raised block-read pack. Production substitutes
    -- are `.bss` symbols `evm_memory`, `evm_memory_pool`, `call_frame_arena`.
    -- GH #10619 + #11186: THREE block-level read sets at cold bound 66,666.
    { name := "storage_reads_area",     base := 0xa1908780, size := 0x411a80,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout STORAGE_READS_AREA; 66,666x64 = 4,266,624 B (addrHash++slotKey); "
        ++ "cold bound 200M/3000 (GH #11186)" },
    { name := "account_reads_area",     base := 0xa1d1a200, size := 0x208d40,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout ACCOUNT_READS_AREA; 66,666x32 = 2,133,312 B (addrHash)" },
    { name := "code_reads_area",        base := 0xa1f22f40, size := 0x411a80,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout CODE_READS_AREA; 66,666x64 = 4,266,624 B (addrHash++codeHash); "
        ++ "consumer is the execution witness (stateless_host_exec_witness.py:182), NOT the BAL" },
    -- GH #10619 review gate 3: TRANSACTION level (tx caps stay 16384/16384/8192).
    { name := "tx_storage_reads_area",  base := 0xa23349c0, size := 0x100000,  mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_STORAGE_READS_AREA; per-tx storage_reads, merged up and cleared" },
    { name := "tx_account_reads_area",  base := 0xa24349c0, size := 0x80000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_ACCOUNT_READS_AREA; per-tx account_reads" },
    { name := "tx_code_reads_area",     base := 0xa24b49c0, size := 0x80000,   mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_CODE_READS_AREA; per-tx code_reads 8192x64 (cold bound 5588; GH #11186 D3)" },
    -- r59nm S2: WRITE side (block/tx storage maps already at derived targets).
    { name := "storage_writes_area",    base := 0xa25349c0, size := 0x823500, mode := .rw, zone := .ram,
      evidence := "MemoryLayout STORAGE_WRITES_AREA; 66,666x128 = 8,533,248 B "
        ++ "(addrHash++slotKey++value, 96 B used of a 128 B stride); block level, "
        ++ "filled only by write_sets_incorporate_tx" },
    { name := "tx_storage_writes_area", base := 0xa2d57ec0, size := 0xaea00, mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_STORAGE_WRITES_AREA; 5,588x128 = 715,264 B; "
        ++ "per-tx storage_writes, target of storage_write_record (mirrors set_storage, state_tracker.py:489)" },
    -- r59nm S5a: undo journal standing in for take_snapshot's dict copy
    -- (state_tracker.py:800-806) under the no-dynamic-allocation constraint --
    -- a per-frame copy would cost capacity x call depth.
    --
    -- GH #11189 / #11200: the journal has a finite capacity, but its overflow
    -- behavior is now fail-closed. `storage_writes_undo_push` checks the cursor
    -- before its first journal store, returns `a0 = 1`, and latches both
    -- `tx_storage_writes_overflow` and `storage_writes_overflow`; its callers
    -- reject or consume that latch before mutating/publishing the incomplete map.
    -- `destroy_storage` also checks the cursor before its read/drop side effects.
    -- Do not describe the cap as unreachable: value-unchanged SSTORE paths can
    -- journal without advancing the persistent execution-log cursor, so the
    -- capacity question is distinct from the fail-closed soundness fix.
    { name := "storage_writes_undo_area", base := EvmAsm.Codegen.storageWritesUndoBase, size := 0x1994e80, mode := .rw, zone := .ram,
      evidence := "MemoryLayout STORAGE_WRITES_UNDO_AREA; 167,652x160 = 26,824,320 B "
        ++ "(entryIndex, wasAbsent, prevValue|fullRow); reverse-replayed by write_sets_restore_frame; "
        ++ "160 B stride journals full 128 B row for destroy_storage wasAbsent=2. "
        ++ "relocated above .state_gas_diag; overflow is fail-closed: storage_writes_undo_push latches both tx/block flags and returns failure before any journal store; "
        ++ "Row audit: 16 B of the 160 (offsets 16..31) are never written and never read; "
        ++ "kind 0/1 need 40 B (32 B value + packed index/kind, 8-aligned), only kind 2 "
        ++ "needs the 128 B payload and it is bounded by distinct written slots, so "
        ++ "segregating by kind gives a 40 B hot array" },
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
    { name := "account_writes_area",    base := 0xbdb80000, size := 0x800000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout ACCOUNT_WRITES_AREA; 8 MiB = 65536x128; high pack GH #11186 "
        ++ "(AW→AU→TX_AW→SSZ); 65536 covers the 64035 distinct-account bound (#11770)" },
    { name := "account_writes_undo_area", base := 0xbe380000, size := 0x1400000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout ACCOUNT_WRITES_UNDO_AREA; 20 MiB = 163840x128; covers the "
        ++ "161204 account-write-EVENT bound derived in GH #11770; high pack between AW and TX_AW" },
    { name := "tx_account_writes_area", base := 0xbf780000, size := 0x200000, mode := .rw, zone := .ram,
      evidence := "MemoryLayout TX_ACCOUNT_WRITES_AREA; 2 MiB = 16384x128; per-tx "
        ++ "account_writes; high pack abuts .sszscratch (GH #11186)" } ]

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
    emitter out into the execution-time authorization-preparation path to
    clear the 1500-line file-size cap. Grew to `0x5d204` for the SELFDESTRUCT
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
abbrev textSizeBytes : Nat := RegionMapLinkPins.textSizeBytes

/-- ELF-measured `.data` size for the `stateless_guest` unit
    (`readelf -S`, current value `0x5370`). Link-layout-dependent; this is
    intentionally a short current fact rather than a copied growth history.
    The drift guard re-derives it from the linked ELF. -/
abbrev dataSizeBytes : Nat := RegionMapLinkPins.dataSizeBytes

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
    `body_state_snapshot_by_depth` stays at `0xbb09c688` while its successor
    `b1sc_sort_a` moves `0xbb0b6700 -> 0xbb0b8700`, because the slab's end goes
    `0xbb0b66f0 -> 0xbb0b86f8` and both round up to the same 32-byte boundary, cutting
    the padding from 16 bytes to 8. **Do not predict this pin by subtraction**; a
    removal absorbs in the same direction (#10986, #10988). -/
abbrev bssSizeBytes : Nat := RegionMapLinkPins.bssSizeBytes

/-- Base of `.state_gas_diag`. Unlike every other RAM section this one carries
    **no `--section-start` flag**: the linker places it immediately after
    `.bss`, so its base is a *consequence* of `bssSizeBytes` — and it is
    therefore **DERIVED here, not pinned**.

    ⚠️ GH #11186 landed this as an independent class-A pin first, on the
    reasoning that a hand-typed constant would go stale. Correct premise, wrong
    conclusion: **the right conclusion from *it is a consequence* is to derive
    it.** An independent pin for a derived quantity can contradict its own
    premise the moment the two are regenerated at different times — and while
    both were pins, `guestScratch_sat`'s `sepConj` join typechecked only because
    the two `abbrev`s happened to *reduce to the same numeral*. That is
    agreement by coincidence, not by construction: when `bssSizeBytes` moved
    under a branch, CI failed with an application type mismatch at
    `GuestImage.lean`, and a **clean** rebase (no conflict, no marker) produced a
    `RegionMapLinkPins` whose `stateGasDiagBase` described the old image while
    its `bssSizeBytes` described the new one.

    Derived, the join holds because the two bounds are the SAME TERM, with no
    reduction and no coincidence involved. `check-region-map.sh` then checks this
    derivation against the linked ELF (`.state_gas_diag base == .bss end`),
    which is also the only thing that can catch the one way it could break:
    padding, if a future `.bss` size were not 8-aligned. -/
abbrev stateGasDiagBase : Nat := 0xa0b70000 + bssSizeBytes

/-- ELF-measured `.state_gas_diag` size. -/
abbrev stateGasDiagSizeBytes : Nat := RegionMapLinkPins.stateGasDiagSizeBytes

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

/-- `.data` section (`-Tdata=0xa0b00000`). Contains the initialized static and
    verdict data; the call-frame union itself is in `.bss`. -/
def dataRegion : GuestRegion :=
  { name := ".data", base := 0xa0b00000, size := dataSizeBytes, mode := .rw, zone := .ram,
    evidence := "ELF -Tdata=0xa0b00000; 0x" ++ natToHex dataSizeBytes ++ "-byte PROGBITS extent" }

/-- `.bss` zero-initialized arena (`--section-start=.bss=0xa0b70000`). The
    base moved down from `0xa0b70000` into the `.data` slack (`.data` uses
    only 21,360 B of its 16 MiB reservation) to make room for the GH #10836
    BAL-arena resize; the `.data`/`.bss` sum budget proved at
    `CallFrameLayout.lean` (`≤ sszScratchBase - dataBase = 0x1c980000`) is
    unchanged since neither endpoint moves. -/
def bssRegion : GuestRegion :=
  { name := ".bss", base := 0xa0b70000, size := bssSizeBytes, mode := .nobits, zone := .ram,
    evidence := "ELF --section-start=.bss=0xa0b70000; 0x" ++ natToHex bssSizeBytes ++ "-byte NOBITS extent" }

/-- `.state_gas_diag` NOBITS per-transaction state-gas differential outputs
    (`DispatcherExecStateGas.lean:158`, emitted unconditionally). GH #11186:
    this section was in the image but in **no** region list, so neither
    `guestRegionMap_fits_ram` nor `guestRegionMap_pairwise_disjoint` ranged over
    it and `check-memorylayout-region-coverage.sh` could not see it — it is not
    a `MemoryLayout` anchor. It sits at the base of the largest free RAM gap,
    which is where an undeclared neighbour stops being harmless. -/
def stateGasDiagRegion : GuestRegion :=
  { name := ".state_gas_diag", base := stateGasDiagBase, size := stateGasDiagSizeBytes,
    mode := .nobits, zone := .ram,
    evidence := "ELF NOBITS section placed after .bss (no --section-start); base 0x"
      ++ natToHex stateGasDiagBase ++ ", 0x" ++ natToHex stateGasDiagSizeBytes ++ "-byte extent" }

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
    `[0xa0830000, 0xa0a30000)` = 2 MiB (16384x128 transient rows). The
    persistent 2 MiB arena formerly below it at `0xa0630000` has been retired. -/
def stateTrackerLiveRegion : GuestRegion :=
  { name := "transient_storage_log", base := 0xa0830000, size := 0x200000, mode := .rw, zone := .ram,
    evidence := "emitted guest transient storage-log base 0xa0830000..0xa0a30000 (2 MiB)" }

/-! ## The authoritative EMITTED-REALITY region map.

    One list, one source of truth, describing what the *currently-emitted*
    `stateless_guest` actually touches — this is the map routine triples and wave
    `.9.3` frame against. It is GENUINELY pairwise disjoint with NO exception
    list: `zisk_system`→OUTPUT→`guest_stack` tile `[0xa0000000, 0xa0050000)`
    contiguously; `transient_storage_log` ends `0xa0a30000` well below `.data`
    (`0xa0b00000`); `.data` ends `0xa0b05310`, `.bss` ends `0xbbefb8a0` where
    `.state_gas_diag` begins, and that ends `0xbbe68230`, all below
    `.sszscratch`; INPUT and `.text` sit in their own zones.
    ⚠️ The `.bss` end quoted here is a **current fact read off the image**, not a
    constant: it is `bssRegion.base + bssSizeBytes` and moves with every `.bss`
    growth. It read `0xbe6a4860` until GH #11186 found it stale by 37 MiB — the
    kernel-checked statements below are the load-bearing ones, this sentence is
    orientation. The
    guest's one intentional overlap lives strictly inside the `.bss` member and
    is expanded — as its own inventory —
    in `dataUnionChildren`/`aliasedPairs` below. The scheme-A anchors are the
    separate, aspirational port contract (`schemeAAnchors`), deliberately NOT in
    this list because they collide with `guest_stack` in the current build. -/
def guestRegionMap : List GuestRegion :=
  [ inputRegion, ziskSystemRegion, outputRegion, guestStackRegion,
    stateTrackerLiveRegion, textRegion, dataRegion,
    bssRegion, stateGasDiagRegion, sszScratchRegion ]

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
        -- GH #11995: NODE_DB_BUCKETS / CODE_DB_BUCKETS anchors removed.
        (EvmAsm.Stateless.STATE_TRACKER_AREA).toNat,
        (EvmAsm.Stateless.EVM_FRAME_STACK).toNat,
        (EvmAsm.Stateless.EVM_VALUE_STACK).toNat,
        -- GH #11186: EVM_MEMORY/KECCAK/ECRECOVER/SHA256 scratches reclaimed.
        -- GH #10619 + #11186: three read sets at cold bound 66,666.
        (EvmAsm.Stateless.STORAGE_READS_AREA).toNat,
        (EvmAsm.Stateless.ACCOUNT_READS_AREA).toNat,
        (EvmAsm.Stateless.CODE_READS_AREA).toNat,
        (EvmAsm.Stateless.TX_STORAGE_READS_AREA).toNat,
        (EvmAsm.Stateless.TX_ACCOUNT_READS_AREA).toNat,
        (EvmAsm.Stateless.TX_CODE_READS_AREA).toNat,
        (EvmAsm.Stateless.STORAGE_WRITES_AREA).toNat,
        (EvmAsm.Stateless.TX_STORAGE_WRITES_AREA).toNat,
        (EvmAsm.Stateless.STORAGE_WRITES_UNDO_AREA).toNat,
        -- High pack AW → AU → TX_AW → SSZ (GH #11186).
        (EvmAsm.Stateless.ACCOUNT_WRITES_AREA).toNat,
        (EvmAsm.Stateless.ACCOUNT_WRITES_UNDO_AREA).toNat,
        (EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA).toNat ] := by decide

/-! ## Within-`.bss` aliasing inventory (the `call_frame_arena` union).

    ELF ground truth (`readelf -s`, this build; five children):
    ```
    ad3dd5e0  call_frame_arena  == basr_values
    aec487e0  basr_accounts          (+  S)
    b04b39e0  baap_storage_desc      (+ 2S)
    b08842e0  baap_storage_paths
    b0e9eae0  baap_storage_values
    b37f65e0  call_frame_arena_end   (== base + frameArrayBytes)
    ```
    with `S = bsrMaxStateChanges * bsrEncodedAccountBytes`. These are relocatable
    symbols reached via independent `la`; only the *offsets within the arena* are
    layout-invariant, so this inventory uses arena-relative offsets, not the
    absolute build addresses. The absolute base is captured once for
    cross-checking. -/

/-- Absolute base of `call_frame_arena` (== `basr_values`) in this build.
    LINK-LAYOUT-DEPENDENT — class-A pin from `RegionMapLinkPins` (issue #11230 / #11282). -/
abbrev callFrameArenaBase : Nat := RegionMapLinkPins.callFrameArenaBase

/-! The memory-pool base is link-dependent too. Naming it separately lets the
    drift guard compare this absolute pin with the linked ELF, rather than
    checking only the relative 96 MiB extent. -/
abbrev evmMemoryPoolBase : Nat := RegionMapLinkPins.evmMemoryPoolBase

/-- Absolute shared nested-frame EVM-memory pool, emitted immediately after
    `call_frame_arena`. Both endpoints are link-layout-dependent pins checked
    against the ELF. -/
def evmMemoryPoolRegion : GuestRegion :=
  { name := "evm_memory_pool", base := evmMemoryPoolBase, size := evmMemoryPoolBytes,
    mode := .rw, zone := .ram,
    evidence := "ELF evm_memory_pool..evm_memory_pool_end; 96 MiB shared LIFO frame memory" }

/-- Pool endpoints follow the class-A pin aliases — no hand hex (fence #11282). -/
theorem evmMemoryPoolRegion_matches_elf :
    evmMemoryPoolRegion.base = evmMemoryPoolBase
      ∧ evmMemoryPoolRegion.base + evmMemoryPoolRegion.size =
        evmMemoryPoolBase + evmMemoryPoolBytes := by
  simp [evmMemoryPoolRegion, evmMemoryPoolBase, evmMemoryPoolBytes]

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

/-- The five Phase-H arenas coalesced into the front of `call_frame_arena`,
    in layout order, as arena-relative offset/size pairs. Mirrors the emit in
    `BlockVerdictDataSection.lean` (the `basr_values`/`basr_accounts` pair, then
    the three `baap_storage_*` arenas). -/
def dataUnionChildren : List UnionChild :=
  [ { name := "basr_values",              off := 0,                                          size := basrArenaBytes },
    { name := "basr_accounts",            off := basrArenaBytes,                             size := basrArenaBytes },
    { name := "baap_storage_desc",        off := 2 * basrArenaBytes,
                                          size := bsrMaxBalItems * baapStorageDescBytes },
    { name := "baap_storage_paths",       off := 2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes,
                                          size := bsrMaxBalItems * bsrPathBytes },
    { name := "baap_storage_values",      off := 2 * basrArenaBytes + bsrMaxBalItems * baapStorageDescBytes + bsrMaxBalItems * bsrPathBytes,
                                          size := bsrMaxBalItems * bsrPathBytes } ]

/-- Two union children occupy disjoint arena-relative ranges. -/
def UnionChild.disjoint (a b : UnionChild) : Bool :=
  decide (a.off + a.size ≤ b.off) || decide (b.off + b.size ≤ a.off)

def unionChildrenPairwiseDisjoint : List UnionChild → Bool
  | []      => true
  | c :: cs => cs.all (fun d => c.disjoint d) && unionChildrenPairwiseDisjoint cs

/-- Each child's range fits inside the arena `[0, frameArrayBytes)`. -/
def unionChildFitsArena (c : UnionChild) : Bool := decide (c.off + c.size ≤ frameArrayBytes)

/-- **The five coalesced arenas are mutually disjoint** (each owns a distinct
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
    coalesced child; there are exactly five, matching `dataUnionChildren`. -/
theorem aliasedPairs_shape :
    aliasedPairs = [ ("call_frame_arena", "basr_values"),
                     ("call_frame_arena", "basr_accounts"),
                     ("call_frame_arena", "baap_storage_desc"),
                     ("call_frame_arena", "baap_storage_paths"),
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
             + 2 * (bsrMaxBalItems * bsrPathBytes)) ] := by decide

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
-- 31 -> 27: GH #11186 reclaimed EVM_MEMORY + three crypto scratches into .bss
--            (four scheme-A anchors removed; section bases still 8).
-- 27 -> 25: GH #11995 removed the aspirational NODE_DB/CODE_DB bucket anchors
--            (never referenced by any emitted instruction).
theorem stableGuestBases_length : stableGuestBases.length = 25 := by decide

end EvmAsm.Codegen.RegionMap
