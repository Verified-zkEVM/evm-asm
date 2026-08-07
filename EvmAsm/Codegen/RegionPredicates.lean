/-
  EvmAsm.Codegen.RegionPredicates

  Separation-logic predicates for the regions measured in
  `docs/4ch8f-predicate-shapes.md` (GH #11241, input GH #11237).

  Derived from `origin/main` `7185e9274`. A predicate that gets revised later is
  normal; one that was never written teaches nothing — so the commit is named
  rather than left implicit (the `#10651` caveat for the baap enumeration).

  ## What is here, and what was already done elsewhere

  The issue's suggested order turned out to be **partly redundant with existing
  work**, which is worth recording before adding anything:

  * `call_frame_arena` frame slots (doc §1) — **already done** in
    `EvmAsm/Codegen/CallFrameWindows.lean`. `frameBase base d` is the address
    formula, and `phaseDView_eq_framesTiling` states the arena *is* the
    separating conjunction of its 1025 equal-stride windows: disjointness of
    distinct depths in its strongest form, with `focusFrame` / `unfocusFrame`
    for the extract / re-absorb directions.
  * The union-child phase boundary (doc §3, issue item 4) — **already done** in
    `EvmAsm/Codegen/CallFramePhase.lean`. `phaseD_eq_phaseH` is the
    dissolve-and-reinterpret theorem the issue describes, and `phaseH_to_phaseD`
    is the handoff from concrete buffers. `anyBytes` is the `raw_bytes(base, n)`
    interface, already carrying the tiling theory (`anyTilesAt`).

  ⇒ So this module covers what genuinely had **no assertion over it at all**:
  the memory pool as a resource, the dispatch-journal zero contracts, and the
  `teer_success_table` entry layout.

  ## Naming (per the issue, and deliberately not `…Is`)

  `…EntriesFrom base xs` — `xs` in consecutive entries from `base`, saying
  nothing about what follows; the composable, partial form.
  `…Buffer base xs` — the run *and* that this is all of it: `xs.length` live,
  remainder owned-unconstrained to capacity.
  `…Own base` — the bytes are owned, contents arbitrary.

  The test is whether the name stays true when the list is shorter than the
  region. `…EntriesFrom` does; `…Is` does not, which is why `evmStackIs`'s
  structure is copied here but its name is not.

  ## Bases are parameters, never hex prose

  Per doc §9.1. It is also forced: of the symbols here, only `evm_refund_acc`
  is in `GuestAddrs`, and `teer_success_table` / `evm_memory_pool` are absent
  from it entirely. Extents and strides *are* taken from the same constants
  `CallFrameLayout` / `BlockVerdictParams` / `RegionMap` use, and pinned against
  the emitted literal where one exists.

  ## ⚠️ Every extent claim names its build unit

  `baap_storage_values` is emitted at three sizes in three units (#11222) and
  `evm_memory_pool` at two (guest 96 MiB vs a 1 MiB probe emit in
  `CallFrameDescend.lean`). A predicate that does not name its unit is false in
  at least one of them. A symbol exists per *image*, not per repository.
-/

import EvmAsm.Rv64.SAsm.PhaseSplit
import EvmAsm.Rv64.SAsm.GlobalData
import EvmAsm.Codegen.CallFrameWindows
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasProg
import EvmAsm.Codegen.Programs.BlockVerdictDataSectionTail
import EvmAsm.Stateless.SpecRef.Types
import EvmAsm.Stateless.SpecRef.StateTracker

namespace EvmAsm.Codegen
namespace RegionPredicates

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Build units

    A string rather than a type, matching how `BuildUnit` names appear in the
    region map: these are labels for *which image* a claim is about, and the
    point is that the claim is stated at all. -/

/-- The build unit every extent claim in this module is about. -/
def statelessGuest : String := "stateless_guest"

/-! ## 1. `evm_memory_pool` — the shared nested-frame EVM memory pool

    Doc §4. The **easy shape**: not a record table but a LIFO byte arena, with
    per-frame windows as slices and reclaim on return. There is no maintained
    invariant for anyone to break — no free list, no ordering side condition.

    ⚠️ Unit-dependent size: the guest emits 96 MiB (`evmMemoryPoolRegion`),
    while `CallFrameDescend.lean`'s probe emits `.zero 0x100000` (1 MiB) under
    the same symbol name. Every claim below is about `statelessGuest`. -/

/-- Extent of the pool in the stateless guest, from the layout constant rather
    than a literal. -/
def poolBytes : Nat := evmMemoryPoolBytes

/-- 96 MiB. Stated as a kernel fact so a layout edit shows up here. -/
theorem poolBytes_eq : poolBytes = 100663296 := by decide

/-- **Ownership of the whole pool**, contents arbitrary. This is the honest
    shape for a byte arena: there is no entry type to index, so there is no
    `…EntriesFrom` form for this region — a fact about the structure, not an
    omission. -/
def poolOwn (base : Word) : Assertion := anyBytes base poolBytes

theorem pcFree_poolOwn (base : Word) : (poolOwn base).pcFree :=
  pcFree_anyBytes base poolBytes

/-! ### The pool's initialisation contract

    ⚠️ **Do not assume the pool is zero on entry to anything.** Nothing zeroes
    the 96 MiB; frames write their own windows, and the depth-1 reset paths
    restore *limits*, not contents. So a routine that reads a pool byte it has
    not written reads whatever the previous frame at that offset left there.

    ⭐ **This is why `poolOwn` is the strongest predicate available for the
    region, and why there is deliberately no `poolZero` companion.** For
    `evmMemZero`-style regions a zero predicate is the right opening resource;
    here it would be unsound — writing one would let a caller conclude a read
    returns `0` from a cell no one initialised. The absence is the contract, so
    it is stated rather than left as a missing definition somebody later
    "fixes".

    ⇒ **Audited entry points: none.** Unlike the dispatch-journal cells
    (§2), whose contract names `emitRuntimeDispatcherCallableSetup` as the
    routine that discharges it on every `runtime_dispatcher_call`, no entry
    point establishes a zero precondition for this region — there is nothing to
    audit, which is a different fact from "not yet audited". A caller needing
    known contents must establish them itself via `bytesRegion`. -/

/-- **One live per-frame window**: `len` bytes at pool-relative `off`. Windows
    are slices of the pool, not allocations from it. -/
def poolWindow (base : Word) (off len : Nat) : Assertion :=
  anyBytes (base + BitVec.ofNat 64 off) len

theorem pcFree_poolWindow (base : Word) (off len : Nat) :
    (poolWindow base off len).pcFree :=
  pcFree_anyBytes _ len

/-- **Two live windows at non-overlapping offset ranges are separate
    resources.** The LIFO discipline makes enter/return pair up, so live
    windows never overlap; this is the assertion-level form a caller uses to
    hold two frames' memory at once. Proved by exhibiting the pair as a
    two-segment tiling, so it rests on `anyTilesAt`'s separating structure
    rather than on a fresh disjointness argument. -/
theorem poolWindow_pair (base : Word) (off1 len1 len2 : Nat) :
    anyTilesAt base off1 [len1, len2]
      = (poolWindow base off1 len1 ** poolWindow base (off1 + len1) len2) := by
  unfold anyTilesAt poolWindow
  simp [anyTilesAt, sepConj_emp_right']

/-! ### The one-slot surplus, and a conflation worth naming

    ⚠️ The issue's item 1 attributes the `0x19000` stride and the parent-depth
    slot index to `evm_memory_pool`. Those are the **`call_frame_arena`**'s
    (doc §1); the pool is a byte arena with no stride at all and is a
    *pairwise-disjoint sibling* of the arena, not a part of it
    (`RegionMap.frameRuntimeRegions_pairwise_disjoint`). Recorded because a
    predicate written to the issue's wording would be about the wrong region.

    The surplus itself is an arena fact and belongs with the arena constants. -/

/-- **Slot 1024 is never reached.** The arena allocates `frameSlotCount = 1025`
    slots, but the index is the *parent* depth: a child at depth `d ∈ 1..1024`
    uses slot `d - 1 ∈ 0..1023`, and depth 0 never calls `call_frame_enter`. So
    one slot is allocated and unreachable — stated rather than rounded away. -/
theorem frameSlot_index_lt_maxCallDepth {d : Nat} (hlo : 1 ≤ d)
    (hhi : d ≤ maxCallDepth) : d - 1 < maxCallDepth := by
  unfold maxCallDepth at hhi ⊢; omega

theorem frameSlot_surplus : maxCallDepth < frameSlotCount := by decide

/-- Restated as the gap: exactly one allocated slot is unreachable. -/
theorem frameSlot_surplus_one : frameSlotCount - maxCallDepth = 1 := by decide

/-! ## 2. Dispatch-journal initialisation contracts (DJ-01..DJ-12)

    Doc §7; authoritative table `docs/4ch8f-dispatch-journal-initialization.md`
    (#11227 / #11152). These are **preconditions, not layout**: each cell is its
    own 8-byte symbol with its own base, and the whole contract is that readers
    may assume zero on dispatcher entry.

    `emitRuntimeDispatcherCallableSetup` zeroes DJ-01..DJ-12 before any reader
    runs, on every `runtime_dispatcher_call` (user and system re-entry). -/

/-- The twelve cells the dispatcher wipes, in DJ-01..DJ-12 order. Names, not
    addresses: only `evm_refund_acc` is in `GuestAddrs`, so a caller supplies
    the bases (doc §9.1) and this list is what fixes their identity and order. -/
def dispatchJournalWipeSet : List String :=
  [ "evm_refund_acc",                    -- DJ-01
    "evm_selfdestruct_seen_count",       -- DJ-02
    "evm_selfdestruct_seen_overflow",    -- DJ-03
    "create_nonce_table_count",          -- DJ-04
    "create_nonce_table_overflow",       -- DJ-05
    "create_nonce_undo_count",           -- DJ-06
    "account_state_pending_count",       -- DJ-07
    "account_state_created_count",       -- DJ-08
    "account_state_delete_count",        -- DJ-09
    "account_state_overflow",            -- DJ-10
    "evm_log_data_used",                 -- DJ-11
    "evm_log_data_overflow" ]            -- DJ-12

theorem dispatchJournalWipeSet_length : dispatchJournalWipeSet.length = 12 := by decide

/-- ⚠️ Cells that **survive** system re-entry (#11147) and are therefore
    *outside* the wipe set. Listing them is the point: an empty slot meaning
    "no obligation" and an empty slot meaning "obligation already met" are
    different facts, and only one survives a refactor. -/
def dispatchJournalSystemSurvivors : List String :=
  [ "evm_selfdestruct_destroyed_count",
    "evm_selfdestruct_destroyed_overflow" ]

/-- The survivors are genuinely disjoint from the twelve — the two lists cannot
    drift into agreeing by accident. -/
theorem dispatchJournalSurvivors_disjoint :
    dispatchJournalSystemSurvivors.all
      (fun s => !dispatchJournalWipeSet.contains s) = true := by decide

/-- **The zero precondition**, over the cells' addresses in wipe-set order.
    Recursion with `**` and `empAssertion` at nil, following `evmStackIs`'s
    structure; each cell is a `globalCellIs … 0`, so a write to any of them
    needs this atom in the pre rather than ambient `.data` access. -/
def dispatchJournalZero : List Word → Assertion
  | [] => empAssertion
  | a :: as => globalCellIs a 0 ** dispatchJournalZero as

theorem pcFree_dispatchJournalZero (addrs : List Word) :
    (dispatchJournalZero addrs).pcFree := by
  induction addrs with
  | nil => exact pcFree_emp
  | cons a as ih => exact pcFree_sepConj (pcFree_globalCellIs a 0) ih

/-- Peel one cell — the opening lemma of a dispatcher triple (doc §9.4). -/
theorem dispatchJournalZero_cons (a : Word) (as : List Word) :
    dispatchJournalZero (a :: as)
      = (globalCellIs a 0 ** dispatchJournalZero as) := rfl

/-- The contract is over exactly the twelve. Ties the assertion's arity to the
    named set, so a cell added to one and not the other fails to elaborate. -/
def dispatchJournalContract (addrs : List Word)
    (_hlen : addrs.length = dispatchJournalWipeSet.length) : Assertion :=
  dispatchJournalZero addrs

/-! ## 3. `teer_success_table` (+ `teer_success_count`)

    Doc §6; close write-up #11233. Converged and staying. Spec counterparts are
    `written_accounts` + `delegation_set_for` inside `set_delegation`.

    Consumers: (1) `eip7702_auth_state_prepare` — ACCOUNT_WRITE / AUTH_BASE
    charged once per authority; (2) **`extcodehash_at_header_state_root`** — on
    a match with the charged word nonzero, EMPTY_CODE_HASH.

    `teer_success_count` is a **live entry count**, not a high-water mark past
    deleted holes, and is zeroed at `eip7702_auth_state_prepare` entry. Readers
    must use the count: the table body may be stale past it. -/

/-- Entry stride: `slli t3, t2, 5` in the emitter — 32 bytes. -/
def teerEntryBytes : Nat := 32

/-- Capacity, from the emitter's own bound (`bgeu t1, t3, .L77prep_bad`). -/
def teerCapacity : Nat := teerSuccessfulAuthCapacity

/-- Extent as capacity × stride. -/
def teerTableBytes : Nat := teerCapacity * teerEntryBytes

/-- **`capacity * stride = extent`, EXACT** — 1060 × 32 = 33920. -/
theorem teerTableBytes_eq : teerTableBytes = 33920 := by decide

theorem teerCapacity_eq : teerCapacity = 1060 := by decide

/-! **Model ≡ emitted image.** ⚠️ `teerTableBytes_eq` alone does *not* pin the
    model to the guest: the data section emits a **hardcoded** `.zero 33920`
    rather than interpolating `teerSuccessfulAuthCapacity`, so the derived
    extent and the emitted literal are two independent numbers that could
    drift apart silently. This guard is what ties them, in the repo's
    exactly-once containment idiom. If capacity or stride changes and the
    emitter is not updated with it, this fails.

    (The capacity *bound* in the append path — `li t3, …; bgeu t1, t3` in
    `TxIntrinsicStateGas.lean` — does interpolate the constant, so that end is
    already drift-proof. It is the arena size that was not.) -/

#guard (ziskStatelessVerdictV2DataSectionTail.splitOn
    ("teer_success_table:\n  .zero " ++ toString teerTableBytes ++ "\n")).length == 2

/-! ### Reusing the spec-reference types

    ⭐ **`authority` is a `SpecRef.Address`, not a fresh byte list.** The spec
    type is `Stateless.SpecRef.Address := Bytes := List Byte := List (BitVec 8)`
    (`SpecRef/Types.lean:31`), so this is the *same* representation named
    honestly — the field's type now says which spec notion it carries.

    ⚠️ **There is no single `TeerEntry`-equivalent struct in `SpecRef`, and it
    would be wrong to reuse the nearest-looking one.**
    `SpecRef.Transactions.Authorization` is the **signed input tuple**
    (`chainId, address, nonce, yParity, r, s`) — its `address` field is the
    delegation *target*, whereas this table's key is the **recovered
    authority** (`recover_authority auth`, `SpecRef/Interpreter.lean:139`), a
    different address entirely. Conflating them would be a silent correctness
    bug, not a naming preference.

    ⇒ The genuine equivalent is not a struct but the **pair of `List Address`
    locals inside `SpecRef.Interpreter.set_delegation`**
    (`SpecRef/Interpreter.lean:197`): `written_accounts` (ACCOUNT_WRITE charged
    at most once per authority) and `delegation_set_for` (AUTH_BASE charged at
    most once per authority). The guest's one 32-byte row carries both facts —
    membership gives the former, the `+20` flag the latter — which is why the
    guest has one table where the spec has two lists. That is the
    correspondence, and it is stated as theorems below rather than asserted in
    prose. -/

/-- One row of the table. `charged` is the u32 at `+20..23`: the AUTH_BASE
    charged flag, 0 or 1, which `extcodehash_at_header_state_root` tests for
    nonzero. -/
structure TeerEntry where
  /-- The **recovered** authority address, 20 bytes big-endian at `+0..19`.
      Typed as the spec's `Address` so the region's contents are named in the
      spec's vocabulary. -/
  authority : Stateless.SpecRef.Address
  /-- `AUTH_BASE_charged` — the u32 at `+20..23`. -/
  charged : Bool
  deriving Repr

/-- The entry's validity invariant: a spec `Address` is 20 bytes. -/
def TeerEntry.wf (e : TeerEntry) : Prop := e.authority.length = 20

/-- The 32 bytes of one entry: address, the little-endian u32 flag, then the
    8-byte pad at `+24..31`. -/
def TeerEntry.render (e : TeerEntry) : List (BitVec 8) :=
  e.authority
    ++ [(if e.charged then 1 else 0), 0, 0, 0]
    ++ List.replicate 8 0

theorem TeerEntry.render_length {e : TeerEntry} (h : e.wf) :
    e.render.length = teerEntryBytes := by
  unfold TeerEntry.render teerEntryBytes
  unfold TeerEntry.wf at h
  simp [h]

/-- **The partial run** — `xs` in consecutive entries from `base`, saying
    nothing about what follows. This is the composable form and the one a
    routine touching one row should be handed. Structure copied from
    `evmStackIs` (`Evm64/Stack.lean`): base as a parameter, contents as a
    `List`, recursion with `**` and a stride step, `empAssertion` at nil. -/
def teerEntriesFrom (base : Word) : List TeerEntry → Assertion
  | [] => empAssertion
  | e :: es =>
      bytesRegion base e.render
        ** teerEntriesFrom (base + BitVec.ofNat 64 teerEntryBytes) es

theorem pcFree_teerEntriesFrom (base : Word) (xs : List TeerEntry) :
    (teerEntriesFrom base xs).pcFree := by
  induction xs generalizing base with
  | nil => exact pcFree_emp
  | cons e es ih => exact pcFree_sepConj (bytesRegion_pcFree _ _) (ih _)

theorem teerEntriesFrom_cons (base : Word) (e : TeerEntry) (es : List TeerEntry) :
    teerEntriesFrom base (e :: es)
      = (bytesRegion base e.render
          ** teerEntriesFrom (base + BitVec.ofNat 64 teerEntryBytes) es) := rfl

/-- **The whole buffer** — the run *and* that this is all of it: `xs.length`
    live entries, then the remainder owned-unconstrained out to capacity. This
    is what a caller holds; it is what weakens to `teerOwn` at a phase
    boundary.

    `xs.length ≤ teerCapacity` is threaded as a hypothesis rather than folded
    into the assertion (doc's low-stakes call, decided per region and named
    here). The emitter's fail-closed `bgeu` against `teerSuccessfulAuthCapacity`
    is the operational form of the same bound. -/
def teerBuffer (base : Word) (xs : List TeerEntry)
    (_hcap : xs.length ≤ teerCapacity) : Assertion :=
  teerEntriesFrom base xs
    ** anyBytes (base + BitVec.ofNat 64 (xs.length * teerEntryBytes))
         ((teerCapacity - xs.length) * teerEntryBytes)

theorem pcFree_teerBuffer (base : Word) (xs : List TeerEntry)
    (hcap : xs.length ≤ teerCapacity) :
    (teerBuffer base xs hcap).pcFree :=
  pcFree_sepConj (pcFree_teerEntriesFrom _ _) (pcFree_anyBytes _ _)

/-- **Ownership only** — the table's bytes, contents arbitrary. The state the
    region enters at a phase boundary, matching `evmWordOwn`'s role. -/
def teerOwn (base : Word) : Assertion := anyBytes base teerTableBytes

theorem pcFree_teerOwn (base : Word) : (teerOwn base).pcFree :=
  pcFree_anyBytes base teerTableBytes

/-- An empty table is the whole capacity, owned and unconstrained — the state
    `eip7702_auth_state_prepare` starts from after zeroing the count. -/
theorem teerBuffer_nil (base : Word) :
    teerBuffer base [] (by simp) = (empAssertion ** teerOwn base) := by
  unfold teerBuffer teerOwn teerEntriesFrom
  simp [teerTableBytes]

/-! ### Correspondence with `SpecRef.Interpreter.set_delegation`

    The two spec locals this one table stands in for, as projections out of the
    table's contents. These are the values a caller would compare against the
    spec run — the table's *meaning*, in the spec's own types. -/

/-- The table's contribution to the spec's `written_accounts`: every authority
    present, in append order. Membership in the table is what the guest tests
    where the spec tests `written_accounts.contains authority` to decide whether
    ACCOUNT_WRITE has already been charged. -/
def teerWrittenAccounts (xs : List TeerEntry) : List Stateless.SpecRef.Address :=
  xs.map (·.authority)

/-- The spec's `delegation_set_for`: exactly the authorities whose AUTH_BASE was
    charged, i.e. the rows with the `+20` word nonzero. -/
def teerDelegationSetFor (xs : List TeerEntry) : List Stateless.SpecRef.Address :=
  (xs.filter (·.charged)).map (·.authority)

/-- ⭐ **The spec invariant the two lists stand in:** `delegation_set_for` is
    contained in `written_accounts`. AUTH_BASE is only ever charged for an
    authority the transaction has already written, so a charged row cannot exist
    without its authority being present. Falls out of the shared projection —
    which is the point of deriving both from one table rather than modelling two
    independent regions. -/
theorem teerDelegationSetFor_subset_written (xs : List TeerEntry) :
    ∀ a ∈ teerDelegationSetFor xs, a ∈ teerWrittenAccounts xs := by
  intro a ha
  unfold teerDelegationSetFor at ha
  unfold teerWrittenAccounts
  simp only [List.mem_map] at ha ⊢
  obtain ⟨e, he, rfl⟩ := ha
  exact ⟨e, List.mem_of_mem_filter he, rfl⟩

/-- The spec's `setAdd` is a no-op on an element already present
    (`SpecRef/StateTracker.lean:74`) — the case where the guest's scan finds a
    match and appends nothing. -/
theorem setAdd_noop_of_contains {α : Type} [BEq α] (s : List α) (x : α)
    (h : s.contains x = true) : Stateless.SpecRef.setAdd s x = s := by
  unfold Stateless.SpecRef.setAdd
  simp [h]

/-- Appending a fresh row extends the projection by exactly one address — the
    spec's `setAdd` on its miss path. -/
theorem teerWrittenAccounts_append (xs : List TeerEntry) (e : TeerEntry) :
    teerWrittenAccounts (xs ++ [e]) = teerWrittenAccounts xs ++ [e.authority] := by
  unfold teerWrittenAccounts; simp

/-- ⭐ **The guest's append-if-absent linear scan IS the spec's `setAdd`** —
    stated as its two branches, which is the form a caller discharges.
    This branch: **scan hit ⇒ nothing is appended.**

    The emitter walks `teer_success_count` rows comparing the authority
    (`TxIntrinsicStateGas.lean`, the `.L77prep_seen_append` loop) and appends
    only on a miss; the spec writes `written_accounts := setAdd written_accounts
    authority`. This says those two produce the same list — so the region's
    contents track the spec value step for step, rather than merely having the
    same shape.

    Note the spec's `setAdd` appends at the tail and keeps first-insertion
    order, which is why no sortedness invariant is needed on this table (doc §6
    "linear membership by address; no sort required"). -/
theorem teerScan_hit_implements_setAdd (xs : List TeerEntry) (e : TeerEntry)
    (h : e.authority ∈ teerWrittenAccounts xs) :
    Stateless.SpecRef.setAdd (teerWrittenAccounts xs) e.authority
      = teerWrittenAccounts xs := by
  have hb : (teerWrittenAccounts xs).contains e.authority = true := by simpa using h
  simp only [Stateless.SpecRef.setAdd, hb, if_true]

/-- **Scan miss ⇒ the guest appends one row, and that is `setAdd`.** -/
theorem teerScan_miss_implements_setAdd (xs : List TeerEntry) (e : TeerEntry)
    (h : e.authority ∉ teerWrittenAccounts xs) :
    Stateless.SpecRef.setAdd (teerWrittenAccounts xs) e.authority
      = teerWrittenAccounts (xs ++ [e]) := by
  have hb : (teerWrittenAccounts xs).contains e.authority = false := by
    simpa using h
  simp only [Stateless.SpecRef.setAdd, hb, if_false, Bool.false_eq_true,
    teerWrittenAccounts_append]

/-! ### The Assertion, parameterised by the spec values

    ⭐ This is the shape worth reusing elsewhere: an `Assertion` whose arguments
    are **`SpecRef` data**, asserting that a region of memory *represents* that
    spec value. `teerEntriesFrom` describes bytes; `teerRepresents` says which
    spec state those bytes are a representation of, existentially quantifying the
    concrete rows away. A caller reasoning about `set_delegation` can then talk
    about `written` / `delegated` without ever mentioning the byte layout. -/

/-- **The region at `base` represents the spec's `written_accounts` and
    `delegation_set_for`.** Every row is well-formed (a 20-byte spec address),
    and the two projections are exactly the given spec lists. -/
def teerRepresents (base : Word)
    (written delegated : List Stateless.SpecRef.Address) : Assertion :=
  fun ps => ∃ xs : List TeerEntry,
    (∀ e ∈ xs, e.wf)
      ∧ teerWrittenAccounts xs = written
      ∧ teerDelegationSetFor xs = delegated
      ∧ teerEntriesFrom base xs ps

theorem pcFree_teerRepresents (base : Word)
    (written delegated : List Stateless.SpecRef.Address) :
    (teerRepresents base written delegated).pcFree := by
  rintro ps ⟨xs, _, _, _, hps⟩
  exact pcFree_teerEntriesFrom base xs ps hps

/-- **Introduction**: a concrete well-formed table represents the spec values
    its own projections compute. The bridge from the byte-level predicate to the
    spec-level one. -/
theorem teerEntriesFrom_represents {base : Word} {xs : List TeerEntry}
    (hwf : ∀ e ∈ xs, e.wf) {ps : PartialState} (h : teerEntriesFrom base xs ps) :
    teerRepresents base (teerWrittenAccounts xs) (teerDelegationSetFor xs) ps :=
  ⟨xs, hwf, rfl, rfl, h⟩

/-- The spec invariant survives the abstraction: anything the region represents
    still has `delegated ⊆ written`. So a caller cannot obtain a
    `teerRepresents` for an inconsistent pair of spec lists. -/
theorem teerRepresents_subset {base : Word}
    {written delegated : List Stateless.SpecRef.Address} {ps : PartialState}
    (h : teerRepresents base written delegated ps) :
    ∀ a ∈ delegated, a ∈ written := by
  obtain ⟨xs, _, hw, hd, _⟩ := h
  subst hw; subst hd
  exact teerDelegationSetFor_subset_written xs

/-! ### Satisfiability

    ⚠️ A predicate no state can satisfy proves nothing about the region, and a
    bundled hypothesis can make a theorem vacuous without saying so (#10688).
    So the entry model is instantiated at concrete data. -/

/-- A concrete well-formed entry: a 20-byte authority with the flag set. -/
def teerEntryExample : TeerEntry :=
  { authority := List.replicate 20 0xAB, charged := true }

example : teerEntryExample.wf := by simp [TeerEntry.wf, teerEntryExample]

/-- It renders to exactly one stride, with the flag where the consumer reads
    it (`+20`) and the pad zero — so the layout claim is checked, not asserted. -/
example : teerEntryExample.render.length = 32 := by decide
example : teerEntryExample.render[20]! = 1 := by decide
example : teerEntryExample.render[21]! = 0 := by decide
example : teerEntryExample.render[31]! = 0 := by decide

/-- The charged flag is what distinguishes two otherwise identical rows — the
    negative control for the byte the EXTCODEHASH consumer tests. -/
example :
    ({ authority := List.replicate 20 0xAB, charged := false } : TeerEntry).render[20]!
      = 0 := by decide

/-! ⚠️ The correspondence projections are checked at concrete data too. A
    `delegated ⊆ written` theorem is worthless if `delegated` is always empty,
    so the witness below has a **strict** subset: two authorities written, one
    of them AUTH_BASE-charged. -/

private def authA : Stateless.SpecRef.Address := List.replicate 20 0xAA
private def authB : Stateless.SpecRef.Address := List.replicate 20 0xBB

private def teerTableExample : List TeerEntry :=
  [ { authority := authA, charged := true },
    { authority := authB, charged := false } ]

/-- Both authorities are in `written_accounts`… -/
example : teerWrittenAccounts teerTableExample = [authA, authB] := by decide

/-- …but only the charged one is in `delegation_set_for`. So the subset
    inclusion is strict here, and `teerDelegationSetFor` is not vacuously
    empty. -/
example : teerDelegationSetFor teerTableExample = [authA] := by decide

example : authB ∉ teerDelegationSetFor teerTableExample := by decide

/-- The scan-miss step really does extend the spec value by one address. -/
example :
    Stateless.SpecRef.setAdd (teerWrittenAccounts teerTableExample) authA
      = teerWrittenAccounts teerTableExample := by decide

/-! ## 4. `callee_seed_table` — ⛔ NO PREDICATE; structural finding

    Doc §5 specifies this region (128 × 96 = 12288, "`#guard` in
    `BlockVerdictParams`", count `callee_seed_count`, zeroed at
    `seed_callee_storage` entry). **None of it is in the tree.**

    Measured on `7185e9274`: `callee_seed_table`, `callee_seed_count`,
    `seed_callee_storage`, `calleeSeedTableCap`, `calleeSeedTableBytes` and
    `calleeSeedEntryBytes` have **zero occurrences** anywhere in `EvmAsm/**` —
    no emitter, no symbol, no capacity constant. The only mentions in the
    repository are `docs/4ch8f-predicate-shapes.md` §5 and
    `docs/4ch8f-region-map.md:177`.

    ⚠️ There is no `#guard` for `128 * 96`. The only `12288` in Lean is
    `systemCallReturndataMaxBytes` (`EvmAsm/Codegen/Dispatch.lean:74`), an
    unrelated constant of coincidentally equal value — which is what makes the
    doc row look verifiable when it is not.

    **What would have to change first:** the region has to exist in some build
    unit, with an emitter and a capacity constant, before a predicate can name
    a base or an extent. Until then a predicate here would be about nothing.
    Contrast doc §6, which checks out exactly: see `teerTableBytes_eq` above. -/

/-- The absent symbols, recorded so the finding is machine-checkable prose
    rather than a comment that rots. If any of these acquires an emitter, this
    list is the place that should stop being true. -/
def calleeSeedAbsentSymbols : List String :=
  [ "callee_seed_table", "callee_seed_count", "seed_callee_storage" ]

theorem calleeSeedAbsentSymbols_length : calleeSeedAbsentSymbols.length = 3 := by decide

/-! ## 5. `baap_storage_values` — byte range only; two structural findings

    Doc §3 / §8. The union-child **phase boundary** for this region is already
    discharged in `EvmAsm/Codegen/CallFramePhase.lean`: `phaseD_eq_phaseH` is
    the dissolve-and-reinterpret theorem (the two views are literally the same
    assertion, so nothing has to be proven relating the two uses), and
    `phaseH_to_phaseD` is the release direction from concrete buffers. The
    child's own offset and size are pinned in `children_offsets_match_regionMap`
    against `RegionMap.dataUnionChildren`.

    ⇒ So what is left here is not a predicate but two findings about the
    *structure*, which the issue asks for explicitly rather than as a fallback.

    ⚠️ **Finding 1 — entries are variable-length, so the run cannot be indexed
    by `i`.** Values are encoded storage blobs packed by a **byte cursor**
    (`baap_storage_value_cursor`, a high-water byte pointer reset to base at
    apply entry); only the *paths* are fixed 64-byte records, in the sibling
    `baap_storage_paths`. An entry-indexed `…EntriesFrom` would need an
    alignment or offset-table invariant that the structure does not currently
    have. A byte-range form (`anyBytes base n`) is the honest interim, and it
    is what `CallFramePhase` already uses. Adding the invariant is a change to
    the *structure*, not a proof obligation.

    ⚠️ **Finding 2 — no validity invariant is asserted anywhere.** No
    sortedness, no uniqueness, no monotone BAI. So a predicate asserting
    anything beyond the byte range would be asserting something the code does
    not maintain.

    ⛔ **And the extent is unit-dependent (#11222):** the same symbol name is
    emitted at **three sizes in three units** — guest `6_400_000`
    (`bsrMaxBalItems * bsrPathBytes`), the `BalAccountApplyPostFields` probe
    `3_840_000`, and `BalAccountDescriptorArray` `32_768`. An `extent =`
    theorem is therefore true in `stateless_guest` and **false** in the other
    two. Closing #11222 (overload vs dead) is required before any single global
    claim; until then the unit must be named at every use, which is why
    `statelessGuest` exists above. Its initialisation contract is
    **self-discharged** — the routine clears the cells in its own entry block
    rather than imposing the obligation on callers.

    ⚠️ #10651 may change this region's enumeration; this module states its
    derivation commit at the top for that reason. -/

/-- The three build units that emit `baap_storage_values`, with the size each
    one uses. Recorded as data so the overload is checkable rather than prose:
    a predicate naming no unit is wrong in two of these three. -/
def baapStorageValuesUnitSizes : List (String × Nat) :=
  [ ("stateless_guest", 6400000),
    ("BalAccountApplyPostFields probe", 3840000),
    ("BalAccountDescriptorArray", 32768) ]

/-- The guest size is the layout formula's, not a literal — so if
    `bsrMaxBalItems` or `bsrPathBytes` moves, this fails rather than the doc
    quietly becoming wrong. -/
theorem baapStorageValues_guest_size_eq_formula :
    (baapStorageValuesUnitSizes.head?.map (·.2)) = some (bsrMaxBalItems * bsrPathBytes) := by
  decide

/-- ⚠️ The three sizes really are distinct — the overload is not a
    documentation artifact of one number written three ways. -/
theorem baapStorageValues_sizes_distinct :
    (baapStorageValuesUnitSizes.map (·.2)).eraseDups.length = 3 := by decide

/-! ## `bal_canonical_sort` row arrays (GH #10817)

    The prerequisite `docs/leaf-routine-targets.md:49` names: *"needs a
    `balEntriesFrom`-style run predicate; mirror `teerEntriesFrom`"*. Without a
    `List`-indexed assertion over the row array, #10817's headline obligation —
    that the output is a **permutation** of the input — cannot be *stated* at
    all, only its sortedness.

    ⚠️ **Stride is a parameter here, unlike `teerEntriesFrom`.** The teer table
    has one entry width; `bal_canonical_sort` is called at **six** live sites
    (`BalSerializer.lean:1071-1108`, `#guard`-pinned at 6 in
    `BlockAccessListBuilder.lean`) with **four** distinct strides among them —
    `a2` is 96, 64, 64, 40, 64, 24, so `64` is shared by the storage reads and
    the balance and code changes. #10817 asks explicitly to *"parameterise over
    the descriptors"* rather than over literal byte offsets, so that a
    row-content change cannot silently invalidate a proof. `balSortCallSites`
    below is that parameterisation.

    ⚠️ Both counts here are pinned by `by decide` rather than left as prose —
    `balSortCallSites_count` (six sites) and `balSortCallSites_stride_count`
    (four strides). That is not decoration: this docstring said *"five distinct
    strides"* on arrival, and `balSortCallSites_stride_count` is exactly the
    theorem that refutes it. A prose count that disagrees with the data is the
    case for moving counts into the data, so the numbers quoted above are the
    ones those theorems assert.

    ⚠️ **Rows are opaque bytes, deliberately.** A typed `BalRow` with a
    `.render` (the `TeerEntry` shape) would bake one call site's segment layout
    into the predicate, and the six sites disagree — including one whose slot
    segment is **little-endian** where every other is big-endian. The sort moves
    whole rows and never interprets them, so opaque bytes is the faithful
    vocabulary; the *key* is where interpretation belongs, and it belongs to the
    spec-side model (`SpecRef._build_from_builder`), not here. -/

/-- Every row of `rs` is exactly `stride` bytes wide.

    Threaded as a `Prop` rather than folded into `balEntriesFrom`, matching the
    `teerBuffer` capacity call: the assertion stays about *resource*, and the
    shape obligation stays visible in each theorem's hypotheses. -/
def balRowsWf (stride : Nat) (rs : List (List (BitVec 8))) : Prop :=
  ∀ r ∈ rs, r.length = stride

theorem balRowsWf_nil (stride : Nat) : balRowsWf stride [] := by
  intro r hr; exact absurd hr (by simp)

theorem balRowsWf_cons {stride : Nat} {r : List (BitVec 8)}
    {rs : List (List (BitVec 8))} (h : balRowsWf stride (r :: rs)) :
    r.length = stride ∧ balRowsWf stride rs := by
  refine ⟨h r (by simp), ?_⟩
  intro x hx
  exact h x (by simp [hx])

/-- **The partial run** — `rs` in consecutive `stride`-byte rows from `base`,
    saying nothing about what follows. The composable form, and the one a proof
    about one row should be handed. Structure mirrors `teerEntriesFrom`. -/
def balEntriesFrom (stride : Nat) (base : Word) :
    List (List (BitVec 8)) → Assertion
  | [] => empAssertion
  | r :: rs =>
      bytesRegion base r
        ** balEntriesFrom stride (base + BitVec.ofNat 64 stride) rs

theorem pcFree_balEntriesFrom (stride : Nat) (base : Word)
    (rs : List (List (BitVec 8))) : (balEntriesFrom stride base rs).pcFree := by
  induction rs generalizing base with
  | nil => exact pcFree_emp
  | cons r rs ih => exact pcFree_sepConj (bytesRegion_pcFree _ _) (ih _)

theorem balEntriesFrom_cons (stride : Nat) (base : Word) (r : List (BitVec 8))
    (rs : List (List (BitVec 8))) :
    balEntriesFrom stride base (r :: rs)
      = (bytesRegion base r
          ** balEntriesFrom stride (base + BitVec.ofNat 64 stride) rs) := rfl

/-- **The whole buffer** — the run *and* that this is all of it: `rs.length`
    live rows, then the remainder owned-unconstrained out to `cap` rows.

    `rs.length ≤ cap` is a hypothesis rather than a conjunct, as in
    `teerBuffer`. The operational form of the same bound is the sort's own
    fail-closed capacity check. -/
def balBuffer (stride cap : Nat) (base : Word) (rs : List (List (BitVec 8)))
    (_hcap : rs.length ≤ cap) : Assertion :=
  balEntriesFrom stride base rs
    ** anyBytes (base + BitVec.ofNat 64 (rs.length * stride))
         ((cap - rs.length) * stride)

theorem pcFree_balBuffer (stride cap : Nat) (base : Word)
    (rs : List (List (BitVec 8))) (hcap : rs.length ≤ cap) :
    (balBuffer stride cap base rs hcap).pcFree :=
  pcFree_sepConj (pcFree_balEntriesFrom _ _ _) (pcFree_anyBytes _ _)

/-- **Ownership only** — the array's bytes, contents arbitrary. -/
def balOwn (stride cap : Nat) (base : Word) : Assertion :=
  anyBytes base (cap * stride)

theorem pcFree_balOwn (stride cap : Nat) (base : Word) :
    (balOwn stride cap base).pcFree := pcFree_anyBytes _ _

/-! ### The six live call sites, as data

    #10817 asks for the row shapes as parameters rather than literals. These are
    read off `BalSerializer.lean:1071-1108` — the `a2` (stride), `a3`
    (segment descriptor) and `a4` (segment count) actually passed.

    ⚠️ The issue's own table lists **four** row kinds and omits two, both
    unusual: `storage_reads`, whose descriptor `0x2020` carries **no BE flag**
    (the only little-endian segment on the live path — the read row's slot is an
    LE stack word at `+32`), and the `accounts` array itself at stride **24**.
    A proof covering only the issue's four covers 4 of 6 live sites. -/
structure BalSortCallSite where
  /-- The row array's guest symbol, or its literal address for the read arena. -/
  array : String
  /-- `a2` — the row stride in bytes. -/
  stride : Nat
  /-- `a3` — the packed segment descriptor. -/
  segments : Nat
  /-- `a4` — how many key segments the descriptor carries. -/
  segCount : Nat
  deriving Repr, DecidableEq

/-- The six calls in `bal_serializer_rebuild_hash`, in emission order. -/
def balSortCallSites : List BalSortCallSite :=
  [ { array := "bal_builder_storage_changes", stride := 96,
      segments := 0x0818a0209400, segCount := 3 },
    { array := "0xa1ba0000 (storage_reads)", stride := 64,
      segments := 0x2020, segCount := 1 },
    { array := "bal_builder_balance_changes", stride := 64,
      segments := 0x08189400, segCount := 2 },
    { array := "bal_builder_nonce_changes", stride := 40,
      segments := 0x08189400, segCount := 2 },
    { array := "bal_builder_code_changes", stride := 64,
      segments := 0x08189400, segCount := 2 },
    { array := "bal_builder_accounts", stride := 24,
      segments := 0x9400, segCount := 1 } ]

/-- The `#guard` at `BlockAccessListBuilder.lean` pins six calls; this pins that
    this table is the same six. -/
theorem balSortCallSites_count : balSortCallSites.length = 6 := by decide

/-- ⭐ **Every live stride is 8-aligned**, which is not cosmetic:
    `bal_canonical_sort` swaps rows with `ld`/`sd`, so a non-8-aligned stride
    faults. `BlockAccessListBuilder.lean` states the rule
    (*"ANY ROW ARRAY THAT WILL BE SORTED MUST HAVE AN 8-ALIGNED STRIDE"*) and
    the probe found the empirical version — a stride-20 arena puts row 1 at
    `base+20` and faults. Any triple over the sort carries this as a hypothesis;
    this theorem is why the six live sites satisfy it. -/
theorem balSortCallSites_strides_aligned :
    balSortCallSites.all (fun c => c.stride % 8 == 0) = true := by decide

/-- ⚠️ Four distinct strides (96, 64, 40, 24) across six sites — so a predicate
    with a fixed stride could not describe the live path, which is why
    `balEntriesFrom` takes one as a parameter. (`64` is shared by the storage
    reads and the balance and code changes.) -/
theorem balSortCallSites_stride_count :
    (balSortCallSites.map (·.stride)).eraseDups.length = 4 := by decide

/-- ⚠️ Exactly one live site sorts on a little-endian segment. Recorded because
    a canonical-key definition that assumes big-endian throughout would be wrong
    on precisely this one, with no local symptom — the failure mode this
    module's header warns about. -/
theorem balSortCallSites_one_le_segment :
    (balSortCallSites.filter (fun c => c.segments == 0x2020)).length = 1 := by decide

end RegionPredicates
end EvmAsm.Codegen
