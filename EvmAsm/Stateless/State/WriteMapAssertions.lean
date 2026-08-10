/-
  EvmAsm.Stateless.State.WriteMapAssertions

  Separation-logic assertions for the guest's **spec-shaped write maps** (GH #11571).

  The guest has converged on `state_tracker.py`'s two-container model (#11326 item 3,
  #11329): a block-level map and a per-transaction map for account writes, and the
  same pair for storage writes. Those arenas had **no `Assertion` vocabulary** — the
  predicate inventory covered the *legacy* append-only logs (`storageLogIs`,
  `Evm64/StorageAssertions.lean`) and the byte-level regions, so the containers the
  whole convergence is moving *toward* were describable only as raw bytes.

  Defining them now is a sequencing decision, per #11655: the attribution cluster
  (#11648–#11653) has closed, so the shapes are final, and a stated predicate is what
  freezes a shape and converts later drift into a build failure. #11654 is the
  cautionary case — SLOAD's 45-theorem spec was deleted the day its container retired,
  because the spec was written against the container rather than against a predicate.

  ## Why this is core and not beside the maps

  The maps themselves live in `Codegen/Programs/AccountWriteMap.lean` and
  `StorageWriteMap.lean`, and `Codegen/RegionPredicates.lean` has the run-predicate
  pattern (`teerEntriesFrom`) that #11571 asks these to follow. **None of that can be
  imported here.** `check-layering` L1 makes `EvmAsm/Codegen` a pure sink: the point
  of these predicates is to be consumed by *core-side* bridges against
  `SpecRef/StateTracker.lean`, so they must live in core, which may not import
  Codegen. `Stateless/Crypto/FieldAssertions.lean` records the identical decision for
  the crypto field predicates and is the precedent followed here.

  Consequence: `teerEntriesFrom`'s shape is **mirrored, not reused**, and the row
  layouts below are *restated* from the emitted maps rather than shared with them.
  That restatement is the thing a later routine triple pins; until such a triple
  exists, a layout drift in `Codegen` would not be caught here. Stated plainly
  because it is the one weakness of a core-side predicate over an emitted structure.

  ## Layout provenance (read from the emitted maps, 2026-08-10)

  **Account rows** — `AccountWriteMap.lean:207`, stride **128**:

      { addr_BE20@0, padding@20..31, balance@32, nonce@64, optionalState@72,
        codePtr@80, codeLen@88, execFlags@96, reserved@104, validMask@112,
        reserved@120 }

  Bases: `ACCOUNT_WRITES_AREA` (block) and `TX_ACCOUNT_WRITES_AREA` (tx),
  `Stateless/MemoryLayout.lean`. `execFlags@96` value **2 = live**; zero means
  present-dead or deleted (`AccountWriteMap.lean:177`). ⚠️ That flag is why a row
  list is not by itself a map: see `AccountWriteRow.live` and the note on
  `accountWriteRowsFrom`.

  **Storage rows** — `StorageWriteMap.lean:357`, stride **128**:
  `(rowAddress@0 : 32 B, slotKey@32 : 32 B, value@64 : 32 B, baseline@96 : 32 B)`,
  where `baseline` is the slot's value at the start of the transaction, captured on
  append so `block_access_lists.py`'s net-zero-write exclusion can be computed.

  All multi-byte scalar fields are accessed by the guest with `sd`/`ld`, so they are
  modelled with `↦ₘ` (little-endian, 8-byte aligned) rather than by byte-splatting.
  Every offset used here is a multiple of 8, and both bases are 8-aligned, so the
  alignment requirement of `memIs` is met by construction.

  ## ⚠️ A shape divergence the abstraction has to cross

  `SpecRef`'s storage side is **nested** — `BlockState.storageWrites :
  List (Address × List (Bytes32 × U256))`, mirroring Python's
  `Dict[Address, Dict[Bytes32, U256]]` — while the guest's rows are **flat**, one row
  per `(address, slot)` pair. #11571's proposed signature is the flat one, which is
  right for the guest, so the correspondence needs a **group-by**, not a rename.
  `groupByAddress` below is that function and `storageRowsAbstract` is the hook a
  `StateTracker` correspondence proof hangs from.

  ## Scope

  Vocabulary only, per #11571's non-goals: no routine triples (`account_writes_upsert`
  / `_lookup`, commit/reset walkers are follow-ons), and the **undo journals** are
  deliberately excluded — their counterpart is `restore_tx_state`'s dict-copy
  semantics and the theorem shape differs (#11572).
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Stateless.MemoryLayout
import EvmAsm.Stateless.SpecRef.StateTracker

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Row strides and field offsets

    Named rather than inlined so a caller cites a symbol and a later drift is a
    one-line change, per the #11571 discipline of parameterising the stride instead
    of hardcoding it at every use. -/

/-- Bytes per `account_writes` / `tx_account_writes` row (`AccountWriteMap.lean:172`). -/
def accountWriteRowBytes : Nat := 128

/-- Bytes per `storage_writes` row (`StorageWriteMap.lean`, the `* 128` capacity
    guards). -/
def storageWriteRowBytes : Nat := 128

/-- `execFlags@96` value marking a row **live**; zero means present-dead or deleted
    (`AccountWriteMap.lean:177`). A value, not a bit index — it is the emitted `andi`
    immediate. -/
def accountWriteLiveFlag : Nat := 2

/-! ## Account write rows -/

/-- One `account_writes` row, as the guest lays it out.

    The 20-byte address key and the 32-byte big-endian balance are byte strings; the
    remaining fields are `sd`/`ld` words. `padding@20..31` and the two reserved words
    are deliberately absent: a row predicate should not claim what the writers do not
    establish, and both `.Lawr_store` and `.Lawb_store` leave them unconstrained. -/
structure AccountWriteRow where
  /-- 20-byte big-endian address key at `+0`, identical to the builder's address
      segment (`AccountWriteMap.lean:208`). -/
  address : List (BitVec 8)
  /-- 32-byte big-endian balance at `+32`. -/
  balance : List (BitVec 8)
  /-- u64 nonce at `+64`. -/
  nonce : Word
  /-- `optionalState` word at `+72` — the `Optional[Account]` discriminant, which is
      what makes a deleted account representable at all. -/
  optionalState : Word
  /-- code pointer at `+80`. -/
  codePtr : Word
  /-- code length at `+88`. -/
  codeLen : Word
  /-- `execFlags` at `+96`; `accountWriteLiveFlag` is the live bit. -/
  execFlags : Word
  /-- components mask at `+112`, gating whether `execFlags` is stored or copied. -/
  validMask : Word

namespace AccountWriteRow

/-- Well-formedness: the key is 20 bytes and the balance 32, exactly as the writers
    store them. Mirrors `TeerEntry.wf`'s role — a length side condition the render
    lemma needs, kept out of the predicate so it can be assumed once per caller. -/
def wf (r : AccountWriteRow) : Prop :=
  r.address.length = 20 ∧ r.balance.length = 32

/-- Is this row live? Zero `execFlags & 2` means present-dead or deleted, so a row
    being *present* is not the same as its address being *in* the map. -/
def live (r : AccountWriteRow) : Prop :=
  r.execFlags &&& BitVec.ofNat 64 accountWriteLiveFlag ≠ 0

end AccountWriteRow

/-- One account row at `base`, field by field.

    Offsets are the emitted ones; every scalar is a `↦ₘ` word because the guest reads
    and writes them with `ld`/`sd`. Unmodelled bytes (`+20..31`, `+104`, `+120`) are
    simply not mentioned, so this composes with whatever a caller holds for them. -/
def accountWriteRowIs (base : Word) (r : AccountWriteRow) : Assertion :=
  bytesRegion base r.address
    ** bytesRegion (base + 32) r.balance
    ** ((base + 64) ↦ₘ r.nonce)
    ** ((base + 72) ↦ₘ r.optionalState)
    ** ((base + 80) ↦ₘ r.codePtr)
    ** ((base + 88) ↦ₘ r.codeLen)
    ** ((base + 96) ↦ₘ r.execFlags)
    ** ((base + 112) ↦ₘ r.validMask)

/-- **The partial run** — `rs` in consecutive rows from `base`, saying nothing about
    what follows. The composable form, and the one a routine touching a single row
    should be handed.

    Structure mirrors `Codegen/RegionPredicates.lean`'s `teerEntriesFrom` (itself
    copied from `evmStackIs`): base as a parameter, contents as a `List`, recursion
    with `**` and a stride step, `empAssertion` at nil.

    ⚠️ **This is a row list, not a map.** Rows carry a live flag and the arena is
    append-with-scan, so two rows may share an address (the later one winning) and a
    row may be dead. `AccountWriteRowsMap` below is the well-formedness that makes the
    list denote a finite map; keeping them separate is deliberate, because a routine
    mid-upsert holds the run *without* the map property. -/
def accountWriteRowsFrom (base : Word) : List AccountWriteRow → Assertion
  | [] => empAssertion
  | r :: rs =>
      accountWriteRowIs base r
        ** accountWriteRowsFrom (base + BitVec.ofNat 64 accountWriteRowBytes) rs

/-- Block-level `account_writes`, at `ACCOUNT_WRITES_AREA`. Filled only by
    `account_writes_incorporate_tx`, mirroring `BlockState.accountWrites`. -/
def accountWritesMapIs (rs : List AccountWriteRow) : Assertion :=
  accountWriteRowsFrom ACCOUNT_WRITES_AREA rs

/-- Per-transaction `account_writes`, at `TX_ACCOUNT_WRITES_AREA`. The target of
    `account_write_record`, mirroring `TransactionState.accountWrites`. -/
def txAccountWritesMapIs (rs : List AccountWriteRow) : Assertion :=
  accountWriteRowsFrom TX_ACCOUNT_WRITES_AREA rs

/-! ## Storage write rows -/

/-- One `storage_writes` row: the outer address key, the inner slot key, the value,
    and the pre-transaction baseline captured on append. All four are 32-byte
    big-endian buffers. -/
structure StorageWriteRow where
  /-- 32-byte outer `Address` key at `+0`, keyed exactly as `storage_read_record`
      keys its reads — so the same slot in two contracts is two rows. -/
  rowAddress : List (BitVec 8)
  /-- 32-byte inner `Bytes32` slot key at `+32`. -/
  slotKey : List (BitVec 8)
  /-- 32-byte `U256` value at `+64`. -/
  value : List (BitVec 8)
  /-- 32-byte pre-transaction baseline at `+96`. Zero *is* the spec's answer for a
      slot with no prior value (`_get_pre_tx_storage` "Returns 0 if not set"), so a
      zero baseline is not a sentinel. -/
  baseline : List (BitVec 8)

namespace StorageWriteRow

/-- All four fields are exactly 32 bytes. -/
def wf (r : StorageWriteRow) : Prop :=
  r.rowAddress.length = 32 ∧ r.slotKey.length = 32
    ∧ r.value.length = 32 ∧ r.baseline.length = 32

/-- The `(address, slot)` pair this row keys on. Flat, matching the guest. -/
def key (r : StorageWriteRow) : List (BitVec 8) × List (BitVec 8) :=
  (r.rowAddress, r.slotKey)

end StorageWriteRow

/-- One storage row at `base`, field by field. -/
def storageWriteRowIs (base : Word) (r : StorageWriteRow) : Assertion :=
  bytesRegion base r.rowAddress
    ** bytesRegion (base + 32) r.slotKey
    ** bytesRegion (base + 64) r.value
    ** bytesRegion (base + 96) r.baseline

/-- **The partial run** for storage rows, same shape as `accountWriteRowsFrom`. -/
def storageWriteRowsFrom (base : Word) : List StorageWriteRow → Assertion
  | [] => empAssertion
  | r :: rs =>
      storageWriteRowIs base r
        ** storageWriteRowsFrom (base + BitVec.ofNat 64 storageWriteRowBytes) rs

/-- `storage_writes` at a caller-supplied base.

    Unlike the account maps this takes the base as a parameter rather than pinning
    `MemoryLayout` constants: the storage arenas' bases are computed in
    `Codegen/Programs/StorageWriteMap.lean` (`storageWritesBlockBase` /
    `storageWritesTxBase`) and are **not** exported as `Stateless/MemoryLayout`
    definitions the way the account areas are, so pinning them here would duplicate a
    literal that core cannot see. A caller supplies the base it owns. -/
def storageWritesMapIs (base : Word) (rs : List StorageWriteRow) : Assertion :=
  storageWriteRowsFrom base rs

/-! ## `pcFree`

    Every predicate here is program-counter-free, which is what lets it be framed
    across a call. Same obligation `pcFree_teerEntriesFrom` discharges for the
    Codegen-side run. -/

theorem pcFree_accountWriteRowIs (base : Word) (r : AccountWriteRow) :
    (accountWriteRowIs base r).pcFree := by
  unfold accountWriteRowIs
  repeat' first
    | apply pcFree_sepConj
    | exact bytesRegion_pcFree _ _
    | exact pcFree_memIs

theorem pcFree_accountWriteRowsFrom (base : Word) (rs : List AccountWriteRow) :
    (accountWriteRowsFrom base rs).pcFree := by
  induction rs generalizing base with
  | nil => exact pcFree_emp
  | cons r rs ih => exact pcFree_sepConj (pcFree_accountWriteRowIs _ _) (ih _)

theorem pcFree_storageWriteRowIs (base : Word) (r : StorageWriteRow) :
    (storageWriteRowIs base r).pcFree := by
  unfold storageWriteRowIs
  repeat' first
    | apply pcFree_sepConj
    | exact bytesRegion_pcFree _ _

theorem pcFree_storageWriteRowsFrom (base : Word) (rs : List StorageWriteRow) :
    (storageWriteRowsFrom base rs).pcFree := by
  induction rs generalizing base with
  | nil => exact pcFree_emp
  | cons r rs ih => exact pcFree_sepConj (pcFree_storageWriteRowIs _ _) (ih _)

/-! ## Structural lemmas

    `cons` and `snoc`. The `snoc` direction is the one an append-at-the-tail upsert
    needs and is not definitional, exactly as `DecodeChain.snoc` was not — the
    recursion is from the front while the writer extends at the back. -/

theorem accountWriteRowsFrom_cons (base : Word) (r : AccountWriteRow)
    (rs : List AccountWriteRow) :
    accountWriteRowsFrom base (r :: rs)
      = (accountWriteRowIs base r
          ** accountWriteRowsFrom (base + BitVec.ofNat 64 accountWriteRowBytes) rs) :=
  rfl

theorem storageWriteRowsFrom_cons (base : Word) (r : StorageWriteRow)
    (rs : List StorageWriteRow) :
    storageWriteRowsFrom base (r :: rs)
      = (storageWriteRowIs base r
          ** storageWriteRowsFrom (base + BitVec.ofNat 64 storageWriteRowBytes) rs) :=
  rfl

/-! ## The map abstraction

    #11571 item 2: state, per predicate, that the entry list viewed as a finite map is
    well-formed — no duplicate keys under the container's insert discipline. This is
    the hook a `SpecRef/StateTracker` correspondence proof hangs from.

    ⚠️ Stated as a **precondition-shaped predicate over the list**, not proved here. The
    guest's arena is append-with-scan (`.Lawr_scan`), so uniqueness is a property of
    the *writer*.

    ⭐ **Update (#11921 row 1): the writer half is now a theorem.**
    `State/AccountWriteUpsert.lean` models `account_write_record`'s upsert and proves
    `accountWriteUpsert_rowsMap` — this predicate is preserved by the writer, from the
    empty arena up. It cannot be cited *from* this module (that one imports this one),
    which is why the clause stays a hypothesis in the definition; callers should discharge
    it with that theorem rather than assume it.

    Still open, and deliberately so: the model↔machine step, i.e. that the emitted
    `.Lawr_scan`/`.Lawr_append`/`.Lawr_store` sequence implements the model. That needs an
    SAsm transcription of the routine, which does not exist. Same discipline as
    [[write-predicates-to-survive-movement]]. -/

/-- The live rows of an account run, in order. Dead rows are present in memory and
    absent from the map. -/
def liveAccountRows (rs : List AccountWriteRow) : List AccountWriteRow :=
  rs.filter (fun r => decide (r.execFlags &&& BitVec.ofNat 64 accountWriteLiveFlag ≠ 0))

/-- **The map property for account rows**: every row is well-formed, and no two live
    rows share an address key. Under it, `liveAccountRows` denotes a finite
    `Address ⇀ Optional[Account]` — the shape of `BlockState.accountWrites` and
    `TransactionState.accountWrites` (`SpecRef/StateTracker.lean:90,110`). -/
def AccountWriteRowsMap (rs : List AccountWriteRow) : Prop :=
  (∀ r ∈ rs, r.wf)
    ∧ ((liveAccountRows rs).map AccountWriteRow.address).Nodup

/-- **The map property for storage rows**: every row is well-formed and no two rows
    share an `(address, slot)` pair. -/
def StorageWriteRowsMap (rs : List StorageWriteRow) : Prop :=
  (∀ r ∈ rs, r.wf) ∧ (rs.map StorageWriteRow.key).Nodup

/-! ### Crossing the flat/nested divergence

    `SpecRef` stores storage writes nested by address; the guest stores flat rows.
    Neither is wrong — they are different encodings of the same dictionary — so the
    abstraction is a group-by rather than a coercion. -/

/-- Group flat rows by their outer address, preserving first-appearance order of
    addresses and, within an address, row order. The shape of
    `List (Address × List (Bytes32 × U256))` that `SpecRef` uses. -/
def groupByAddress (rs : List StorageWriteRow) :
    List (List (BitVec 8) × List (List (BitVec 8) × List (BitVec 8))) :=
  rs.foldl
    (fun acc r =>
      if acc.any (fun p => p.1 = r.rowAddress) then
        acc.map (fun p =>
          if p.1 = r.rowAddress then (p.1, p.2 ++ [(r.slotKey, r.value)]) else p)
      else acc ++ [(r.rowAddress, [(r.slotKey, r.value)])])
    []

/-- ⭐ **The abstraction hook.** Under the map property, the flat guest rows and the
    nested `SpecRef` shape agree: grouping the rows by address yields one group per
    distinct address, and every `(slot, value)` pair of the flat list appears in
    exactly one group.

    Stated, not proved — the statement is the deliverable #11571 asks for ("state the
    intended abstraction lemma per predicate"), and discharging it wants the upsert
    routine's uniqueness fact, which is a follow-on. Naming it here means the
    `StateTracker` correspondence proof has a single named obligation to consume
    rather than re-deriving the grouping inline. -/
def storageRowsAbstract (rs : List StorageWriteRow) : Prop :=
  StorageWriteRowsMap rs →
    (((groupByAddress rs).map Prod.fst).Nodup
      ∧ (groupByAddress rs).foldl (fun n p => n + p.2.length) 0 = rs.length)

/-! ## Non-vacuity, kernel-checked

    A predicate nobody has instantiated is indistinguishable from one that cannot be.
    These are concrete witnesses plus the matching negative controls, in the style of
    `Progress/Routines.lean`'s `crossVerdictOk` control: the point is not that the
    definitions elaborate, but that they *separate* the cases they claim to. -/

section NonVacuity

/-- A live, well-formed account row. -/
private def sampleRowA : AccountWriteRow :=
  { address := List.replicate 19 0 ++ [1]
    balance := List.replicate 32 0
    nonce := 7
    optionalState := 1
    codePtr := 0
    codeLen := 0
    execFlags := BitVec.ofNat 64 accountWriteLiveFlag
    validMask := 0 }

/-- A second live row at a **different** address. -/
private def sampleRowB : AccountWriteRow :=
  { sampleRowA with address := List.replicate 19 0 ++ [2] }

/-- A **dead** row (zero `execFlags`) sharing `sampleRowA`'s address. -/
private def sampleRowDead : AccountWriteRow :=
  { sampleRowA with execFlags := 0 }

/-- `wf` is satisfiable: the sample row has a 20-byte key and a 32-byte balance. -/
example : sampleRowA.wf := by
  unfold AccountWriteRow.wf sampleRowA; simp

/-- `live` separates the two: the flagged row is live, the zero-flag row is not. So
    `execFlags` is load-bearing rather than decorative. -/
example : sampleRowA.live ∧ ¬ sampleRowDead.live := by
  unfold AccountWriteRow.live sampleRowA sampleRowDead accountWriteLiveFlag
  refine ⟨?_, ?_⟩ <;> decide

/-- ⭐ The map property holds on two live rows with distinct addresses. -/
example : AccountWriteRowsMap [sampleRowA, sampleRowB] := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold AccountWriteRow.wf sampleRowA; simp
    · unfold AccountWriteRow.wf sampleRowB sampleRowA; simp
  · unfold liveAccountRows sampleRowA sampleRowB accountWriteLiveFlag
    decide

/-- ⭐ **Negative control.** The map property FAILS on two live rows sharing an
    address — so `Nodup` is doing real work and the predicate is not trivially true.
    This is the check that distinguishes a map from a row list. -/
example : ¬ AccountWriteRowsMap [sampleRowA, sampleRowA] := by
  intro h
  have := h.2
  unfold liveAccountRows sampleRowA accountWriteLiveFlag at this
  revert this
  decide

/-- ⭐ **The dead-row case, which is the reason `liveAccountRows` exists.** Two rows
    sharing an address are fine when one is dead — the map is over *live* rows, and an
    append-with-scan arena legitimately retains superseded rows. A predicate that
    demanded `Nodup` over all rows would reject reachable states. -/
example : AccountWriteRowsMap [sampleRowDead, sampleRowA] := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold AccountWriteRow.wf sampleRowDead sampleRowA; simp
    · unfold AccountWriteRow.wf sampleRowA; simp
  · unfold liveAccountRows sampleRowDead sampleRowA accountWriteLiveFlag
    decide

/-- Two storage rows: same contract, two different slots. -/
private def sampleStoreA : StorageWriteRow :=
  { rowAddress := List.replicate 32 1
    slotKey := List.replicate 31 0 ++ [1]
    value := List.replicate 31 0 ++ [9]
    baseline := List.replicate 32 0 }

private def sampleStoreB : StorageWriteRow :=
  { sampleStoreA with slotKey := List.replicate 31 0 ++ [2] }

/-- A row in a **different** contract at the same slot as `sampleStoreA` — the case
    the docstring calls out as two entries, not one. -/
private def sampleStoreC : StorageWriteRow :=
  { sampleStoreA with rowAddress := List.replicate 32 2 }

/-- The storage map property holds across distinct `(address, slot)` pairs, including
    the same slot in two contracts. -/
example : StorageWriteRowsMap [sampleStoreA, sampleStoreB, sampleStoreC] := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp [StorageWriteRow.wf, sampleStoreA, sampleStoreB, sampleStoreC]
  · unfold StorageWriteRow.key sampleStoreA sampleStoreB sampleStoreC
    decide

/-- **Negative control** for the storage map property: the identical `(address, slot)`
    twice is rejected. -/
example : ¬ StorageWriteRowsMap [sampleStoreA, sampleStoreA] := by
  intro h
  have := h.2
  unfold StorageWriteRow.key sampleStoreA at this
  revert this
  decide

/-- ⭐ **The flat/nested divergence, concretely.** Three flat rows over two contracts
    group into exactly two address buckets — 2, not 3 — which is the whole content of
    the group-by and the reason a rename would have been wrong. -/
example : (groupByAddress [sampleStoreA, sampleStoreB, sampleStoreC]).length = 2 := by
  unfold groupByAddress sampleStoreA sampleStoreB sampleStoreC
  decide

/-- And no bucket is lost or duplicated: the flattened count returns the row count. -/
example :
    (groupByAddress [sampleStoreA, sampleStoreB, sampleStoreC]).foldl
      (fun n p => n + p.2.length) 0 = 3 := by
  unfold groupByAddress sampleStoreA sampleStoreB sampleStoreC
  decide

end NonVacuity

end EvmAsm.Stateless
