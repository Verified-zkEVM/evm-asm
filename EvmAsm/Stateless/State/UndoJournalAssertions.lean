/-
  EvmAsm.Stateless.State.UndoJournalAssertions

  Separation-logic assertions for the guest's **rollback undo journals** (GH #11572).

  `restore_tx_state` (`state_tracker.py:809-826`; port `SpecRef/StateTracker.lean`
  `copyTxState`/`restoreTxState`) restores the write dicts **by copy**. The guest
  cannot afford a dict copy at capacity × call depth, so it implements the same effect
  as an undo journal: push pre-values on overwrite, replay in reverse on revert.

  That machinery was **entirely unmodeled** — no predicate, no list-level model — and
  rollback is where soundness bugs have clustered: #11189 (undo journal fail-OPEN on
  overflow), #11198 (no capacity guard), #11078 (auth OOG applies instead of rolling
  back), #11001 (reverting child leaves caller short). Each is invisible to
  routine-local proofs until the journal has a predicate and revert has a statement.

  ## ⚠️ The two journals are NOT the same shape, and the constants have MOVED AGAIN

  #11572 was already corrected once (2026-08-08) because its first numbers would have
  produced a *wrong* predicate rather than an imprecise one. **Both corrected numbers
  are now stale too**, measured against the tree on 2026-08-10:

  | journal | #11572 (corrected) | actual |
  |---|---|---|
  | storage undo capacity | 32768, `× 160 = 0x500000` | **167652**, `× 160 = 0x1994e80` |
  | account undo capacity | `txAccountWritesCapacity` = 16384 | **`accountWritesUndoCapacity` = 163840** |

  The account one matters most: `Codegen/Programs/AccountWriteUndo.lean:29` now says in
  as many words that the journal bound is *"no longer the same constant as
  `txAccountWritesCapacity`"*, and `:61` explains why — the journal is bounded by
  write **events**, and repeated updates to one key add events without adding map
  rows. Taking the issue's instruction literally would under-bound the account journal
  by 10×, which is exactly the failure mode its own correction note warns about.

  Values used here are therefore read from the tree, not from the issue:

  * **storage** — `STORAGE_WRITES_UNDO_AREA`, stride **160**, capacity **167652**
    (`MemoryLayout.lean:356`, `StorageWriteMap.lean:123`; gas-derived:
    `floor((TX_MAX_GAS_LIMIT − TX_BASE) / 100)`);
  * **account** — `ACCOUNT_WRITES_UNDO_AREA`, stride **128**, capacity **163840**
    (`MemoryLayout.lean:450`, `AccountWriteUndo.lean:52`; covers the 161204
    account-write-EVENT bound of #11770).

  ## Layouts (from core `MemoryLayout.lean`, not from Codegen)

  Storage, 160 B (`MemoryLayout.lean:336-341`):

      +0  entryIndex (8 B) · +8 wasAbsent (8 B) · +16 pad (16 B)
      +32 payload: prevValue (32 B) when wasAbsent = 0
                   full map row (128 B) when wasAbsent = 2

  `wasAbsent` is a field, not a sentinel, because **zero is a legitimate stored
  value**: restoring an appended key by writing zero would invent a written-zero slot
  where the spec has no key. Code 2 is the `destroy_storage` drop, journalling the full
  row so a later append reusing the parked tail cannot corrupt fail-restore.

  Account, 128 B (`MemoryLayout.lean:446-455`):

      +0 entryIndex (8 B) · +8 wasAbsent (8 B) · +16 prevNonce (8 B)
      +24 prevPresent (8 B) · +32 prevBalance (32 B) · +64 prevCodeHash (32 B)
      +96 pad (32 B)

  ## Why stride is a parameter

  #11572 is explicit that a *shared shape* is wrong — the schemas rhyme
  (`entryIndex@0`, `wasAbsent@8`, payload) but 160 ≠ 128. So the run predicate takes
  the stride, following `Codegen/RegionPredicates.lean:718`'s `balEntriesFrom
  (stride) (base)` pattern (mirrored, not imported — same core-side layering
  constraint as `WriteMapAssertions.lean`, see its header).

  ## Scope

  Predicates, cursor cell, well-formedness (**including the capacity bound, so
  #11198's guard is a precondition rather than a hope**), and the *statement* of the
  replay theorem. No routine triples, and the replay theorem is stated not proved —
  discharging it needs the push/replay walkers' triples, which do not exist.
-/

import EvmAsm.Stateless.State.WriteMapAssertions

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-! ## Strides and capacities

    ⚠️ These duplicate constants defined under `Codegen` (`StorageWriteMap.lean:123`,
    `AccountWriteUndo.lean:52`) because core may not import Codegen. The duplication is
    the accepted cost of a core-side predicate; a divergence is caught when a routine
    triple pins it, not here. Cited with provenance so the next reader can re-measure
    rather than trust — which is precisely what this issue's two rounds of stale
    numbers show is necessary. -/

/-- `storage_writes` undo entry stride. 160 rather than 128 so a `wasAbsent = 2`
    `destroy_storage` drop can journal a full map row. -/
def storageUndoEntryBytes : Nat := 160

/-- `account_writes` undo entry stride. -/
def accountUndoEntryBytes : Nat := 128

/-- Storage undo capacity: gas-derived upper bound on producer pushes,
    `floor((16777216 − 12000) / 100)`. -/
def storageUndoCapacity : Nat := 167652

/-- Account undo capacity. ⚠️ NOT the map's `txAccountWritesCapacity` (16384): the
    journal is bounded by write *events*, and repeated updates to one key add events
    without adding rows. -/
def accountUndoCapacity : Nat := 163840

/-- Region-size cross-checks, so a stride/capacity edit that stops matching the
    documented arena size fails the build rather than drifting silently. Values from
    `MemoryLayout.lean`'s own tables. -/
example : storageUndoCapacity * storageUndoEntryBytes = 0x1994e80 := by decide
example : accountUndoCapacity * accountUndoEntryBytes = 0x1400000 := by decide

/-! ## Storage undo entries -/

/-- Why an entry was pushed. A field rather than a sentinel: zero is a legitimate
    stored value, so "restore by writing zero" would invent a written-zero slot where
    the spec has no key at all. -/
inductive UndoKind
  /-- `0` — the write overwrote an existing value; `payload` is the previous value. -/
  | overwrite
  /-- `1` — the write appended a new key; restoring means *dropping* it, not zeroing. -/
  | append
  /-- `2` — `destroy_storage` dropped a row; `payload` is the whole 128 B map row. -/
  | destroyDrop
  deriving DecidableEq, BEq, Repr

/-- The emitted `wasAbsent` word for each kind. -/
def UndoKind.code : UndoKind → Nat
  | .overwrite => 0
  | .append => 1
  | .destroyDrop => 2

/-- One `storage_writes` undo entry. -/
structure StorageUndoEntry where
  /-- Index into the tx-level map this write touched, at `+0`. -/
  entryIndex : Word
  /-- Why it was pushed, at `+8`. -/
  kind : UndoKind
  /-- Payload at `+32`: 32 bytes for `.overwrite`, 128 for `.destroyDrop`, and empty
      for `.append` (there is nothing to restore — the key is dropped). -/
  payload : List (BitVec 8)

namespace StorageUndoEntry

/-- The payload length is determined by the kind — the fact that makes reverse replay
    unambiguous, and the reason `wasAbsent` cannot be folded into the payload. -/
def wf (e : StorageUndoEntry) : Prop :=
  match e.kind with
  | .overwrite => e.payload.length = 32
  | .append => e.payload.length = 0
  | .destroyDrop => e.payload.length = 128

end StorageUndoEntry

/-- One storage undo entry at `base`. The `+16..31` pad is unmodelled, so this
    composes with whatever a caller holds for it. -/
def storageUndoEntryIs (base : Word) (e : StorageUndoEntry) : Assertion :=
  ((base) ↦ₘ e.entryIndex)
    ** ((base + 8) ↦ₘ BitVec.ofNat 64 e.kind.code)
    ** bytesRegion (base + 32) e.payload

/-! ## Account undo entries -/

/-- One `account_writes` undo entry. -/
structure AccountUndoEntry where
  /-- `+0` index into the tx-level map. -/
  entryIndex : Word
  /-- `+8` `1` if the write appended a new key, else `0`. -/
  wasAbsent : Word
  /-- `+16` previous nonce. -/
  prevNonce : Word
  /-- `+24` previous presence discriminant. -/
  prevPresent : Word
  /-- `+32` previous balance, 32 bytes big-endian. -/
  prevBalance : List (BitVec 8)
  /-- `+64` previous code hash, 32 bytes. -/
  prevCodeHash : List (BitVec 8)

namespace AccountUndoEntry

/-- Both byte fields are exactly 32 bytes. -/
def wf (e : AccountUndoEntry) : Prop :=
  e.prevBalance.length = 32 ∧ e.prevCodeHash.length = 32

end AccountUndoEntry

/-- One account undo entry at `base`. The `+96..127` pad is unmodelled. -/
def accountUndoEntryIs (base : Word) (e : AccountUndoEntry) : Assertion :=
  ((base) ↦ₘ e.entryIndex)
    ** ((base + 8) ↦ₘ e.wasAbsent)
    ** ((base + 16) ↦ₘ e.prevNonce)
    ** ((base + 24) ↦ₘ e.prevPresent)
    ** bytesRegion (base + 32) e.prevBalance
    ** bytesRegion (base + 64) e.prevCodeHash

/-! ## The runs, stride-parameterised

    One generic recursion per entry type, taking the stride, per #11572's instruction
    that a shared shape would be wrong. -/

/-- Storage undo entries in consecutive `stride`-byte slots from `base`. -/
def storageUndoFrom (stride : Nat) (base : Word) : List StorageUndoEntry → Assertion
  | [] => empAssertion
  | e :: es =>
      storageUndoEntryIs base e ** storageUndoFrom stride (base + BitVec.ofNat 64 stride) es

/-- Account undo entries in consecutive `stride`-byte slots from `base`. -/
def accountUndoFrom (stride : Nat) (base : Word) : List AccountUndoEntry → Assertion
  | [] => empAssertion
  | e :: es =>
      accountUndoEntryIs base e ** accountUndoFrom stride (base + BitVec.ofNat 64 stride) es

/-- The `storage_writes` undo journal at its arena, at the emitted stride. -/
def storageUndoJournalIs (es : List StorageUndoEntry) : Assertion :=
  storageUndoFrom storageUndoEntryBytes STORAGE_WRITES_UNDO_AREA es

/-- The `account_writes` undo journal at its arena, at the emitted stride. -/
def accountUndoJournalIs (es : List AccountUndoEntry) : Assertion :=
  accountUndoFrom accountUndoEntryBytes ACCOUNT_WRITES_UNDO_AREA es

/-- The cursor cell: how many entries are live. A caller supplies the address because
    the cursor is a `.bss` symbol resolved at link time, not a `MemoryLayout`
    constant. -/
def undoCursorIs (addr : Word) (n : Nat) : Assertion :=
  addr ↦ₘ BitVec.ofNat 64 n

/-! ## Well-formedness, with the capacity guard as a PRECONDITION

    #11572 item 3: #11198's capacity guard becomes part of well-formedness, so any
    proof over a push site must discharge it rather than hope. #11189 is the reason
    this is not cosmetic — the journal used to fail **open** on overflow, which is the
    false-ACCEPT direction. -/

/-- Storage journal well-formedness: every entry's payload matches its kind, and the
    journal is within its arena. -/
def StorageUndoJournalWF (es : List StorageUndoEntry) : Prop :=
  (∀ e ∈ es, e.wf) ∧ es.length ≤ storageUndoCapacity

/-- Account journal well-formedness. -/
def AccountUndoJournalWF (es : List AccountUndoEntry) : Prop :=
  (∀ e ∈ es, e.wf) ∧ es.length ≤ accountUndoCapacity

/-! ## `pcFree` -/

theorem pcFree_storageUndoEntryIs (base : Word) (e : StorageUndoEntry) :
    (storageUndoEntryIs base e).pcFree := by
  unfold storageUndoEntryIs
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _

theorem pcFree_storageUndoFrom (stride : Nat) (base : Word) (es : List StorageUndoEntry) :
    (storageUndoFrom stride base es).pcFree := by
  induction es generalizing base with
  | nil => exact pcFree_emp
  | cons e es ih => exact pcFree_sepConj (pcFree_storageUndoEntryIs _ _) (ih _)

theorem pcFree_accountUndoEntryIs (base : Word) (e : AccountUndoEntry) :
    (accountUndoEntryIs base e).pcFree := by
  unfold accountUndoEntryIs
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _

theorem pcFree_accountUndoFrom (stride : Nat) (base : Word) (es : List AccountUndoEntry) :
    (accountUndoFrom stride base es).pcFree := by
  induction es generalizing base with
  | nil => exact pcFree_emp
  | cons e es ih => exact pcFree_sepConj (pcFree_accountUndoEntryIs _ _) (ih _)

/-! ## Structural lemmas

    `snoc` is the one a push site needs, and — as with `DecodeChain.snoc` — it is not
    definitional: the recursion runs from the front while a push extends at the back. -/

theorem storageUndoFrom_cons (stride : Nat) (base : Word) (e : StorageUndoEntry)
    (es : List StorageUndoEntry) :
    storageUndoFrom stride base (e :: es)
      = (storageUndoEntryIs base e
          ** storageUndoFrom stride (base + BitVec.ofNat 64 stride) es) := rfl

theorem accountUndoFrom_cons (stride : Nat) (base : Word) (e : AccountUndoEntry)
    (es : List AccountUndoEntry) :
    accountUndoFrom stride base (e :: es)
      = (accountUndoEntryIs base e
          ** accountUndoFrom stride (base + BitVec.ofNat 64 stride) es) := rfl

/-! ## `snoc` — the push-site direction

    A push extends the journal at the BACK while the run recurses from the FRONT, so
    `snoc` is not definitional (same shape as `DecodeChain.snoc`).

    ⭐ **The arithmetic obstruction recorded here earlier is solvable, and the key is
    `BitVec.ofNat_add_ofNat`.** The step needs

        (base + ofNat stride) + ofNat (stride * n) = base + ofNat (stride * (n + 1))

    over `BitVec 64` with a **variable** stride. `bv_omega` cannot see through
    `ofNat`-of-a-product, which is what made this look blocked — but no bitvector
    reasoning is needed at all: push the two `ofNat`s together with `ofNat_add_ofNat`,
    then discharge `stride + stride * n = stride * (n + 1)` in `Nat` with `ring`. My
    earlier note said this wanted "a dedicated `ofNat` distribution lemma"; that lemma is
    in core, and looking for it beat working around it. -/

/-- The `ofNat`/stride step, isolated: advancing one stride then `n` strides equals
    advancing `n + 1` strides. Separated because both `snoc` proofs need it and it is the
    only arithmetic in either. -/
theorem base_add_stride_succ (base : Word) (stride n : Nat) :
    (base + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (stride * n)
      = base + BitVec.ofNat 64 (stride * (n + 1)) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 1
  -- `stride + stride * n = stride * (n + 1)`. Deliberately NOT `ring`: this file does
  -- not import `Mathlib.Tactic.Ring`, and `omega` cannot multiply two variables either.
  rw [Nat.mul_succ, Nat.add_comm]

/-- Appending one storage undo entry at the run's tail. -/
theorem storageUndoFrom_snoc (stride : Nat) (e : StorageUndoEntry) :
    ∀ (es : List StorageUndoEntry) (base : Word),
      storageUndoFrom stride base (es ++ [e])
        = (storageUndoFrom stride base es
            ** storageUndoEntryIs (base + BitVec.ofNat 64 (stride * es.length)) e) := by
  intro es
  induction es with
  | nil =>
    intro base
    simp only [List.nil_append, List.length_nil, Nat.mul_zero]
    rw [storageUndoFrom_cons]
    simp [storageUndoFrom, sepConj_emp_left', sepConj_emp_right']
  | cons a as ih =>
    intro base
    rw [List.cons_append, storageUndoFrom_cons, storageUndoFrom_cons, ih,
      ← sepConj_assoc', List.length_cons, ← base_add_stride_succ]

/-- Appending one account undo entry at the run's tail. -/
theorem accountUndoFrom_snoc (stride : Nat) (e : AccountUndoEntry) :
    ∀ (es : List AccountUndoEntry) (base : Word),
      accountUndoFrom stride base (es ++ [e])
        = (accountUndoFrom stride base es
            ** accountUndoEntryIs (base + BitVec.ofNat 64 (stride * es.length)) e) := by
  intro es
  induction es with
  | nil =>
    intro base
    simp only [List.nil_append, List.length_nil, Nat.mul_zero]
    rw [accountUndoFrom_cons]
    simp [accountUndoFrom, sepConj_emp_left', sepConj_emp_right']
  | cons a as ih =>
    intro base
    rw [List.cons_append, accountUndoFrom_cons, accountUndoFrom_cons, ih,
      ← sepConj_assoc', List.length_cons, ← base_add_stride_succ]

/-! ## The replay theorem, stated

    #11572 item 2, the reason this is its own issue:

        replay(journal_suffix_since_mark, map) = map_at_mark

    i.e. the guest's revert equals `restoreTxState`'s dict copy on the map view.

    ⚠️ **Stated, not proved.** Discharging it needs the push and replay walkers'
    triples, which do not exist (#11572 non-goals), and it needs the map-side
    predicates from #11571 — which is why that issue is the stated dependency.

    Nesting is LIFO, so reverse replay is exact: a child frame's entries sit above its
    parent's mark, appended keys unwind from the end, and a successful child's entries
    are RETAINED so a later parent revert still undoes them (`frame_return`'s
    merge-on-success cursor discipline). Any replay function has to reverse the suffix,
    which is why the statement below quantifies over `mark` and takes `es.drop mark`. -/

/-- The shape a revert-path proof must establish for the account journal: replaying the
    suffix pushed since `mark`, in reverse, over the current row list returns the row
    list as of `mark`.

    `replay` is a parameter rather than a definition on purpose — the replay *function*
    is what the walker's triple will exhibit, and fixing it here would prejudge the
    walker's shape. What is pinned is the equation it must satisfy, plus the
    well-formedness and cursor facts it may assume. -/
def AccountReplayRestores
    (replay : List AccountUndoEntry → List AccountWriteRow → List AccountWriteRow)
    : Prop :=
  ∀ (es : List AccountUndoEntry) (mark : Nat)
    (rowsAtMark rowsNow : List AccountWriteRow),
    AccountUndoJournalWF es →
    mark ≤ es.length →
    AccountWriteRowsMap rowsAtMark →
    AccountWriteRowsMap rowsNow →
    replay ((es.drop mark).reverse) rowsNow = rowsAtMark

/-- The storage-side analogue, over flat `StorageWriteRow`s. -/
def StorageReplayRestores
    (replay : List StorageUndoEntry → List StorageWriteRow → List StorageWriteRow)
    : Prop :=
  ∀ (es : List StorageUndoEntry) (mark : Nat)
    (rowsAtMark rowsNow : List StorageWriteRow),
    StorageUndoJournalWF es →
    mark ≤ es.length →
    StorageWriteRowsMap rowsAtMark →
    StorageWriteRowsMap rowsNow →
    replay ((es.drop mark).reverse) rowsNow = rowsAtMark

/-! ## Non-vacuity, kernel-checked -/

section NonVacuity

private def sampleOverwrite : StorageUndoEntry :=
  { entryIndex := 3, kind := .overwrite, payload := List.replicate 32 7 }

private def sampleAppend : StorageUndoEntry :=
  { entryIndex := 4, kind := .append, payload := [] }

private def sampleDestroy : StorageUndoEntry :=
  { entryIndex := 5, kind := .destroyDrop, payload := List.replicate 128 0 }

/-- All three kinds are well-formed at their own payload lengths — so `wf` admits the
    whole emitted vocabulary and not just the common case. -/
example : sampleOverwrite.wf ∧ sampleAppend.wf ∧ sampleDestroy.wf := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [StorageUndoEntry.wf, sampleOverwrite, sampleAppend, sampleDestroy]

/-- ⭐ **Negative control on the kind/payload coupling.** An `.append` entry carrying a
    32-byte payload is rejected, and an `.overwrite` carrying none is too. This is what
    stops `wasAbsent` degenerating into a sentinel — the distinction #11189's
    fail-open bug lived next to. -/
example :
    ¬ ({ entryIndex := 0, kind := .append, payload := List.replicate 32 1 }
          : StorageUndoEntry).wf
      ∧ ¬ ({ entryIndex := 0, kind := .overwrite, payload := [] }
          : StorageUndoEntry).wf := by
  refine ⟨?_, ?_⟩ <;> simp [StorageUndoEntry.wf]

/-- The kind codes are the three distinct emitted `wasAbsent` values. -/
example :
    UndoKind.overwrite.code = 0 ∧ UndoKind.append.code = 1
      ∧ UndoKind.destroyDrop.code = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⭐ **The capacity guard bites.** A journal at capacity is well-formed; one over it
    is not — so #11198's guard is a discharged precondition rather than a hope, and
    #11189's fail-open state is not representable as a well-formed journal. -/
example :
    StorageUndoJournalWF (List.replicate storageUndoCapacity sampleAppend)
      ∧ ¬ StorageUndoJournalWF
            (List.replicate (storageUndoCapacity + 1) sampleAppend) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    have : e = sampleAppend := List.eq_of_mem_replicate he
    subst this
    simp [StorageUndoEntry.wf, sampleAppend]
  · simp
  · intro h
    have := h.2
    simp at this

/-- A concrete account undo entry is well-formed. -/
example :
    ({ entryIndex := 1, wasAbsent := 0, prevNonce := 2, prevPresent := 1
       prevBalance := List.replicate 32 0
       prevCodeHash := List.replicate 32 0 } : AccountUndoEntry).wf := by
  simp [AccountUndoEntry.wf]

/-- ⚠️ **The two capacities really are different**, which is the correction this file
    records: the account journal is 10× the value #11572 instructs using. -/
example : accountUndoCapacity ≠ 16384 ∧ storageUndoCapacity ≠ 32768 := by
  refine ⟨?_, ?_⟩ <;> decide

end NonVacuity

end EvmAsm.Stateless
