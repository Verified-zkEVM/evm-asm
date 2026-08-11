/-
  EvmAsm.Stateless.State.StorageWriteUpsert

  **The storage writer model, and the two invariants it establishes** (GH #11921 row 2,
  writer half).

  Row 1 (`AccountWriteUpsert.lean`) turned `AccountWriteRowsMap`'s `Nodup` clause from a
  precondition into a theorem about the writer. This is the storage-side counterpart, and
  it carries one invariant the account side has no analogue for.

  ## ⭐ One model, two tiers

  `storage_write_record` (`Codegen/Programs/StorageWriteMap.lean:222`, targeting
  `TX_STORAGE_WRITES_AREA`) and `storage_writes_block_upsert` (`:416`, targeting
  `STORAGE_WRITES_AREA`) are the **same** upsert: identical scan, identical 32-byte
  double-key compare, identical append-with-baseline-capture, identical overflow-drop.
  They differ in arena base and capacity only. So the capacity is a **parameter** here
  rather than a pinned constant, and both routines are instances of one model.

  This also keeps the module core-side: the capacities (`txStorageWritesCapacity = 5588`,
  `blockStorageWritesCapacity = 66666`) live in `Codegen`, which core cannot see — the
  same reason `storageWritesMapIs` takes its base as a parameter
  (`WriteMapAssertions.lean:244`). Parameterising is not a workaround for the layering,
  it is what makes the shared shape visible.

  ## ⭐ The baseline rule, which is not a mirror of anything

  `+96` (the pre-interval baseline) is written **on append only**. A hit overwrites `+64`
  and leaves `+96` alone, deliberately: it freezes the first-write value for the whole
  interval so `execution_map_state_changes` can compare final-vs-parent for MPT apply.

  This is not a stylistic detail. Dropping it made a zero-clear of a nonzero parent look
  like `0 → 0`, so the change was silently omitted from the state root — the 7251
  multi-block residual recorded at `StorageWriteMap.lean:205-212` and #11547. A model that
  merges the baseline like the value would be wrong in exactly the way that regression
  was, and no `Nodup`-style theorem would notice.

  So `storageWriteUpsert_baselines` states it: **the writer never modifies an existing
  row's baseline.** It is the one invariant here whose violation is a known live defect
  rather than a hypothetical.

  ## ⚠️ What this is, and what it is not

  Model-level. There is **no `Program`** for either routine — both are emitted as raw
  RISC-V `String`s, and `docs/4ch8f-guest-image-coverage.md:211,213` classifies them
  UNCONVERTED. So no Hoare triple can be attached and **no registry row is claimed**, the
  same honest position row 1 took (`Progress.lean:785-786`). What is proven here is that
  the *model* has the properties the map vocabulary assumes; tying the model to the
  emitted bytes needs an SAsm transcription that does not exist.

  Read visibility is stated over `storageRowLookup` (`StorageReadPath.lean:57`) rather
  than a second scan function, so the writer's guarantees land on the predicate the read
  path already uses.
-/
import EvmAsm.Stateless.State.StorageReadPath

namespace EvmAsm.Stateless.State

open EvmAsm.Stateless

/-! ## The argument bundle -/

/-- One field per register of the `storage_write_record` / `storage_writes_block_upsert`
    ABI: `a0` = rowAddress ptr, `a1` = slotKey ptr, `a2` = value ptr, and the baseline
    pointer (`a6` / `a3` respectively).

    The baseline is carried **already resolved**: the routines branch on a null pointer
    and store 32 zero bytes (`.Lswr_base_zero` / `.Lswb_base_zero`), because zero *is*
    `_get_pre_tx_storage`'s documented answer for an unset slot rather than a sentinel.
    Modelling the null pointer as a separate case would invent a distinction the guest
    does not make. -/
structure StorageWriteArgs where
  /-- 32-byte outer address key. -/
  rowAddress : List (BitVec 8)
  /-- 32-byte inner slot key. -/
  slotKey : List (BitVec 8)
  /-- 32-byte value to store at `+64`. -/
  value : List (BitVec 8)
  /-- 32-byte baseline, null pointer already resolved to zeros. -/
  baseline : List (BitVec 8)

namespace StorageWriteArgs

/-- All four buffers are exactly 32 bytes — the ABI's own requirement. -/
def wf (a : StorageWriteArgs) : Prop :=
  a.rowAddress.length = 32 ∧ a.slotKey.length = 32
    ∧ a.value.length = 32 ∧ a.baseline.length = 32

/-- The `(address, slot)` pair the scan compares against, in the row's own vocabulary. -/
def key (a : StorageWriteArgs) : List (BitVec 8) × List (BitVec 8) :=
  (a.rowAddress, a.slotKey)

end StorageWriteArgs

/-- The row `.Lswr_append` / `.Lswb_append` builds: all four fields from the arguments,
    baseline included. This is the **only** place a baseline is ever written. -/
def freshStorageRow (a : StorageWriteArgs) : StorageWriteRow :=
  { rowAddress := a.rowAddress, slotKey := a.slotKey,
    value := a.value, baseline := a.baseline }

theorem freshStorageRow_wf {a : StorageWriteArgs} (h : a.wf) :
    (freshStorageRow a).wf := h

/-! ## The scan -/

/-- `.Lswr_scan` / `.Lswb_scan`: overwrite the value of the **first** row whose
    `(address, slot)` pair matches, leaving position, every other row, and — crucially —
    **the matched row's baseline** untouched.

    The `.Lswr_journal_hit` detour is invisible here: it pushes the superseded value onto
    the undo journal (#11572's surface) and then falls through to the same
    `.Lswr_store`, so the map effect is identical whether or not the value changed. -/
def storageUpsertHit (a : StorageWriteArgs) :
    List StorageWriteRow → List StorageWriteRow
  | [] => []
  | r :: rs =>
      if r.key = a.key then { r with value := a.value } :: rs
      else r :: storageUpsertHit a rs

/-- Is the key already present? The scan's exit condition. -/
def storageRowsHave (rs : List StorageWriteRow)
    (k : List (BitVec 8) × List (BitVec 8)) : Prop :=
  ∃ r ∈ rs, r.key = k

instance (rs : List StorageWriteRow) (k : List (BitVec 8) × List (BitVec 8)) :
    Decidable (storageRowsHave rs k) := by
  unfold storageRowsHave; infer_instance

/-- ⭐ **The routine**, both tiers. Scan; on a hit overwrite the value in place; on a miss
    append a fresh row capturing the baseline — unless the arena is full, in which case
    `.Lswr_overflow` / `.Lswb_overflow` sets the sticky flag and **the write is dropped**.

    The overflow arm is `rs` unchanged rather than omitted, for the same reason row 1
    gives: dropping it would make read-visibility false in a way no hypothesis records.

    `cap` is `txStorageWritesCapacity` for `storage_write_record` and
    `blockStorageWritesCapacity` for `storage_writes_block_upsert`. -/
def storageWriteUpsert (cap : Nat) (a : StorageWriteArgs)
    (rs : List StorageWriteRow) : List StorageWriteRow :=
  if storageRowsHave rs a.key then storageUpsertHit a rs
  else if cap ≤ rs.length then rs
  else rs ++ [freshStorageRow a]

/-! ## Key laws

    The two branches, one theorem each: the hit branch adds no key, the miss branch adds a
    key that was provably absent. Together they are why uniqueness survives. -/

/-- The hit branch leaves the key sequence **exactly** as it was, position included —
    only `value` is touched. -/
@[simp] theorem storageUpsertHit_map_key (a : StorageWriteArgs)
    (rs : List StorageWriteRow) :
    (storageUpsertHit a rs).map StorageWriteRow.key
      = rs.map StorageWriteRow.key := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [storageUpsertHit]
    split
    · simp [StorageWriteRow.key]
    · simp [ih]

theorem storageUpsertHit_length (a : StorageWriteArgs) (rs : List StorageWriteRow) :
    (storageUpsertHit a rs).length = rs.length := by
  have h := congrArg List.length (storageUpsertHit_map_key a rs)
  simp only [List.length_map] at h
  exact h

/-- The hit branch adds no key. -/
theorem storageWriteUpsert_map_key_of_hit {cap : Nat} {a : StorageWriteArgs}
    {rs : List StorageWriteRow} (hhit : storageRowsHave rs a.key) :
    (storageWriteUpsert cap a rs).map StorageWriteRow.key
      = rs.map StorageWriteRow.key := by
  unfold storageWriteUpsert
  rw [if_pos hhit, storageUpsertHit_map_key]

/-- The miss branch appends exactly one key, the one just written. -/
theorem storageWriteUpsert_map_key_of_miss {cap : Nat} {a : StorageWriteArgs}
    {rs : List StorageWriteRow} (hmiss : ¬ storageRowsHave rs a.key)
    (hcap : rs.length < cap) :
    (storageWriteUpsert cap a rs).map StorageWriteRow.key
      = rs.map StorageWriteRow.key ++ [a.key] := by
  unfold storageWriteUpsert
  rw [if_neg hmiss, if_neg (by omega : ¬ cap ≤ rs.length)]
  simp [freshStorageRow, StorageWriteRow.key, StorageWriteArgs.key]

/-- The capacity arm changes nothing at all. -/
theorem storageWriteUpsert_of_full {cap : Nat} {a : StorageWriteArgs}
    {rs : List StorageWriteRow} (hmiss : ¬ storageRowsHave rs a.key)
    (hcap : cap ≤ rs.length) :
    storageWriteUpsert cap a rs = rs := by
  unfold storageWriteUpsert
  rw [if_neg hmiss, if_pos hcap]

/-! ## ⭐ Invariant 1 — uniqueness, row 2's counterpart to row 1's headline -/

/-- **The writer preserves `(address, slot)`-uniqueness.**

    Both branches are forced: a hit adds no key, and a miss adds a key the miss condition
    says was absent. The capacity arm is the identity. -/
theorem storageWriteUpsert_nodup (cap : Nat) (a : StorageWriteArgs)
    {rs : List StorageWriteRow} (h : (rs.map StorageWriteRow.key).Nodup) :
    ((storageWriteUpsert cap a rs).map StorageWriteRow.key).Nodup := by
  by_cases hhit : storageRowsHave rs a.key
  · rw [storageWriteUpsert_map_key_of_hit hhit]; exact h
  · by_cases hcap : cap ≤ rs.length
    · rw [storageWriteUpsert_of_full hhit hcap]; exact h
    · rw [storageWriteUpsert_map_key_of_miss hhit (by omega)]
      refine List.Nodup.append h (List.nodup_singleton _) ?_
      intro x hx hx'
      rw [List.mem_singleton] at hx'
      subst hx'
      obtain ⟨r, hr, hrk⟩ := List.mem_map.mp hx
      exact hhit ⟨r, hr, hrk⟩

/-- Well-formedness survives: the hit branch only replaces a 32-byte value with another,
    and the append branch adds a row built from well-formed arguments. -/
theorem storageUpsertHit_wf {a : StorageWriteArgs} (ha : a.wf)
    {rs : List StorageWriteRow} (h : ∀ r ∈ rs, r.wf) :
    ∀ r ∈ storageUpsertHit a rs, r.wf := by
  induction rs with
  | nil => intro r hr; cases hr
  | cons r0 rs ih =>
    intro r hr
    rw [storageUpsertHit] at hr
    split at hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨(h r0 (List.mem_cons_self ..)).1, (h r0 (List.mem_cons_self ..)).2.1,
          ha.2.2.1, (h r0 (List.mem_cons_self ..)).2.2.2⟩
      · exact h r (List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact h r (List.mem_cons_self ..)
      · exact ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) r hr

theorem storageWriteUpsert_wf {cap : Nat} {a : StorageWriteArgs} (ha : a.wf)
    {rs : List StorageWriteRow} (h : ∀ r ∈ rs, r.wf) :
    ∀ r ∈ storageWriteUpsert cap a rs, r.wf := by
  unfold storageWriteUpsert
  split
  · exact storageUpsertHit_wf ha h
  · split
    · exact h
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact h r hr
      · rw [List.mem_singleton] at hr; subst hr; exact freshStorageRow_wf ha

/-- ⭐ **The payoff: `StorageWriteRowsMap` is preserved by the writer.**

    So the `Nodup` clause that `WriteMapAssertions.lean:337` states as a precondition is,
    for any state reachable by writing, a theorem — exactly the row-1 argument on the
    storage side. Note this also feeds `storageRowsAbstract`, whose hypothesis is now
    discharged rather than assumed at every call site. -/
theorem storageWriteUpsert_rowsMap (cap : Nat) {a : StorageWriteArgs} (ha : a.wf)
    {rs : List StorageWriteRow} (h : StorageWriteRowsMap rs) :
    StorageWriteRowsMap (storageWriteUpsert cap a rs) :=
  ⟨storageWriteUpsert_wf ha h.1, storageWriteUpsert_nodup cap a h.2⟩

/-- The empty arena is a map, so the invariant has a base case to start from. -/
theorem storageWriteRowsMap_nil : StorageWriteRowsMap ([] : List StorageWriteRow) := by
  refine ⟨?_, ?_⟩
  · intro r hr; cases hr
  · exact List.nodup_nil

/-! ## ⭐ Invariant 2 — the baseline is append-only

    The one with a known live defect behind it (#11547 / the 7251 multi-block residual,
    `StorageWriteMap.lean:205-212`). Stated separately from uniqueness because the two
    fail independently: a writer could keep keys unique and still clobber baselines, and
    that writer would produce a well-formed map with a wrong state root. -/

/-- **A hit never touches any row's baseline.** The scan rewrites `+64` only. -/
@[simp] theorem storageUpsertHit_map_baseline (a : StorageWriteArgs)
    (rs : List StorageWriteRow) :
    (storageUpsertHit a rs).map StorageWriteRow.baseline
      = rs.map StorageWriteRow.baseline := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [storageUpsertHit]
    split
    · simp
    · simp [ih]

/-- ⭐ **The writer only ever *extends* the baseline sequence — it never modifies an
    existing entry.** Both branches: a hit leaves them all alone, an append adds one at
    the end, the overflow arm changes nothing.

    This is the property whose violation is #11547: with `+96` merged like `+64`, a
    zero-clear of a nonzero parent reads back as `0 → 0` and is dropped from the state
    root. Uniqueness would still hold; the state root would still be wrong. -/
theorem storageWriteUpsert_baselines (cap : Nat) (a : StorageWriteArgs)
    (rs : List StorageWriteRow) :
    (storageWriteUpsert cap a rs).map StorageWriteRow.baseline
      = rs.map StorageWriteRow.baseline
    ∨ (storageWriteUpsert cap a rs).map StorageWriteRow.baseline
      = rs.map StorageWriteRow.baseline ++ [a.baseline] := by
  unfold storageWriteUpsert
  split
  · exact Or.inl (storageUpsertHit_map_baseline a rs)
  · split
    · exact Or.inl rfl
    · exact Or.inr (by simp [freshStorageRow])

/-- The sharper form of the same fact: the existing rows' baselines are a **prefix** of
    the result's, at the same positions. This is the shape a first-write-freezing argument
    consumes — it says position `i`'s baseline is stable for the whole interval. -/
theorem storageWriteUpsert_baselines_prefix (cap : Nat) (a : StorageWriteArgs)
    (rs : List StorageWriteRow) :
    ∃ suffix, (storageWriteUpsert cap a rs).map StorageWriteRow.baseline
      = rs.map StorageWriteRow.baseline ++ suffix := by
  rcases storageWriteUpsert_baselines cap a rs with h | h
  · exact ⟨[], by simpa using h⟩
  · exact ⟨[a.baseline], h⟩

/-! ## Read visibility

    Stated over `storageRowLookup` (`StorageReadPath.lean:57`), the predicate the SLOAD /
    CALL-gate readers already walk, so the writer's guarantee lands where the reader's
    obligation is rather than on a second scan function. -/

/-- The reader's step, matching the scan's step. Proved once so the two visibility
    theorems below argue about rows rather than about `find?`. -/
private theorem storageRowLookup_cons (r : StorageWriteRow)
    (rs : List StorageWriteRow) (addr slot : List (BitVec 8)) :
    storageRowLookup (r :: rs) addr slot
      = if r.keysOn addr slot then some r.value else storageRowLookup rs addr slot := by
  unfold storageRowLookup
  rw [List.find?_cons]
  cases r.keysOn addr slot with
  | true => simp
  | false => simp

/-- The reader's `Bool` key test and the scan's `=` key test agree. Both routines compare
    the same 64 bytes; this says the two models of that comparison do too. -/
private theorem keysOn_iff_key (r : StorageWriteRow) (a : StorageWriteArgs) :
    r.keysOn a.rowAddress a.slotKey = true ↔ r.key = a.key := by
  simp [StorageWriteRow.keysOn, StorageWriteRow.key, StorageWriteArgs.key, Prod.ext_iff]

/-- A hit is visible to the reader: after overwriting, the looked-up value is the one
    just written. Induction follows the scan, and the reader stops at the same row. -/
theorem storageRowLookup_storageUpsertHit (a : StorageWriteArgs)
    (rs : List StorageWriteRow) (hhit : storageRowsHave rs a.key) :
    storageRowLookup (storageUpsertHit a rs) a.rowAddress a.slotKey = some a.value := by
  induction rs with
  | nil => obtain ⟨r, hr, -⟩ := hhit; cases hr
  | cons r rs ih =>
    rw [storageUpsertHit]
    split
    · next hkey =>
      have hkeys : ({ r with value := a.value } : StorageWriteRow).keysOn
          a.rowAddress a.slotKey = true := (keysOn_iff_key _ a).mpr hkey
      rw [storageRowLookup_cons, if_pos hkeys]
    · next hkey =>
      have hne : ¬ r.keysOn a.rowAddress a.slotKey = true := fun hc =>
        hkey ((keysOn_iff_key r a).mp hc)
      have hrest : storageRowsHave rs a.key := by
        obtain ⟨r', hr', hk'⟩ := hhit
        rcases List.mem_cons.mp hr' with rfl | hr'
        · exact absurd hk' hkey
        · exact ⟨r', hr', hk'⟩
      rw [storageRowLookup_cons, if_neg hne, ih hrest]

/-- The append is visible: no earlier row keys on the pair (that is the miss condition),
    so the reader walks to the fresh row. -/
private theorem storageRowLookup_append_of_miss (a : StorageWriteArgs)
    {rs : List StorageWriteRow} (hmiss : ¬ storageRowsHave rs a.key) :
    storageRowLookup (rs ++ [freshStorageRow a]) a.rowAddress a.slotKey
      = some a.value := by
  induction rs with
  | nil =>
    have hfresh : (freshStorageRow a).keysOn a.rowAddress a.slotKey = true :=
      (keysOn_iff_key _ a).mpr rfl
    rw [List.nil_append, storageRowLookup_cons, if_pos hfresh]
    rfl
  | cons r rs ih =>
    have hr : ¬ r.key = a.key := fun hc => hmiss ⟨r, List.mem_cons_self, hc⟩
    have hne : ¬ r.keysOn a.rowAddress a.slotKey = true := fun hc =>
      hr ((keysOn_iff_key r a).mp hc)
    have hrest : ¬ storageRowsHave rs a.key := by
      rintro ⟨r', hr', hk'⟩
      exact hmiss ⟨r', List.mem_cons_of_mem _ hr', hk'⟩
    rw [List.cons_append, storageRowLookup_cons, if_neg hne, ih hrest]

/-- ⭐ **The write is visible on both live branches.** On a hit the value is overwritten;
    on an append it is the only row with that key. Only the dropped-on-overflow arm fails
    to be visible, and that arm is `rs` unchanged — which is exactly why it is modelled
    rather than omitted. -/
theorem storageRowLookup_storageWriteUpsert {cap : Nat} (a : StorageWriteArgs)
    {rs : List StorageWriteRow} (hcap : ¬ (¬ storageRowsHave rs a.key ∧ cap ≤ rs.length)) :
    storageRowLookup (storageWriteUpsert cap a rs) a.rowAddress a.slotKey
      = some a.value := by
  unfold storageWriteUpsert
  by_cases hhit : storageRowsHave rs a.key
  · rw [if_pos hhit]; exact storageRowLookup_storageUpsertHit a rs hhit
  · have hlt : ¬ cap ≤ rs.length := fun hc => hcap ⟨hhit, hc⟩
    rw [if_neg hhit, if_neg hlt]
    exact storageRowLookup_append_of_miss a hhit

/-! ## Non-vacuity

    Samples with concrete 32-byte buffers, so the definitions are exercised on data
    rather than only quantified over. Same discipline as `WriteMapAssertions.lean:541`. -/

private def zeros32 : List (BitVec 8) := List.replicate 32 (0 : BitVec 8)

private def sampleArgs : StorageWriteArgs :=
  { rowAddress := (1 : BitVec 8) :: List.replicate 31 (0 : BitVec 8),
    slotKey := (2 : BitVec 8) :: List.replicate 31 (0 : BitVec 8),
    value := (7 : BitVec 8) :: List.replicate 31 (0 : BitVec 8),
    baseline := zeros32 }

/-- A second write to the same key, with a different value and a different baseline —
    the case where a naive merge would clobber the frozen baseline. -/
private def sampleArgs2 : StorageWriteArgs :=
  { sampleArgs with
    value := (9 : BitVec 8) :: List.replicate 31 (0 : BitVec 8),
    baseline := (5 : BitVec 8) :: List.replicate 31 (0 : BitVec 8) }

private theorem sampleArgs_wf : sampleArgs.wf := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sampleArgs, zeros32]

/-- The append lands, and the map property holds afterwards. -/
private theorem sample_append :
    storageWriteUpsert 16 sampleArgs [] = [freshStorageRow sampleArgs] := by
  unfold storageWriteUpsert
  rw [if_neg (by rintro ⟨r, hr, -⟩; cases hr), if_neg (by decide)]
  rfl

/-- ⭐ **The baseline survives the second write, and the value does not.** This is the
    regression check: with a merged baseline the second component would read `5`. -/
private theorem sample_baseline_frozen :
    (storageWriteUpsert 16 sampleArgs2 (storageWriteUpsert 16 sampleArgs [])).map
        StorageWriteRow.baseline
      = [zeros32]
    ∧ (storageWriteUpsert 16 sampleArgs2 (storageWriteUpsert 16 sampleArgs [])).map
        StorageWriteRow.value
      = [(9 : BitVec 8) :: List.replicate 31 (0 : BitVec 8)] := by
  rw [sample_append]
  refine ⟨?_, ?_⟩ <;>
    · unfold storageWriteUpsert
      rw [if_pos ⟨freshStorageRow sampleArgs, List.mem_cons_self .., rfl⟩]
      rfl

end EvmAsm.Stateless.State
