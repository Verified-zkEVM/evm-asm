/-
  EvmAsm.Stateless.State.StorageReadPath

  The `storage_writes` **read path** as a finite-map lookup (GH #11654 groundwork).

  ## Why this exists

  SLOAD's stage-1 proof was deleted when #11596/#11595 retired the append-only
  persistent storage exec-log (`Evm64/Storage/LoadSpec.lean` + `LoadLoopSpec.lean`,
  45 theorems), and the registry row regressed `.conditional → .execSpec`
  (`Progress.lean` `entry "SLOAD" .execSpec none`). That was the right call — the
  proof described a container the guest no longer has — but SLOAD is the **only**
  storage opcode whose coverage moved *backward* during the convergence.

  #11654's stated sequence is `#11653`/`#11651` shape-final → #11571's
  `storageWritesMapIs` → the SLOAD triple. As of 2026-08-10 **the gate is fully
  lifted**: #11651, #11653 and #11256 (the consumer census) are all closed, and
  `storageWritesMapIs` landed with #11571.

  This module is the piece between the predicate and the triple: the read path stated
  as a lookup over the row list, with the facts that make it a *function* rather than a
  scan. The triple itself — map lookup → witness fallback over the emitted
  `StorageWriteMap` routine — is not here; it is the large remaining half of #11654.

  ## Shape

  The guest's map is upsert-in-place: `storage_write_record` scans for the
  `(rowAddress, slotKey)` pair and overwrites in place, appending only on a miss. So a
  key appears **at most once**, which is exactly `StorageWriteRowsMap`'s `Nodup`
  clause — and it is what lets `find?` denote a lookup instead of "the first of
  possibly several". `storageRowLookup_eq_some_of_mem` is that step, and it is the
  reason the map property is a precondition rather than decoration.

  ⚠️ Read-path *fallback* is deliberately a hypothesis, not a definition, in
  `SloadReadPath`: on a map miss the guest consults the witness, and what the witness
  yields is the business of the witness-read spine (#11579), not of this module. Fixing
  a fallback function here would prejudge that.
-/

import EvmAsm.Stateless.State.WriteMapAssertions

namespace EvmAsm.Stateless

/-! ## The lookup -/

/-- Does this row key on `(addr, slot)`? -/
def StorageWriteRow.keysOn (r : StorageWriteRow)
    (addr slot : List (BitVec 8)) : Bool :=
  (r.rowAddress == addr) && (r.slotKey == slot)

/-- The read path over the row list: the value written to `(addr, slot)`, or `none` if
    the map has no such key.

    `find?` rather than a fold because the guest scans and stops; under the map
    property there is at most one match, so the choice is not observable — see
    `storageRowLookup_eq_some_of_mem`. -/
def storageRowLookup (rs : List StorageWriteRow)
    (addr slot : List (BitVec 8)) : Option (List (BitVec 8)) :=
  (rs.find? (fun r => r.keysOn addr slot)).map StorageWriteRow.value

/-! ## Lookup is sound, and — under the map property — complete -/

/-- **Soundness.** A `some` answer is witnessed by an actual row with that key. Needs
    no map property: `find?` only ever returns a member satisfying its predicate. -/
theorem storageRowLookup_sound {rs : List StorageWriteRow}
    {addr slot v : List (BitVec 8)}
    (h : storageRowLookup rs addr slot = some v) :
    ∃ r ∈ rs, r.rowAddress = addr ∧ r.slotKey = slot ∧ r.value = v := by
  unfold storageRowLookup at h
  rcases hf : rs.find? (fun r => r.keysOn addr slot) with _ | r
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem : r ∈ rs := List.mem_of_find?_eq_some hf
    have hpred : r.keysOn addr slot = true :=
      List.find?_some (p := fun q : StorageWriteRow => q.keysOn addr slot) hf
    unfold StorageWriteRow.keysOn at hpred
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    exact ⟨r, hmem, hpred.1, hpred.2, h⟩

/-- **Completeness under the map property.** Every row in a well-formed map is found by
    its own key, with its own value.

    ⭐ This is where `StorageWriteRowsMap`'s `Nodup` earns its place: without it,
    `find?` could return an *earlier* row that happens to share the key, and the read
    path would not be a function of the key. The guest upserts in place, so uniqueness
    holds — but it holds because of the writer, which is why it is a precondition. -/
theorem storageRowLookup_eq_some_of_mem {rs : List StorageWriteRow}
    (hmap : StorageWriteRowsMap rs)
    {r : StorageWriteRow} (hr : r ∈ rs) :
    storageRowLookup rs r.rowAddress r.slotKey = some r.value := by
  unfold storageRowLookup
  -- `find?` succeeds, because `r` itself satisfies the predicate.
  rcases hf : rs.find? (fun q => q.keysOn r.rowAddress r.slotKey) with _ | q
  · exfalso
    have : ∀ q ∈ rs, ¬ (q.keysOn r.rowAddress r.slotKey = true) := by
      intro q hq hpred
      exact absurd (List.find?_eq_none.mp hf q hq) (by simpa using hpred)
    exact this r hr (by unfold StorageWriteRow.keysOn; simp)
  · -- The found row shares `r`'s key, so `Nodup` on keys forces it to BE `r`.
    have hqmem : q ∈ rs := List.mem_of_find?_eq_some hf
    have hpred : q.keysOn r.rowAddress r.slotKey = true :=
      List.find?_some (p := fun z : StorageWriteRow => z.keysOn r.rowAddress r.slotKey) hf
    unfold StorageWriteRow.keysOn at hpred
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    have hkey : StorageWriteRow.key q = StorageWriteRow.key r := by
      unfold StorageWriteRow.key
      rw [hpred.1, hpred.2]
    have hq_eq : q = r :=
      List.inj_on_of_nodup_map hmap.2 hqmem hr hkey
    rw [hf, hq_eq]
    simp

/-- Corollary: on a well-formed map the read path is **decided** by membership — a
    `none` answer means no row keys on the pair. Contrapositive of the above, and the
    form a witness-fallback proof consumes (it needs to know the map genuinely missed
    before it may consult the witness). -/
theorem storageRowLookup_eq_none_iff {rs : List StorageWriteRow}
    (hmap : StorageWriteRowsMap rs) (addr slot : List (BitVec 8)) :
    storageRowLookup rs addr slot = none
      ↔ ∀ r ∈ rs, ¬ (r.rowAddress = addr ∧ r.slotKey = slot) := by
  constructor
  · intro h r hr ⟨ha, hs⟩
    subst ha; subst hs
    rw [storageRowLookup_eq_some_of_mem hmap hr] at h
    exact absurd h (by simp)
  · intro h
    unfold storageRowLookup
    rcases hf : rs.find? (fun q => q.keysOn addr slot) with _ | q
    · rw [hf]; simp
    · exfalso
      have hqmem : q ∈ rs := List.mem_of_find?_eq_some hf
      have hpred : q.keysOn addr slot = true :=
        List.find?_some (p := fun z : StorageWriteRow => z.keysOn addr slot) hf
      unfold StorageWriteRow.keysOn at hpred
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      exact h q hqmem ⟨hpred.1, hpred.2⟩

/-! ## The SLOAD read-path obligation, stated

    What the re-proof must establish, phrased so it can be discharged against the
    emitted `StorageWriteMap` read routine and consumed by SLOAD's stack spec.

    `witnessValue` is a **parameter**: on a map miss the guest consults the witness, and
    what the witness yields belongs to the witness-read spine (#11579), not here.
    Fixing it would prejudge that half. Two levels appear because the spec has two —
    `TransactionState.storageWrites` shadows `BlockState.storageWrites`, which shadows
    the witness — and the tx level is checked first. -/

/-- The obligation: reading `(addr, slot)` returns the tx-level map value if present,
    else the block-level value if present, else whatever the witness says. -/
def SloadReadPath
    (witnessValue : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (readAt : List StorageWriteRow → List StorageWriteRow →
      List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    : Prop :=
  ∀ (txRows blockRows : List StorageWriteRow) (addr slot : List (BitVec 8)),
    StorageWriteRowsMap txRows →
    StorageWriteRowsMap blockRows →
    readAt txRows blockRows addr slot
      = (storageRowLookup txRows addr slot).getD
          ((storageRowLookup blockRows addr slot).getD (witnessValue addr slot))

/-- ⭐ **The obligation is satisfiable**, by the two-level lookup itself. This is the
    anti-vacuity check: a `Prop`-valued obligation nobody has instantiated could be
    unsatisfiable, and then a future "SLOAD satisfies `SloadReadPath`" would be
    vacuous. Exhibiting the canonical witness rules that out and simultaneously names
    the function the triple should be proved against. -/
theorem sloadReadPath_canonical
    (witnessValue : List (BitVec 8) → List (BitVec 8) → List (BitVec 8)) :
    SloadReadPath witnessValue
      (fun txRows blockRows addr slot =>
        (storageRowLookup txRows addr slot).getD
          ((storageRowLookup blockRows addr slot).getD (witnessValue addr slot))) := by
  intro _ _ _ _ _ _
  rfl

/-! ## Non-vacuity -/

section NonVacuity

private def rowA : StorageWriteRow :=
  { rowAddress := List.replicate 32 1
    slotKey := List.replicate 31 0 ++ [1]
    value := List.replicate 31 0 ++ [9]
    baseline := List.replicate 32 0 }

private def rowB : StorageWriteRow :=
  { rowA with slotKey := List.replicate 31 0 ++ [2]
              value := List.replicate 31 0 ++ [8] }

/-- Lookup finds each row by its own key, and returns the right value. -/
example : storageRowLookup [rowA, rowB] rowA.rowAddress rowA.slotKey = some rowA.value := by
  unfold storageRowLookup StorageWriteRow.keysOn rowA rowB; decide

example : storageRowLookup [rowA, rowB] rowB.rowAddress rowB.slotKey = some rowB.value := by
  unfold storageRowLookup StorageWriteRow.keysOn rowA rowB; decide

/-- ⭐ **The address is part of the key, not just the slot.** The same slot in a
    different contract misses — which is the divergence `storage_read_record`'s keying
    exists to preserve, and a lookup keyed on the slot alone would silently return
    another contract's value. -/
example :
    storageRowLookup [rowA, rowB] (List.replicate 32 2) rowA.slotKey = none := by
  unfold storageRowLookup StorageWriteRow.keysOn rowA rowB; decide

/-- A miss on an unwritten slot is `none`, so the witness fallback is reachable rather
    than dead code. -/
example :
    storageRowLookup [rowA, rowB] rowA.rowAddress (List.replicate 31 0 ++ [3]) = none := by
  unfold storageRowLookup StorageWriteRow.keysOn rowA rowB; decide

/-- ⭐ **Tx level shadows block level.** With the same key written at both levels the
    read returns the tx value — the ordering `restore_tx_state`/`mergeTxIntoBlock`
    depend on, and the one a single-level model would get wrong. -/
example :
    (storageRowLookup [rowA] rowA.rowAddress rowA.slotKey).getD
        ((storageRowLookup [rowB] rowA.rowAddress rowA.slotKey).getD (List.replicate 32 0))
      = rowA.value := by
  unfold storageRowLookup StorageWriteRow.keysOn rowA rowB; decide

end NonVacuity

end EvmAsm.Stateless
