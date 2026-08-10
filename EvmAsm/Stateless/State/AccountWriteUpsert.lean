/-
  EvmAsm.Stateless.State.AccountWriteUpsert

  **The `account_write_record` writer model, and the uniqueness invariant it
  establishes** (GH #11921 row 1).

  `WriteMapAssertions.lean` (#11571/#11906) left `AccountWriteRowsMap`'s `Nodup` clause
  as a *precondition* with an explicit reason:

  > uniqueness is a property of the *writer*, and proving it belongs to the upsert
  > routine's triple — which does not exist yet.

  This module supplies the missing half that is available today: a model of
  `account_write_record`'s scan-then-append upsert, and the theorem that it **preserves
  address-uniqueness**. `accountWriteUpsert_rowsMap` is the payoff — the precondition is
  now a theorem about the writer, so a caller that starts from a well-formed map and
  calls the writer stays in a well-formed map.

  ## ⚠️ What this is, and what it is not

  This is a **model-level** result, not a machine-level Hoare triple. There is no SAsm
  `Fn` transcription of `account_write_record` in the tree — it is emitted as assembly
  text (`Codegen/Programs/AccountWriteMap.lean:243`) — so `cpsTripleWithin` has nothing
  to attach to, and inventing a triple over a routine the assembler emits as a string
  would be an unearned claim. Concretely, the gap is:

  * ✅ proved here: the upsert's *algorithm* preserves uniqueness, refines `dictSet` on
    keys, and is read-visible; the capacity arm drops writes.
  * ❌ not proved here: that the emitted instruction sequence implements this model.
    That obligation is `accountWriteUpsert` ≟ `.Lawr_scan`/`.Lawr_append`/`.Lawr_store`,
    and it needs the SAsm transcription first.

  So no registry row is claimed and no tier is regraded. What the model buys is that the
  *specification side* of that future triple is now fixed, machine-checked, and cited by
  symbol — and, per #11921's ranking of row 1, that every downstream row can consume
  uniqueness as a theorem instead of assuming it.

  ## Faithfulness notes (read these before trusting the model)

  1. **The scan does not check liveness.** `.Lawr_cmp` compares 20 key bytes for every
     index below `tx_account_writes_count`; there is no `execFlags` test. So the writer
     hits the first row with a matching address whether it is live or dead, and therefore
     never creates a second row for an address. That is why the theorem below is stated
     over **all** rows, which is stronger than `AccountWriteRowsMap` needs, and the
     live-row clause follows (`nodup_liveAccountRows_of_nodup`).

     ⇒ Corollary worth recording: the dead-row duplicate that `WriteMapAssertions`'
     `[sampleRowDead, sampleRowA]` control admits is **not reachable through this
     writer**. It remains reachable in principle through the other producers (undo
     restore, `account_writes_apply_deletes`, `account_writes_incorporate_tx`), which are
     out of scope here — so the predicate's tolerance stays justified, just not by this
     routine.

  2. **The mask arms are independent**, which is what licenses the field-explicit form of
     `mergeAccountWrite` below. Each arm tests a distinct `andi` immediate and stores to a
     distinct offset (`32..63`, `64`, `72`, `80/88`, `96`), and only the nonce arm reads
     the row back. Rewriting the emitted straight line as a simultaneous record update is
     therefore an equality, not a reordering.

  3. **The nonce is max-reduced, not overwritten.** `bltu t3, t4, .Lawr_no_nonce` skips
     the store when the incoming nonce is *below* the row's, per
     `block_access_lists.py:440-447`. This is a real divergence from
     `SpecRef.setAccount`, which replaces the whole `Optional[Account]`; see
     `NonVacuity` for the kernel-checked witness that the two differ.
-/

import EvmAsm.Stateless.State.WriteMapAssertions

namespace EvmAsm.Stateless.State

open EvmAsm.Stateless.SpecRef (dictSet)

/-! ## Constants, mirrored not imported

    `Stateless/State/` cannot import `Codegen/` (the `check-layering` L1 ruling recorded
    in `WriteMapAssertions.lean`), so the emitted constants are restated here with their
    citation — the same discipline `accountWriteRowBytes` already follows. The `example`s
    are the drift pins. -/

/-- Component-valid mask VALUES from `AccountWriteMap.lean:161-201`. These are values,
    not bit indices: they are the emitted `andi` immediates. -/
def accountWriteMaskBalance : Nat := 1
def accountWriteMaskNonce : Nat := 2
def accountWriteMaskCode : Nat := 4
def accountWriteMaskState : Nat := 8
def accountWriteMaskExecFlags : Nat := 16
def accountWriteMaskTouched : Nat := 32

/-- Rows in the transaction-level arena (`AccountWriteUndo.lean:25`). The bound
    `.Lawr_append` tests with `bgeu t1, t2`. -/
def txAccountWriteCapacity : Nat := 16384

/-- Drift pin: the capacity and the row stride still fill exactly the 2 MiB reservation
    the emitted `#guard` asserts. If either constant moves, this fails. -/
example : txAccountWriteCapacity * accountWriteRowBytes = 0x200000 := by decide

/-- Drift pin: the six mask values are the distinct powers of two the arms test, so no
    two arms can alias. -/
example : [accountWriteMaskBalance, accountWriteMaskNonce, accountWriteMaskCode,
    accountWriteMaskState, accountWriteMaskExecFlags, accountWriteMaskTouched]
    = [1, 2, 4, 8, 16, 32] := by decide

/-- Does `mask` select this component? -/
def maskHas (mask : Word) (v : Nat) : Prop :=
  mask &&& BitVec.ofNat 64 v ≠ 0

instance (mask : Word) (v : Nat) : Decidable (maskHas mask v) := by
  unfold maskHas; infer_instance

/-! ## The call

    `account_write_record`'s arguments, one field per register, named as the calling
    convention documents them (`AccountWriteMap.lean:219-230`). Pointer arguments appear
    already dereferenced: `a0`/`a1`/`a3` are addresses of buffers the routine copies, and
    modelling the copy rather than the pointer is what makes the model about the map
    instead of about memory. -/
structure AccountWriteArgs where
  /-- `a0` → the canonical 20-byte big-endian key. -/
  address : List (BitVec 8)
  /-- `a1` → 32-byte big-endian balance; consumed only under `BALANCE`. -/
  balance : List (BitVec 8)
  /-- `a2`, by value. Consumed only under `NONCE`, and then max-reduced. -/
  nonce : Word
  /-- `a3`/`a4`, consumed together under `CODE`. -/
  codePtr : Word
  codeLen : Word
  /-- `a5`, the `Optional[Account]` discriminant; consumed under `STATE`. -/
  optionalState : Word
  /-- `a6`, the component-valid mask. -/
  mask : Word
  /-- `a7`, consumed only under `EXEC_FLAGS`. -/
  execFlags : Word

namespace AccountWriteArgs

/-- The lengths real producers supply, and the ones `.Lawr_copy_addr` / the balance arm
    actually store. The row-level counterpart of `AccountWriteRow.wf`. -/
def wf (a : AccountWriteArgs) : Prop :=
  a.address.length = 20 ∧ a.balance.length = 32

end AccountWriteArgs

/-! ## `.Lawr_zero` and `.Lawr_store` -/

/-- `.Lawr_append` + `.Lawr_zero`: the key is copied and **every** other modelled field
    is zeroed before the store arms run. -/
def freshAccountRow (address : List (BitVec 8)) : AccountWriteRow :=
  { address := address
    balance := List.replicate 32 0
    nonce := 0
    optionalState := 0
    codePtr := 0
    codeLen := 0
    execFlags := 0
    validMask := 0 }

/-- `.Lawr_store`: the fieldwise merge, as a simultaneous record update.

    Licensed by faithfulness note 2 (the arms are offset-disjoint and order-independent).
    Written field-explicit rather than as a fold of `if`s so that
    `mergeAccountWrite_address` is `rfl` — the key-invariance every theorem below rests
    on is then true by construction rather than by a proof that could rot.

    ⚠️ The nonce arm is `max`, not assignment: `bltu` skips the store when the incoming
    nonce is strictly below the row's, so the guard is `r.nonce ≤ a.nonce` (unsigned,
    matching `bltu`). -/
def mergeAccountWrite (a : AccountWriteArgs) (r : AccountWriteRow) : AccountWriteRow :=
  { address := r.address
    balance := if maskHas a.mask accountWriteMaskBalance then a.balance else r.balance
    nonce :=
      if maskHas a.mask accountWriteMaskNonce ∧ r.nonce ≤ a.nonce then a.nonce else r.nonce
    optionalState :=
      if maskHas a.mask accountWriteMaskState then a.optionalState else r.optionalState
    codePtr := if maskHas a.mask accountWriteMaskCode then a.codePtr else r.codePtr
    codeLen := if maskHas a.mask accountWriteMaskCode then a.codeLen else r.codeLen
    execFlags :=
      if maskHas a.mask accountWriteMaskExecFlags then a.execFlags else r.execFlags
    -- The sticky OR at the end of `.Lawr_no_flags`, which is why TOUCHED needs no payload.
    validMask := a.mask ||| r.validMask }

/-- ⭐ **The merge never moves the key.** True by construction; everything downstream
    needs it, so it is named rather than inlined. -/
@[simp] theorem mergeAccountWrite_address (a : AccountWriteArgs) (r : AccountWriteRow) :
    (mergeAccountWrite a r).address = r.address := rfl

/-- The merge preserves row well-formedness, given the caller's buffers are the documented
    lengths. The balance arm is the only one that can break it. -/
theorem mergeAccountWrite_wf {a : AccountWriteArgs} {r : AccountWriteRow}
    (ha : a.wf) (hr : r.wf) : (mergeAccountWrite a r).wf := by
  refine ⟨hr.1, ?_⟩
  show (if maskHas a.mask accountWriteMaskBalance then a.balance else r.balance).length = 32
  split
  · exact ha.2
  · exact hr.2

/-- A fresh row is well-formed exactly when the key is the canonical 20 bytes. -/
theorem freshAccountRow_wf {address : List (BitVec 8)} (h : address.length = 20) :
    (freshAccountRow address).wf := by
  refine ⟨h, ?_⟩
  show (List.replicate 32 (0 : BitVec 8)).length = 32
  simp

/-! ## `.Lawr_scan` -/

/-- `.Lawr_scan`/`.Lawr_cmp`: merge into the **first** row whose 20-byte key matches,
    leaving position and every other row untouched — `dictSet`'s "update keeps position"
    branch.

    Note the absence of a liveness test, per faithfulness note 1. -/
def upsertHit (a : AccountWriteArgs) : List AccountWriteRow → List AccountWriteRow
  | [] => []
  | r :: rs =>
      if r.address = a.address then mergeAccountWrite a r :: rs
      else r :: upsertHit a rs

/-- Is the key already present? The scan's exit condition. -/
def accountRowsHave (rs : List AccountWriteRow) (address : List (BitVec 8)) : Prop :=
  ∃ r ∈ rs, r.address = address

instance (rs : List AccountWriteRow) (address : List (BitVec 8)) :
    Decidable (accountRowsHave rs address) := by
  unfold accountRowsHave; infer_instance

/-- ⭐ **The routine.** Scan; on a hit merge in place; on a miss append a zeroed row and
    merge into it — unless the arena is full, in which case `.Lawr_overflow` sets the
    sticky flag and **the write is dropped**.

    The overflow arm is modelled as `rs` unchanged rather than omitted: dropping it would
    make the read-visibility theorem below false in a way no hypothesis records. -/
def accountWriteUpsert (a : AccountWriteArgs) (rs : List AccountWriteRow) :
    List AccountWriteRow :=
  if accountRowsHave rs a.address then upsertHit a rs
  else if txAccountWriteCapacity ≤ rs.length then rs
  else rs ++ [mergeAccountWrite a (freshAccountRow a.address)]

/-! ## Key laws

    The two branches of `dictSet`, one theorem each. Together they are the whole reason
    uniqueness survives: the hit branch adds no key, and the miss branch adds a key that
    was provably absent. -/

/-- The hit branch leaves the key sequence **exactly** as it was — position included. -/
@[simp] theorem upsertHit_map_address (a : AccountWriteArgs) (rs : List AccountWriteRow) :
    (upsertHit a rs).map AccountWriteRow.address = rs.map AccountWriteRow.address := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [upsertHit]
    split
    · simp
    · simp [ih]

/-- `upsertHit` changes no row's key, so membership of *other* keys is untouched. -/
theorem upsertHit_length (a : AccountWriteArgs) (rs : List AccountWriteRow) :
    (upsertHit a rs).length = rs.length := by
  have h := congrArg List.length (upsertHit_map_address a rs)
  simp only [List.length_map] at h
  exact h

/-- The miss branch appends exactly one key, the one just written. -/
theorem accountWriteUpsert_map_address_of_miss {a : AccountWriteArgs}
    {rs : List AccountWriteRow} (hmiss : ¬ accountRowsHave rs a.address)
    (hcap : rs.length < txAccountWriteCapacity) :
    (accountWriteUpsert a rs).map AccountWriteRow.address
      = rs.map AccountWriteRow.address ++ [a.address] := by
  unfold accountWriteUpsert
  rw [if_neg hmiss, if_neg (by omega : ¬ txAccountWriteCapacity ≤ rs.length)]
  simp [freshAccountRow]

/-- The hit branch adds no key. -/
theorem accountWriteUpsert_map_address_of_hit {a : AccountWriteArgs}
    {rs : List AccountWriteRow} (hhit : accountRowsHave rs a.address) :
    (accountWriteUpsert a rs).map AccountWriteRow.address
      = rs.map AccountWriteRow.address := by
  unfold accountWriteUpsert
  rw [if_pos hhit, upsertHit_map_address]

/-- The capacity arm changes nothing at all. -/
theorem accountWriteUpsert_of_full {a : AccountWriteArgs} {rs : List AccountWriteRow}
    (hmiss : ¬ accountRowsHave rs a.address)
    (hcap : txAccountWriteCapacity ≤ rs.length) :
    accountWriteUpsert a rs = rs := by
  unfold accountWriteUpsert
  rw [if_neg hmiss, if_pos hcap]

/-! ## ⭐ The uniqueness invariant

    #11921 row 1's headline: `AccountWriteRowsMap`'s `Nodup` clause stops being an
    assumption. -/

/-- **The writer preserves address-uniqueness over all rows.**

    Both branches are forced: a hit adds no key (`upsertHit_map_address`), and a miss adds
    a key that the miss condition says was absent. The capacity arm is the identity. -/
theorem accountWriteUpsert_nodup (a : AccountWriteArgs) {rs : List AccountWriteRow}
    (h : (rs.map AccountWriteRow.address).Nodup) :
    ((accountWriteUpsert a rs).map AccountWriteRow.address).Nodup := by
  by_cases hhit : accountRowsHave rs a.address
  · rw [accountWriteUpsert_map_address_of_hit hhit]; exact h
  · by_cases hcap : txAccountWriteCapacity ≤ rs.length
    · rw [accountWriteUpsert_of_full hhit hcap]; exact h
    · rw [accountWriteUpsert_map_address_of_miss hhit (by omega)]
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      -- The appended key is fresh precisely because the scan missed.
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro hxy
      subst hxy
      obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hx
      exact hhit ⟨r, hr, hrx⟩

/-- Uniqueness over all rows implies it over the live ones: `liveAccountRows` is a
    `filter`, so its key list is a sublist of the full key list. -/
theorem nodup_liveAccountRows_of_nodup {rs : List AccountWriteRow}
    (h : (rs.map AccountWriteRow.address).Nodup) :
    ((liveAccountRows rs).map AccountWriteRow.address).Nodup := by
  unfold liveAccountRows
  exact h.sublist (List.filter_sublist.map AccountWriteRow.address)

/-- The writer preserves row well-formedness. -/
theorem accountWriteUpsert_wf {a : AccountWriteArgs} {rs : List AccountWriteRow}
    (ha : a.wf) (h : ∀ r ∈ rs, r.wf) :
    ∀ r ∈ accountWriteUpsert a rs, r.wf := by
  by_cases hhit : accountRowsHave rs a.address
  · unfold accountWriteUpsert
    rw [if_pos hhit]
    clear hhit
    induction rs with
    | nil => intro r hr; simp [upsertHit] at hr
    | cons x xs ih =>
      rw [upsertHit]
      split
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact mergeAccountWrite_wf ha (h x (by simp))
        · exact h r (by simp [hr])
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact h r (by simp)
        · exact ih (fun y hy => h y (by simp [hy])) r hr
  · by_cases hcap : txAccountWriteCapacity ≤ rs.length
    · rw [accountWriteUpsert_of_full hhit hcap]; exact h
    · unfold accountWriteUpsert
      rw [if_neg hhit, if_neg hcap]
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact h r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact mergeAccountWrite_wf ha (freshAccountRow_wf ha.1)

/-- ⭐⭐ **The precondition is now a theorem.** `AccountWriteRowsMap` is preserved by the
    writer, so a caller need no longer assume uniqueness — it holds inductively from the
    empty arena, which trivially satisfies it.

    This is the fact #11921 says "every other row consumes". -/
theorem accountWriteUpsert_rowsMap {a : AccountWriteArgs} {rs : List AccountWriteRow}
    (ha : a.wf) (h : AccountWriteRowsMap rs)
    (hnd : (rs.map AccountWriteRow.address).Nodup) :
    AccountWriteRowsMap (accountWriteUpsert a rs)
      ∧ ((accountWriteUpsert a rs).map AccountWriteRow.address).Nodup := by
  have hnd' := accountWriteUpsert_nodup a hnd
  exact ⟨⟨accountWriteUpsert_wf ha h.1, nodup_liveAccountRows_of_nodup hnd'⟩, hnd'⟩

/-- The base case that makes the induction usable: the empty arena is a well-formed map
    with unique keys. `tx_account_writes_count` starts at zero every transaction. -/
theorem accountWriteRowsMap_nil :
    AccountWriteRowsMap [] ∧ (([] : List AccountWriteRow).map AccountWriteRow.address).Nodup :=
  ⟨⟨by simp, by simp [liveAccountRows]⟩, by simp⟩

/-! ## Read-visibility

    A writer that maintains an invariant but loses the write would satisfy everything
    above. These are the theorems that pin the write down. -/

/-- The map read, by key — the shape `account_writes_lookup_current` walks. -/
def accountRowLookup (rs : List AccountWriteRow) (address : List (BitVec 8)) :
    Option AccountWriteRow :=
  rs.find? (fun r => decide (r.address = address))

/-- On a hit, the read sees the **merged** row. -/
theorem accountRowLookup_upsertHit {a : AccountWriteArgs} {rs : List AccountWriteRow}
    {r : AccountWriteRow} (h : accountRowLookup rs a.address = some r) :
    accountRowLookup (upsertHit a rs) a.address = some (mergeAccountWrite a r) := by
  induction rs with
  | nil => simp [accountRowLookup] at h
  | cons x xs ih =>
    rw [upsertHit]
    unfold accountRowLookup at h ⊢
    by_cases hx : x.address = a.address
    · -- `x` matched, so it is the row the read returned and the row the merge hit.
      rw [if_pos hx, List.find?_cons_of_pos (by simpa using hx)]
      rw [List.find?_cons_of_pos (by simpa using hx)] at h
      have hxr : x = r := by simpa using h
      subst hxr
      rfl
    · rw [if_neg hx, List.find?_cons_of_neg (by simpa using hx)]
      rw [List.find?_cons_of_neg (by simpa using hx)] at h
      exact ih h

/-- ⭐ **Read sees write, hit branch.** -/
theorem accountRowLookup_upsert_of_hit {a : AccountWriteArgs} {rs : List AccountWriteRow}
    {r : AccountWriteRow} (h : accountRowLookup rs a.address = some r) :
    accountRowLookup (accountWriteUpsert a rs) a.address = some (mergeAccountWrite a r) := by
  have hhit : accountRowsHave rs a.address :=
    ⟨r, List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  unfold accountWriteUpsert
  rw [if_pos hhit]
  exact accountRowLookup_upsertHit h

/-- ⭐ **Read sees write, miss branch** — the appended row is the one the reader finds,
    because no earlier row matches. -/
theorem accountRowLookup_upsert_of_miss {a : AccountWriteArgs} {rs : List AccountWriteRow}
    (hmiss : ¬ accountRowsHave rs a.address)
    (hcap : rs.length < txAccountWriteCapacity) :
    accountRowLookup (accountWriteUpsert a rs) a.address
      = some (mergeAccountWrite a (freshAccountRow a.address)) := by
  unfold accountWriteUpsert accountRowLookup
  rw [if_neg hmiss, if_neg (by omega : ¬ txAccountWriteCapacity ≤ rs.length)]
  rw [List.find?_append]
  have hnone : rs.find? (fun r => decide (r.address = a.address)) = none := by
    rw [List.find?_eq_none]
    intro r hr hp
    simp only [decide_eq_true_eq] at hp
    exact hmiss ⟨r, hr, hp⟩
  rw [hnone]
  simp [freshAccountRow]

/-- ⚠️ **And the arm where it does not.** At capacity the write is dropped, so a reader
    that missed before still misses. Stated so that no downstream proof can quietly
    assume the map always contains what was written. -/
theorem accountRowLookup_upsert_of_full {a : AccountWriteArgs} {rs : List AccountWriteRow}
    (hmiss : ¬ accountRowsHave rs a.address)
    (hcap : txAccountWriteCapacity ≤ rs.length) :
    accountRowLookup (accountWriteUpsert a rs) a.address = none := by
  rw [accountWriteUpsert_of_full hmiss hcap]
  unfold accountRowLookup
  rw [List.find?_eq_none]
  intro r hr hp
  simp only [decide_eq_true_eq] at hp
  exact hmiss ⟨r, hr, hp⟩

/-! ## ⭐ Correspondence to `SpecRef.setAccount`

    `setAccount` is `dictSet ts.accountWrites address account` (`StateTracker.lean:244`),
    and `dictSet` keeps position on a hit and appends on a miss
    (`StateTracker.lean:61`) — structurally the guest's two branches. The theorem below
    makes that identification precise **on keys**, which is the part that transfers
    unconditionally. -/

/-- The key sequence of the guest's arena after a write is exactly `dictSet`'s, below
    capacity. Values are deliberately `Unit`: the *value* halves diverge (see
    `NonVacuity`), the key halves do not, and conflating them is what would produce a
    false `.agrees`. -/
theorem accountWriteUpsert_keys_dictSet (a : AccountWriteArgs) {rs : List AccountWriteRow}
    (hcap : rs.length < txAccountWriteCapacity) :
    (accountWriteUpsert a rs).map AccountWriteRow.address
      = (dictSet (rs.map (fun r => (r.address, ()))) a.address ()).map Prod.fst := by
  unfold dictSet
  by_cases hhit : accountRowsHave rs a.address
  · rw [accountWriteUpsert_map_address_of_hit hhit, if_pos]
    · -- Both sides are the untouched key list; the `if` inside `map` cannot move a key,
      -- because it only fires where the key already equals `a.address`.
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro p hp
      by_cases hk : p.1 = a.address
      · simp [hk]
      · simp [hk]
    · obtain ⟨r, hr, hrk⟩ := hhit
      exact List.any_eq_true.2 ⟨(r.address, ()), List.mem_map.2 ⟨r, hr, rfl⟩, by simp [hrk]⟩
  · rw [accountWriteUpsert_map_address_of_miss hhit hcap, if_neg]
    · simp
    · intro hany
      obtain ⟨p, hp, hpk⟩ := List.any_eq_true.1 hany
      obtain ⟨r, hr, hrp⟩ := List.mem_map.1 hp
      subst hrp
      exact hhit ⟨r, hr, by simpa using hpk⟩

/-! ## Non-vacuity and the value-side divergence

    The negative controls are the point of this section: they are what stops the theorems
    above from being read as "the guest map is `SpecRef.accountWrites`". -/

section NonVacuity

private def keyA : List (BitVec 8) := List.replicate 19 0 ++ [1]
private def keyB : List (BitVec 8) := List.replicate 19 0 ++ [2]

/-- A full-mask write: every component valid (1|2|4|8|16 = 31). -/
private def argsFull (k : List (BitVec 8)) (n : Word) : AccountWriteArgs :=
  { address := k
    balance := List.replicate 31 0 ++ [5]
    nonce := n
    codePtr := 0
    codeLen := 0
    optionalState := 1
    mask := 31
    execFlags := BitVec.ofNat 64 accountWriteLiveFlag }

/-- The writer's arguments are well-formed at the documented lengths. -/
example : (argsFull keyA 7).wf := by
  unfold AccountWriteArgs.wf argsFull keyA; simp

/-- A first write appends one row, and the reader finds it. -/
example :
    (accountWriteUpsert (argsFull keyA 7) []).map AccountWriteRow.address = [keyA] := by
  decide

/-- ⭐ A second write to the **same** key does not grow the arena — the scan hits. This is
    the behaviour uniqueness rests on, checked rather than assumed. -/
example :
    (accountWriteUpsert (argsFull keyA 9)
      (accountWriteUpsert (argsFull keyA 7) [])).length = 1 := by
  decide

/-- ...while a write to a different key does grow it. So the hit test is not vacuously
    true, and the two examples together separate the branches. -/
example :
    (accountWriteUpsert (argsFull keyB 9)
      (accountWriteUpsert (argsFull keyA 7) [])).length = 2 := by
  decide

/-- ⭐ **The value-side divergence, kernel-checked.** A full-mask write carrying nonce 3
    on top of a row at nonce 7 leaves the row at **7**, because `.Lawr_store` max-reduces.
    `SpecRef.setAccount` would have replaced the account wholesale and left nonce 3.

    ⇒ Any `.agrees` claim for this routine against `setAccount` needs an explicit
    nonce-monotonicity hypothesis on the caller; without one the honest verdict is
    `domainRestricted`. That is why `accountWriteUpsert_keys_dictSet` is stated on keys
    only. -/
example :
    ((accountWriteUpsert (argsFull keyA 3)
      (accountWriteUpsert (argsFull keyA 7) [])).map AccountWriteRow.nonce) = [7] := by
  decide

/-- The same write in the other order does move the nonce up, confirming the divergence
    above is the max and not a dropped store. -/
example :
    ((accountWriteUpsert (argsFull keyA 9)
      (accountWriteUpsert (argsFull keyA 7) [])).map AccountWriteRow.nonce) = [9] := by
  decide

/-- ⭐ **The mask is load-bearing.** With `NONCE` cleared the nonce is not written at all,
    even upward — so a `.agrees` claim also needs the caller's mask to select the fields
    the spec's `Account` carries. -/
example :
    ((accountWriteUpsert { argsFull keyA 9 with mask := 1 }
      (accountWriteUpsert (argsFull keyA 7) [])).map AccountWriteRow.nonce) = [7] := by
  decide

/-- The sticky mask OR really accumulates: a BALANCE-only write on top of a full-mask row
    leaves the mask at 31, not 1. `TOUCHED` relies on exactly this. -/
example :
    ((accountWriteUpsert { argsFull keyA 9 with mask := 1 }
      (accountWriteUpsert (argsFull keyA 7) [])).map AccountWriteRow.validMask) = [31] := by
  decide

/-- ⭐ **The invariant, end to end, on a concrete run**: three writes over two keys leave
    a well-formed map with unique live keys. -/
example :
    (((accountWriteUpsert (argsFull keyA 3)
        (accountWriteUpsert (argsFull keyB 9)
          (accountWriteUpsert (argsFull keyA 7) []))).map
      AccountWriteRow.address).Nodup) := by
  decide

end NonVacuity

end EvmAsm.Stateless.State
