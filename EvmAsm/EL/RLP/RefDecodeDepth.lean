/-
  EvmAsm.EL.RLP.RefDecodeDepth

  Characterization of the depth-budgeted RLP decoder (`Ref.decodeD`) in terms
  of the unbudgeted reference decoder (`Ref.decode`) and the nesting depth of
  the decoded item (`RLPItem.listDepth`):

      decodeD d bs = some item  ↔  decode bs = some item ∧ item.listDepth ≤ d

  `decodeD` is `decode` with the nesting budget carried as an explicit
  parameter (spent once per list level, rejecting at 0), so a successful
  budgeted decode is exactly a successful unbudgeted decode whose result fits
  the budget — the budget changes the *accept set*, never the value.

  The proof carries the three mutual statements (for `decodeD`,
  `decodeToSequenceD`, `decodeJoinedEncodingsD`) simultaneously by strong
  induction on the window length, following the shared termination measure of
  the two decoder families (`3 * bs.length + phase`): within one length level,
  the sequence claim needs the joined claim only on strictly shorter windows
  (the payload excludes the header byte), the item claim needs the sequence
  claim on the same window, and the joined claim needs the item claim on a
  window of at most the same length (`bs.take L`) plus the joined claim on a
  strictly shorter one (`bs.drop L` with `L ≥ 1` by `decodeItemLength_pos`).

  Note: `RLPItem.listDepth` lives in the `Ref` namespace (not under the
  `RLPItem` type's own namespace `EvmAsm.EL.RLP.RLPItem`), so dot notation
  `item.listDepth` does not resolve; the statements spell it
  `RLPItem.listDepth item`.
-/

import EvmAsm.EL.RLP.RefDecode
import Mathlib.Tactic.SplitIfs

namespace EvmAsm.EL.RLP.Ref

/-! ## `listDepth` unfolding lemmas -/

private theorem listDepth_bytes (b : List Byte) :
    RLPItem.listDepth (RLPItem.bytes b) = 0 := by
  simp [RLPItem.listDepth]

private theorem listDepth_list (items : List RLPItem) :
    RLPItem.listDepth (RLPItem.list items)
      = 1 + (items.map RLPItem.listDepth).foldr max 0 := by
  simp [RLPItem.listDepth]

/-! ## Unfolding helpers for the joined-encodings decoders

Both `decodeJoinedEncodings` and `decodeJoinedEncodingsD` open with a
*dependent* match on `decodeItemLength` (the equation binder `_hL` feeds the
termination proof), which blocks plain rewriting under a `cases` on the
scrutinee.  These lemmas expose the three behaviors (no header / oversized
item / in-window item) as plain equations, phrasing the in-window case with
`Option.bind`/`Option.map` so the subsequent case analysis is `simp`-friendly. -/

private theorem decodeJoinedEncodingsD_cons_none {d : Nat} {b0 : Byte} {tail : List Byte}
    (h : decodeItemLength (b0 :: tail) = none) :
    decodeJoinedEncodingsD d (b0 :: tail) = none := by
  rw [decodeJoinedEncodingsD]
  split
  · rfl
  · rename_i L' hL
    simp only [h] at hL
    cases hL

private theorem decodeJoinedEncodingsD_cons_gt {d : Nat} {b0 : Byte} {tail : List Byte} {L : Nat}
    (h : decodeItemLength (b0 :: tail) = some L) (hLe : ¬ L ≤ (b0 :: tail).length) :
    decodeJoinedEncodingsD d (b0 :: tail) = none := by
  rw [decodeJoinedEncodingsD]
  split
  · rename_i hL
    simp only [h] at hL
    cases hL
  · rename_i L' hL
    simp only [h, Option.some.injEq] at hL
    subst hL
    rw [if_neg hLe]

private theorem decodeJoinedEncodingsD_cons_le {d : Nat} {b0 : Byte} {tail : List Byte} {L : Nat}
    (h : decodeItemLength (b0 :: tail) = some L) (hLe : L ≤ (b0 :: tail).length) :
    decodeJoinedEncodingsD d (b0 :: tail) =
      (decodeD d ((b0 :: tail).take L)).bind fun item =>
        (decodeJoinedEncodingsD d ((b0 :: tail).drop L)).map fun items => item :: items := by
  rw [decodeJoinedEncodingsD]
  split
  · rename_i hL
    simp only [h] at hL
    cases hL
  · rename_i L' hL
    simp only [h, Option.some.injEq] at hL
    subst hL
    rw [if_pos hLe]
    cases decodeD d ((b0 :: tail).take L) with
    | none => simp
    | some item =>
      cases decodeJoinedEncodingsD d ((b0 :: tail).drop L) with
      | none => simp
      | some items => simp

private theorem decodeJoinedEncodings_cons_none {b0 : Byte} {tail : List Byte}
    (h : decodeItemLength (b0 :: tail) = none) :
    decodeJoinedEncodings (b0 :: tail) = none := by
  rw [decodeJoinedEncodings]
  split
  · rfl
  · rename_i L' hL
    simp only [h] at hL
    cases hL

private theorem decodeJoinedEncodings_cons_gt {b0 : Byte} {tail : List Byte} {L : Nat}
    (h : decodeItemLength (b0 :: tail) = some L) (hLe : ¬ L ≤ (b0 :: tail).length) :
    decodeJoinedEncodings (b0 :: tail) = none := by
  rw [decodeJoinedEncodings]
  split
  · rename_i hL
    simp only [h] at hL
    cases hL
  · rename_i L' hL
    simp only [h, Option.some.injEq] at hL
    subst hL
    rw [if_neg hLe]

private theorem decodeJoinedEncodings_cons_le {b0 : Byte} {tail : List Byte} {L : Nat}
    (h : decodeItemLength (b0 :: tail) = some L) (hLe : L ≤ (b0 :: tail).length) :
    decodeJoinedEncodings (b0 :: tail) =
      (decode ((b0 :: tail).take L)).bind fun item =>
        (decodeJoinedEncodings ((b0 :: tail).drop L)).map fun items => item :: items := by
  rw [decodeJoinedEncodings]
  split
  · rename_i hL
    simp only [h] at hL
    cases hL
  · rename_i L' hL
    simp only [h, Option.some.injEq] at hL
    subst hL
    rw [if_pos hLe]
    cases decode ((b0 :: tail).take L) with
    | none => simp
    | some item =>
      cases decodeJoinedEncodings ((b0 :: tail).drop L) with
      | none => simp
      | some items => simp

/-! ## The simultaneous induction -/

private theorem depth_ind : ∀ n : Nat, ∀ bs : List Byte, bs.length ≤ n →
    (∀ d items, decodeToSequenceD d bs = some items ↔
        decodeToSequence bs = some items ∧ (items.map RLPItem.listDepth).foldr max 0 ≤ d) ∧
    (∀ d item, decodeD d bs = some item ↔
        decode bs = some item ∧ RLPItem.listDepth item ≤ d) ∧
    (∀ d items, decodeJoinedEncodingsD d bs = some items ↔
        decodeJoinedEncodings bs = some items ∧ (items.map RLPItem.listDepth).foldr max 0 ≤ d) := by
  intro n
  induction n with
  | zero =>
    intro bs hbs
    have hnil : bs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hbs)
    subst hnil
    refine ⟨fun d items => ?_, fun d item => ?_, fun d items => ?_⟩
    · simp [decodeToSequenceD, decodeToSequence]
    · simp [decodeD, decode]
    · cases items with
      | nil => simp [decodeJoinedEncodingsD, decodeJoinedEncodings]
      | cons x xs => simp [decodeJoinedEncodingsD, decodeJoinedEncodings]
  | succ n ih =>
    -- ### sequence claim (payloads are strictly shorter: joined IH applies)
    have hseq : ∀ bs : List Byte, bs.length ≤ n + 1 → ∀ d items,
        decodeToSequenceD d bs = some items ↔
          decodeToSequence bs = some items ∧
            (items.map RLPItem.listDepth).foldr max 0 ≤ d := by
      intro bs hbs d items
      cases bs with
      | nil => simp [decodeToSequenceD, decodeToSequence]
      | cons b0 rest =>
        have hr : rest.length ≤ n := by
          simp only [List.length_cons] at hbs; omega
        simp only [decodeToSequenceD, decodeToSequence]
        split_ifs
        · simp
        · simp
        · simp
        · exact (ih _ (by rw [List.length_take]; omega)).2.2 d items
        · simp
        · simp
        · simp
        · simp
        · simp
        · exact (ih _ (by rw [List.length_take, List.length_drop]; omega)).2.2 d items
    -- ### item claim (same window: uses the sequence claim just proved)
    have hdec : ∀ bs : List Byte, bs.length ≤ n + 1 → ∀ d item,
        decodeD d bs = some item ↔
          decode bs = some item ∧ RLPItem.listDepth item ≤ d := by
      intro bs hbs d item
      cases bs with
      | nil => simp [decodeD, decode]
      | cons b0 rest =>
        by_cases hb : b0.toNat ≤ 0xBF
        · -- byte-string arm: identical on both sides; depth of a bytes item is 0
          have hD : decodeD d (b0 :: rest)
              = (decodeToBytes (b0 :: rest)).map RLPItem.bytes := by
            cases d <;> simp [decodeD, hb]
          have hU : decode (b0 :: rest)
              = (decodeToBytes (b0 :: rest)).map RLPItem.bytes := by
            simp [decode, hb]
          rw [hD, hU]
          cases hbt : decodeToBytes (b0 :: rest) with
          | none => simp
          | some raw =>
            simp only [Option.map_some, Option.some.injEq]
            constructor
            · rintro rfl
              exact ⟨rfl, by simp [listDepth_bytes]⟩
            · exact fun h => h.1
        · -- list arm: budget is spent here
          have hU : decode (b0 :: rest)
              = (decodeToSequence (b0 :: rest)).map RLPItem.list := by
            simp [decode, hb]
          cases d with
          | zero =>
            have hD : decodeD 0 (b0 :: rest) = none := by
              simp [decodeD, hb]
            rw [hD, hU]
            constructor
            · intro h; cases h
            · rintro ⟨h, hdep⟩
              obtain ⟨items, -, rfl⟩ := Option.map_eq_some_iff.mp h
              rw [listDepth_list] at hdep
              omega
          | succ d' =>
            have hD : decodeD (d' + 1) (b0 :: rest)
                = (decodeToSequenceD d' (b0 :: rest)).map RLPItem.list := by
              simp [decodeD, hb]
            rw [hD, hU]
            constructor
            · intro h
              obtain ⟨items, hs, rfl⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨hs', hdep⟩ := (hseq _ hbs d' items).mp hs
              refine ⟨Option.map_eq_some_iff.mpr ⟨items, hs', rfl⟩, ?_⟩
              rw [listDepth_list]
              omega
            · rintro ⟨h, hdep⟩
              obtain ⟨items, hs', rfl⟩ := Option.map_eq_some_iff.mp h
              rw [listDepth_list] at hdep
              exact Option.map_eq_some_iff.mpr
                ⟨items, (hseq _ hbs d' items).mpr ⟨hs', by omega⟩, rfl⟩
    -- ### joined claim (item window: same-level item claim; remainder: joined IH)
    have hjoin : ∀ bs : List Byte, bs.length ≤ n + 1 → ∀ d items,
        decodeJoinedEncodingsD d bs = some items ↔
          decodeJoinedEncodings bs = some items ∧
            (items.map RLPItem.listDepth).foldr max 0 ≤ d := by
      intro bs hbs d items
      cases bs with
      | nil =>
        cases items with
        | nil => simp [decodeJoinedEncodingsD, decodeJoinedEncodings]
        | cons x xs => simp [decodeJoinedEncodingsD, decodeJoinedEncodings]
      | cons b0 tail =>
        cases hL : decodeItemLength (b0 :: tail) with
        | none =>
          rw [decodeJoinedEncodingsD_cons_none hL, decodeJoinedEncodings_cons_none hL]
          simp
        | some L =>
          by_cases hLe : L ≤ (b0 :: tail).length
          · rw [decodeJoinedEncodingsD_cons_le hL hLe, decodeJoinedEncodings_cons_le hL hLe]
            have hTake : ((b0 :: tail).take L).length ≤ n + 1 := by
              rw [List.length_take]
              simp only [List.length_cons] at hbs ⊢
              omega
            have hDrop : ((b0 :: tail).drop L).length ≤ n := by
              have hL1 : 1 ≤ L := decodeItemLength_pos hL
              rw [List.length_drop]
              simp only [List.length_cons] at hbs ⊢
              omega
            cases hdec1 : decode ((b0 :: tail).take L) with
            | none =>
              have hD1 : decodeD d ((b0 :: tail).take L) = none := by
                cases hD : decodeD d ((b0 :: tail).take L) with
                | none => rfl
                | some it =>
                  obtain ⟨hu, -⟩ := (hdec _ hTake d it).mp hD
                  simp only [hdec1] at hu
                  cases hu
              rw [hD1]
              simp
            | some item =>
              cases hj1 : decodeJoinedEncodings ((b0 :: tail).drop L) with
              | none =>
                have hJ1 : decodeJoinedEncodingsD d ((b0 :: tail).drop L) = none := by
                  cases hJ : decodeJoinedEncodingsD d ((b0 :: tail).drop L) with
                  | none => rfl
                  | some res =>
                    obtain ⟨hu, -⟩ := ((ih _ hDrop).2.2 d res).mp hJ
                    simp only [hj1] at hu
                    cases hu
                rw [hJ1]
                cases hD : decodeD d ((b0 :: tail).take L) <;> simp
              | some items' =>
                constructor
                · intro h
                  cases hD : decodeD d ((b0 :: tail).take L) with
                  | none =>
                    rw [hD] at h
                    simp at h
                  | some it =>
                    rw [hD] at h
                    cases hJ : decodeJoinedEncodingsD d ((b0 :: tail).drop L) with
                    | none =>
                      rw [hJ] at h
                      simp at h
                    | some res =>
                      rw [hJ] at h
                      simp only [Option.bind_some, Option.map_some,
                        Option.some.injEq] at h
                      subst h
                      obtain ⟨hu1, hdep1⟩ := (hdec _ hTake d it).mp hD
                      obtain ⟨hu2, hdep2⟩ := ((ih _ hDrop).2.2 d res).mp hJ
                      simp only [hdec1, Option.some.injEq] at hu1
                      simp only [hj1, Option.some.injEq] at hu2
                      subst hu1
                      subst hu2
                      refine ⟨rfl, ?_⟩
                      simp only [List.map_cons, List.foldr_cons]
                      omega
                · rintro ⟨h, hdep⟩
                  simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
                  subst h
                  simp only [List.map_cons, List.foldr_cons] at hdep
                  have hD : decodeD d ((b0 :: tail).take L) = some item :=
                    (hdec _ hTake d item).mpr ⟨hdec1, by omega⟩
                  have hJ : decodeJoinedEncodingsD d ((b0 :: tail).drop L) = some items' :=
                    ((ih _ hDrop).2.2 d items').mpr ⟨hj1, by omega⟩
                  rw [hD]
                  simp [hJ]
          · rw [decodeJoinedEncodingsD_cons_gt hL hLe, decodeJoinedEncodings_cons_gt hL hLe]
            simp
    exact fun bs hbs => ⟨hseq bs hbs, hdec bs hbs, hjoin bs hbs⟩

/-! ## Headline characterization -/

/-- The depth-budgeted decoder succeeds exactly when the unbudgeted reference
    decoder succeeds *and* the decoded item's nesting depth fits the budget.
    (`RLPItem.listDepth item` is `item.listDepth`; dot notation does not
    resolve because `listDepth` lives in the `Ref` namespace.) -/
theorem decodeD_eq_some_iff (d : Nat) (bs : List Byte) (item : RLPItem) :
    decodeD d bs = some item ↔ decode bs = some item ∧ RLPItem.listDepth item ≤ d :=
  (depth_ind bs.length bs Nat.le.refl).2.1 d item

/-- Mutual statement carrying the induction: budgeted list-payload decoding
    succeeds iff the unbudgeted one does and every decoded item fits the
    (already decremented) budget. -/
theorem decodeToSequenceD_eq_some_iff (d : Nat) (bs : List Byte) (items : List RLPItem) :
    decodeToSequenceD d bs = some items ↔
      decodeToSequence bs = some items ∧ (items.map RLPItem.listDepth).foldr max 0 ≤ d :=
  (depth_ind bs.length bs Nat.le.refl).1 d items

/-- Mutual statement carrying the induction: budgeted joined-encodings decoding
    succeeds iff the unbudgeted one does and every decoded item fits the budget. -/
theorem decodeJoinedEncodingsD_eq_some_iff (d : Nat) (bs : List Byte) (items : List RLPItem) :
    decodeJoinedEncodingsD d bs = some items ↔
      decodeJoinedEncodings bs = some items ∧ (items.map RLPItem.listDepth).foldr max 0 ≤ d :=
  (depth_ind bs.length bs Nat.le.refl).2.2 d items

/-! ## Corollaries -/

/-- A successful unbudgeted decode within the budget is a budgeted decode. -/
theorem decodeD_eq_decode_of_listDepth_le (d : Nat) (bs : List Byte) (item : RLPItem)
    (hd : decode bs = some item) (hdep : RLPItem.listDepth item ≤ d) :
    decodeD d bs = some item :=
  (decodeD_eq_some_iff d bs item).mpr ⟨hd, hdep⟩

/-- The budget only ever *shrinks* the accept set: inputs the reference
    rejects stay rejected at every budget. -/
theorem decodeD_none_of_decode_none (d : Nat) (bs : List Byte)
    (h : decode bs = none) : decodeD d bs = none := by
  cases hD : decodeD d bs with
  | none => rfl
  | some item =>
    obtain ⟨hu, -⟩ := (decodeD_eq_some_iff d bs item).mp hD
    simp only [h] at hu
    cases hu

/-- Budget monotonicity: a decode that fits budget `d` also fits any `d' ≥ d`. -/
theorem decodeD_mono (d d' : Nat) (hle : d ≤ d') (bs : List Byte) (item : RLPItem)
    (h : decodeD d bs = some item) : decodeD d' bs = some item := by
  obtain ⟨hu, hdep⟩ := (decodeD_eq_some_iff d bs item).mp h
  exact (decodeD_eq_some_iff d' bs item).mpr ⟨hu, Nat.le_trans hdep hle⟩

/-- Success of the budgeted decoder, characterized without naming the result. -/
theorem decodeD_isSome_iff (d : Nat) (bs : List Byte) :
    (decodeD d bs).isSome ↔
      ∃ item, decode bs = some item ∧ RLPItem.listDepth item ≤ d := by
  constructor
  · intro h
    obtain ⟨item, hD⟩ := Option.isSome_iff_exists.mp h
    exact ⟨item, (decodeD_eq_some_iff d bs item).mp hD⟩
  · rintro ⟨item, hu, hdep⟩
    rw [decodeD_eq_decode_of_listDepth_le d bs item hu hdep]
    rfl

/-! ## Computational sanity checks

The budget cut sits exactly at `listDepth`: nesting depth `k` needs budget
`k`, one unit per list level, bytes are free. -/

#guard decodeD 0 [0x82#8, 0x61#8, 0x62#8] = some (.bytes [0x61#8, 0x62#8])
#guard RLPItem.listDepth (.list [.list [], .bytes [0x05#8]]) = 2
#guard decodeD 1 [0xc2#8, 0xc0#8, 0x05#8] = none
#guard decodeD 2 [0xc3#8, 0xc0#8, 0x81#8, 0x80#8]
  = some (.list [.list [], .bytes [0x80#8]])
#guard decode [0xc2#8, 0xc1#8, 0xc0#8] = some (.list [.list [.list []]])
#guard decodeD 2 [0xc2#8, 0xc1#8, 0xc0#8] = none
#guard decodeD 3 [0xc2#8, 0xc1#8, 0xc0#8] = some (.list [.list [.list []]])

end EvmAsm.EL.RLP.Ref
