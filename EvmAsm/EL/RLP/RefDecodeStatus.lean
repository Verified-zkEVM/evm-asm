/-
  EvmAsm.EL.RLP.RefDecodeStatus

  Pure branch lemmas for the recursive machine decoder (#12419 fresh-tree
  track): each lemma states exactly what `decodeD` / `decodeJoinedEncodingsD`
  does on a byte window `win bs off len` under the branch conditions the
  machine routine `rlp_decode` tests (first-byte class, exact-fit and
  canonicality checks, the nesting budget).  The machine correspondence
  proof consumes these; nothing here mentions the machine.

  Window discipline: the machine walks `bs` in place with `(off, len)`
  cursor pairs; the reference decodes slices.  `win bs off len` is the slice
  named by a cursor pair, and the `win_*` algebra says slicing commutes with
  the cursor arithmetic — this is the entire content of the "in-place walk
  = slice recursion" mapping.
-/

import EvmAsm.EL.RLP.RefDecode

namespace EvmAsm.EL.RLP.Ref

open EvmAsm.EL.RLP

/-- The slice named by a cursor pair. -/
def win (bs : List Byte) (off len : Nat) : List Byte :=
  (bs.drop off).take len

/-- Big-endian value of a window (the long-form length field). -/
def winBE (bs : List Byte) (off len : Nat) : Nat :=
  Nat.fromBytesBE (win bs off len)

theorem win_length {bs : List Byte} {off len : Nat}
    (h : off + len ≤ bs.length) : (win bs off len).length = len := by
  unfold win
  rw [List.length_take, List.length_drop]
  omega

theorem win_nil (bs : List Byte) (off : Nat) : win bs off 0 = [] := by
  simp [win]

theorem win_take {bs : List Byte} {off len : Nat} (L : Nat) (hL : L ≤ len) :
    (win bs off len).take L = win bs off L := by
  unfold win
  rw [List.take_take]
  congr 1
  omega

theorem win_drop {bs : List Byte} {off len L : Nat} :
    (win bs off len).drop L = win bs (off + L) (len - L) := by
  unfold win
  rw [List.drop_take, List.drop_drop]

theorem win_getD {bs : List Byte} {off len k : Nat}
    (hk : k < len) (h : off + len ≤ bs.length) :
    (win bs off len).getD k 0 = bs.getD (off + k) 0 := by
  unfold win
  have hoff : off ≤ bs.length := by omega
  have hkd : k < (bs.drop off).length := by
    rw [List.length_drop]
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk,
    List.getElem?_drop, List.getD_eq_getElem?_getD]

theorem win_cons {bs : List Byte} {off len : Nat}
    (hlen : 1 ≤ len) (h : off + len ≤ bs.length) :
    win bs off len = bs.getD off 0 :: win bs (off + 1) (len - 1) := by
  have h1 : (win bs off len).length = len := win_length h
  have hne : win bs off len ≠ [] := by
    intro hnil
    rw [hnil] at h1
    simp at h1
    omega
  obtain ⟨b0, tail, hw⟩ := List.exists_cons_of_ne_nil hne
  have hb0 : b0 = bs.getD off 0 := by
    have h0 := win_getD (bs := bs) (off := off) (len := len) (k := 0)
      (by omega) h
    rw [hw] at h0
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    exact h0
  have htail : tail = win bs (off + 1) (len - 1) := by
    have hdrop := win_drop (bs := bs) (off := off) (len := len) (L := 1)
    rw [hw] at hdrop
    simpa using hdrop
  rw [hw, hb0, htail]

/-! ## Private unfold helpers

`decodeD` hides its budget check behind a nested match on `d`, and
`decodeJoinedEncodingsD` opens with a *dependent* match on `decodeItemLength`
(the equation binder feeds the termination proof), which blocks plain
rewriting under a `cases` on the scrutinee.  These lemmas expose the branch
behaviors as plain equations (same technique as `RefDecodeDepth.lean`). -/

/-- List-header dispatch of `decodeD` at a positive budget. -/
private theorem decodeD_succ_list {d : Nat} {b0 : Byte} {tail : List Byte}
    (hb : ¬ b0.toNat ≤ 0xBF) :
    decodeD (d + 1) (b0 :: tail)
      = (decodeToSequenceD d (b0 :: tail)).map RLPItem.list := by
  unfold decodeD
  rw [if_neg hb]

private theorem decodeJoinedEncodingsD_cons_none {d : Nat} {b0 : Byte}
    {tail : List Byte} (h : decodeItemLength (b0 :: tail) = none) :
    decodeJoinedEncodingsD d (b0 :: tail) = none := by
  rw [decodeJoinedEncodingsD]
  split
  · rfl
  · rename_i L' hL
    simp only [h] at hL
    cases hL

private theorem decodeJoinedEncodingsD_cons_gt {d : Nat} {b0 : Byte}
    {tail : List Byte} {L : Nat}
    (h : decodeItemLength (b0 :: tail) = some L)
    (hLe : ¬ L ≤ (b0 :: tail).length) :
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

private theorem decodeJoinedEncodingsD_cons_le {d : Nat} {b0 : Byte}
    {tail : List Byte} {L : Nat}
    (h : decodeItemLength (b0 :: tail) = some L)
    (hLe : L ≤ (b0 :: tail).length) :
    decodeJoinedEncodingsD d (b0 :: tail) =
      (decodeD d ((b0 :: tail).take L)).bind fun item =>
        (decodeJoinedEncodingsD d ((b0 :: tail).drop L)).map
          fun items => item :: items := by
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

/-! ## Byte-string arms of `decodeD`

The window is `b0 :: rest` with `b0 = bs.getD off 0` and `1 ≤ len`.
Every lemma's hypotheses are exactly the conditions the machine has
established on the branch in question. -/

/-- Empty window rejects. -/
theorem decodeD_len_zero (d : Nat) (bs : List Byte) (off : Nat) :
    decodeD d (win bs off 0) = none := by
  rw [win_nil]
  unfold decodeD
  rfl

/-- Single-byte arm, exact fit: a lone byte below `0x80` is itself. -/
theorem decodeD_single_ok {bs : List Byte} {off : Nat} (d : Nat)
    (h : off + 1 ≤ bs.length) (hb : (bs.getD off 0).toNat < 0x80) :
    decodeD d (win bs off 1) = some (.bytes [bs.getD off 0]) := by
  rw [win_cons (by omega) h]
  simp only [Nat.sub_self, win_nil]
  unfold decodeD decodeToBytes
  rw [if_pos (by omega : (bs.getD off 0).toNat ≤ 0xBF)]
  simp only [List.length_cons, List.length_nil]
  rw [if_pos ⟨trivial, hb⟩]
  rfl

/-- Single-byte first byte with a longer window rejects
    (the reference's "negative length"). -/
theorem decodeD_single_long {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length) (hlen : 2 ≤ len)
    (hb : (bs.getD off 0).toNat < 0x80) :
    decodeD d (win bs off len) = none := by
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos (by omega : (bs.getD off 0).toNat ≤ 0xBF)]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_pos hb]
  rfl

/-- Short byte string with a length mismatch (truncated or trailing). -/
theorem decodeD_short_bytes_badlen {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length) (hlen : 1 ≤ len)
    (hlo : 0x80 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xB7)
    (hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0x80)) :
    decodeD d (win bs off len) = none := by
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos (by omega : (bs.getD off 0).toNat ≤ 0xBF)]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat < 0x80)),
    if_pos hhi]
  rcases Nat.lt_or_ge len (1 + ((bs.getD off 0).toNat - 0x80)) with hc | hc
  · rw [if_pos (by omega : (bs.getD off 0).toNat - 0x80 ≥ len - 1 + 1)]
    rfl
  · rw [if_neg (by omega : ¬((bs.getD off 0).toNat - 0x80 ≥ len - 1 + 1)),
      if_pos (by omega : 1 + ((bs.getD off 0).toNat - 0x80) < len - 1 + 1)]
    rfl

/-- `0x81`-prefixed single byte below `0x80`: non-canonical, rejects. -/
theorem decodeD_short_bytes_noncanon {bs : List Byte} {off : Nat} (d : Nat)
    (h : off + 2 ≤ bs.length)
    (hb : (bs.getD off 0).toNat = 0x81)
    (hraw : (bs.getD (off + 1) 0).toNat < 0x80) :
    decodeD d (win bs off 2) = none := by
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos (by omega : (bs.getD off 0).toNat ≤ 0xBF)]
  have hwl : (win bs (off + 1) (2 - 1)).length = 2 - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [hb]
  rw [if_neg (by omega : ¬((2 : Nat) - 1 + 1 = 1 ∧ (0x81 : Nat) < 0x80)),
    if_neg (by omega : ¬((0x81 : Nat) < 0x80)),
    if_pos (by omega : (0x81 : Nat) ≤ 0xB7),
    if_neg (by omega : ¬((0x81 : Nat) - 0x80 ≥ 2 - 1 + 1)),
    if_neg (by omega : ¬(1 + ((0x81 : Nat) - 0x80) < 2 - 1 + 1)),
    win_take (0x81 - 0x80) (by omega)]
  have hgd : (((win bs (off + 1) (0x81 - 0x80)).getD 0 0)).toNat < 0x80 := by
    rw [win_getD (by omega) (by omega)]
    simpa using hraw
  rw [if_pos ⟨by omega, hgd⟩]
  rfl

/-- Short byte string, exact fit and canonical: accepts the payload. -/
theorem decodeD_short_bytes_ok {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0x80 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xB7)
    (hfit : len = 1 + ((bs.getD off 0).toNat - 0x80))
    (hcanon : ¬ ((bs.getD off 0).toNat = 0x81
      ∧ (bs.getD (off + 1) 0).toNat < 0x80)) :
    decodeD d (win bs off len)
      = some (.bytes (win bs (off + 1) (len - 1))) := by
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos (by omega : (bs.getD off 0).toNat ≤ 0xBF)]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat < 0x80)),
    if_pos hhi,
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0x80 ≥ len - 1 + 1)),
    if_neg (by omega : ¬(1 + ((bs.getD off 0).toNat - 0x80) < len - 1 + 1))]
  have hL : (bs.getD off 0).toNat - 0x80 = len - 1 := by omega
  rw [hL, win_take _ (Nat.le_refl _)]
  have hnc : ¬(len - 1 = 1
      ∧ ((win bs (off + 1) (len - 1)).getD 0 0).toNat < 0x80) := by
    rintro ⟨h1, h2⟩
    rw [win_getD (by omega) (by omega)] at h2
    exact hcanon ⟨by omega, by simpa using h2⟩
  rw [if_neg hnc]
  rfl

/-- Long byte string whose length-of-length runs past the window. -/
theorem decodeD_long_bytes_trunc {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length) (hlen : 1 ≤ len)
    (hlo : 0xB8 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xBF)
    (htr : len ≤ (bs.getD off 0).toNat - 0xB7) :
    decodeD d (win bs off len) = none := by
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos hhi]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xB7)),
    if_pos (by omega : (bs.getD off 0).toNat - 0xB7 ≥ len - 1 + 1)]
  rfl

/-- Long byte string with a leading zero in the length field. -/
theorem decodeD_long_bytes_zero {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xB8 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xBF)
    (htr : (bs.getD off 0).toNat - 0xB7 < len)
    (hz : bs.getD (off + 1) 0 = 0) :
    decodeD d (win bs off len) = none := by
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos hhi]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xB7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xB7 ≥ len - 1 + 1))]
  have hz' : (win bs (off + 1) (len - 1)).getD 0 0 = 0 := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_pos hz']
  rfl

/-- Long byte string declaring a short-form length: non-canonical. -/
theorem decodeD_long_bytes_small {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xB8 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xBF)
    (htr : (bs.getD off 0).toNat - 0xB7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hsmall : winBE bs (off + 1) ((bs.getD off 0).toNat - 0xB7) < 0x38) :
    decodeD d (win bs off len) = none := by
  simp only [winBE] at hsmall
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos hhi]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xB7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xB7 ≥ len - 1 + 1))]
  have hz' : ¬((win bs (off + 1) (len - 1)).getD 0 0 = 0) := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_neg hz',
    win_take _ (by omega : (bs.getD off 0).toNat - 0xB7 ≤ len - 1),
    if_pos hsmall]
  rfl

/-- Long byte string with a length mismatch. -/
theorem decodeD_long_bytes_badlen {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xB8 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xBF)
    (htr : (bs.getD off 0).toNat - 0xB7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hbig : 0x38 ≤ winBE bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
    (hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0xB7)
      + winBE bs (off + 1) ((bs.getD off 0).toNat - 0xB7)) :
    decodeD d (win bs off len) = none := by
  simp only [winBE] at hbig hbad
  rw [win_cons (by omega) h]
  unfold decodeD decodeToBytes
  rw [if_pos hhi]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xB7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xB7 ≥ len - 1 + 1))]
  have hz' : ¬((win bs (off + 1) (len - 1)).getD 0 0 = 0) := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_neg hz',
    win_take _ (by omega : (bs.getD off 0).toNat - 0xB7 ≤ len - 1),
    if_neg (by omega :
      ¬(Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
        < 0x38))]
  rcases Nat.lt_or_ge len (1 + ((bs.getD off 0).toNat - 0xB7)
      + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7)))
    with hc | hc
  · rw [if_pos (by omega : (bs.getD off 0).toNat - 0xB7
        + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
        ≥ len - 1 + 1)]
    rfl
  · rw [if_neg (by omega : ¬((bs.getD off 0).toNat - 0xB7
        + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
        ≥ len - 1 + 1)),
      if_pos (by omega : 1 + ((bs.getD off 0).toNat - 0xB7)
        + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
        < len - 1 + 1)]
    rfl

/-- Long byte string, exact fit: accepts the payload. -/
theorem decodeD_long_bytes_ok {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xB8 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xBF)
    (htr : (bs.getD off 0).toNat - 0xB7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hbig : 0x38 ≤ winBE bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
    (hfit : len = 1 + ((bs.getD off 0).toNat - 0xB7)
      + winBE bs (off + 1) ((bs.getD off 0).toNat - 0xB7)) :
    decodeD d (win bs off len)
      = some (.bytes (win bs (off + 1 + ((bs.getD off 0).toNat - 0xB7))
          (winBE bs (off + 1) ((bs.getD off 0).toNat - 0xB7)))) := by
  have hlen1 : 1 ≤ len := Nat.lt_of_le_of_lt (Nat.zero_le _) htr
  simp only [winBE] at hbig hfit ⊢
  rw [win_cons hlen1 h]
  unfold decodeD decodeToBytes
  rw [if_pos hhi]
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬(len - 1 + 1 = 1 ∧ (bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xB7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xB7 ≥ len - 1 + 1))]
  have hz' : ¬((win bs (off + 1) (len - 1)).getD 0 0 = 0) := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_neg hz',
    win_take _ (by omega : (bs.getD off 0).toNat - 0xB7 ≤ len - 1),
    if_neg (by omega :
      ¬(Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
        < 0x38)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xB7
      + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
      ≥ len - 1 + 1)),
    if_neg (by omega : ¬(1 + ((bs.getD off 0).toNat - 0xB7)
      + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7))
      < len - 1 + 1)),
    win_drop]
  have hdlen : len - 1 - ((bs.getD off 0).toNat - 0xB7)
      = Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xB7)) := by
    omega
  rw [hdlen, win_take _ (Nat.le_refl _)]
  rfl

/-! ## List arms of `decodeD` -/

/-- A list header with an exhausted nesting budget rejects. -/
theorem decodeD_list_budget {bs : List Byte} {off len : Nat}
    (h : off + len ≤ bs.length) (hlen : 1 ≤ len)
    (hlo : 0xC0 ≤ (bs.getD off 0).toNat) :
    decodeD 0 (win bs off len) = none := by
  rw [win_cons hlen h]
  unfold decodeD
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]

/-- Short list with a length mismatch. -/
theorem decodeD_short_list_badlen {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length) (hlen : 1 ≤ len)
    (hlo : 0xC0 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xF7)
    (hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0xC0)) :
    decodeD (d + 1) (win bs off len) = none := by
  rw [win_cons (by omega) h,
    decodeD_succ_list (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]
  unfold decodeToSequenceD
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat < 0xC0)), if_pos hhi]
  rcases Nat.lt_or_ge len (1 + ((bs.getD off 0).toNat - 0xC0)) with hc | hc
  · rw [if_pos (by omega : (bs.getD off 0).toNat - 0xC0 ≥ len - 1 + 1)]
    rfl
  · rw [if_neg (by omega : ¬((bs.getD off 0).toNat - 0xC0 ≥ len - 1 + 1)),
      if_pos (by omega : 1 + ((bs.getD off 0).toNat - 0xC0) < len - 1 + 1)]
    rfl

/-- Short list, exact fit: the payload's joined encodings at the
    decremented budget. -/
theorem decodeD_short_list_items {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xC0 ≤ (bs.getD off 0).toNat) (hhi : (bs.getD off 0).toNat ≤ 0xF7)
    (hfit : len = 1 + ((bs.getD off 0).toNat - 0xC0)) :
    decodeD (d + 1) (win bs off len)
      = (decodeJoinedEncodingsD d (win bs (off + 1) (len - 1))).map .list := by
  rw [win_cons (by omega) h,
    decodeD_succ_list (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]
  unfold decodeToSequenceD
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat < 0xC0)), if_pos hhi,
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xC0 ≥ len - 1 + 1)),
    if_neg (by omega : ¬(1 + ((bs.getD off 0).toNat - 0xC0) < len - 1 + 1))]
  have hJ : (bs.getD off 0).toNat - 0xC0 = len - 1 := by omega
  rw [hJ, win_take _ (Nat.le_refl _)]

/-- Long list whose length-of-length runs past the window. -/
theorem decodeD_long_list_trunc {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length) (hlen : 1 ≤ len)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : len ≤ (bs.getD off 0).toNat - 0xF7) :
    decodeD (d + 1) (win bs off len) = none := by
  rw [win_cons (by omega) h,
    decodeD_succ_list (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]
  unfold decodeToSequenceD
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat < 0xC0)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xF7)),
    if_pos (by omega : (bs.getD off 0).toNat - 0xF7 ≥ len - 1 + 1)]
  rfl

/-- Long list with a leading zero in the length field. -/
theorem decodeD_long_list_zero {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 = 0) :
    decodeD (d + 1) (win bs off len) = none := by
  rw [win_cons (by omega) h,
    decodeD_succ_list (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]
  unfold decodeToSequenceD
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat < 0xC0)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xF7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xF7 ≥ len - 1 + 1))]
  have hz' : (win bs (off + 1) (len - 1)).getD 0 0 = 0 := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_pos hz']
  rfl

/-- Long list declaring a short-form length: non-canonical. -/
theorem decodeD_long_list_small {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hsmall : winBE bs (off + 1) ((bs.getD off 0).toNat - 0xF7) < 0x38) :
    decodeD (d + 1) (win bs off len) = none := by
  simp only [winBE] at hsmall
  rw [win_cons (by omega) h,
    decodeD_succ_list (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]
  unfold decodeToSequenceD
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat < 0xC0)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xF7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xF7 ≥ len - 1 + 1))]
  have hz' : ¬((win bs (off + 1) (len - 1)).getD 0 0 = 0) := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_neg hz',
    win_take _ (by omega : (bs.getD off 0).toNat - 0xF7 ≤ len - 1),
    if_pos hsmall]
  rfl

/-- Long list with a length mismatch. -/
theorem decodeD_long_list_badlen {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hbig : 0x38 ≤ winBE bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
    (hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0xF7)
      + winBE bs (off + 1) ((bs.getD off 0).toNat - 0xF7)) :
    decodeD (d + 1) (win bs off len) = none := by
  simp only [winBE] at hbig hbad
  rw [win_cons (by omega) h,
    decodeD_succ_list (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]
  unfold decodeToSequenceD
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat < 0xC0)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xF7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xF7 ≥ len - 1 + 1))]
  have hz' : ¬((win bs (off + 1) (len - 1)).getD 0 0 = 0) := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_neg hz',
    win_take _ (by omega : (bs.getD off 0).toNat - 0xF7 ≤ len - 1),
    if_neg (by omega :
      ¬(Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
        < 0x38))]
  rcases Nat.lt_or_ge len (1 + ((bs.getD off 0).toNat - 0xF7)
      + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7)))
    with hc | hc
  · rw [if_pos (by omega : (bs.getD off 0).toNat - 0xF7
        + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
        ≥ len - 1 + 1)]
    rfl
  · rw [if_neg (by omega : ¬((bs.getD off 0).toNat - 0xF7
        + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
        ≥ len - 1 + 1)),
      if_pos (by omega : 1 + ((bs.getD off 0).toNat - 0xF7)
        + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
        < len - 1 + 1)]
    rfl

/-- Long list, exact fit: the payload's joined encodings at the
    decremented budget. -/
theorem decodeD_long_list_items {bs : List Byte} {off len : Nat} (d : Nat)
    (h : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hbig : 0x38 ≤ winBE bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
    (hfit : len = 1 + ((bs.getD off 0).toNat - 0xF7)
      + winBE bs (off + 1) ((bs.getD off 0).toNat - 0xF7)) :
    decodeD (d + 1) (win bs off len)
      = (decodeJoinedEncodingsD d
          (win bs (off + 1 + ((bs.getD off 0).toNat - 0xF7))
            (winBE bs (off + 1) ((bs.getD off 0).toNat - 0xF7)))).map .list := by
  have hlen1 : 1 ≤ len := Nat.lt_of_le_of_lt (Nat.zero_le _) htr
  simp only [winBE] at hbig hfit ⊢
  rw [win_cons hlen1 h,
    decodeD_succ_list (by omega : ¬((bs.getD off 0).toNat ≤ 0xBF))]
  unfold decodeToSequenceD
  have hwl : (win bs (off + 1) (len - 1)).length = len - 1 :=
    win_length (by omega)
  simp only [List.length_cons, hwl]
  rw [if_neg (by omega : ¬((bs.getD off 0).toNat < 0xC0)),
    if_neg (by omega : ¬((bs.getD off 0).toNat ≤ 0xF7)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xF7 ≥ len - 1 + 1))]
  have hz' : ¬((win bs (off + 1) (len - 1)).getD 0 0 = 0) := by
    rw [win_getD (by omega) (by omega)]
    simpa using hz
  rw [if_neg hz',
    win_take _ (by omega : (bs.getD off 0).toNat - 0xF7 ≤ len - 1),
    if_neg (by omega :
      ¬(Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
        < 0x38)),
    if_neg (by omega : ¬((bs.getD off 0).toNat - 0xF7
      + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
      ≥ len - 1 + 1)),
    if_neg (by omega : ¬(1 + ((bs.getD off 0).toNat - 0xF7)
      + Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7))
      < len - 1 + 1)),
    win_drop]
  have hdlen : len - 1 - ((bs.getD off 0).toNat - 0xF7)
      = Nat.fromBytesBE (win bs (off + 1) ((bs.getD off 0).toNat - 0xF7)) := by
    omega
  rw [hdlen, win_take _ (Nat.le_refl _)]

/-! ## `decodeItemLength` on a window -/

theorem itemLength_single {bs : List Byte} {c rem : Nat}
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hb : (bs.getD c 0).toNat < 0x80) :
    decodeItemLength (win bs c rem) = some 1 := by
  rw [win_cons hrem h]
  unfold decodeItemLength
  simp only []
  rw [if_pos hb]

theorem itemLength_short_bytes {bs : List Byte} {c rem : Nat}
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hlo : 0x80 ≤ (bs.getD c 0).toNat) (hhi : (bs.getD c 0).toNat ≤ 0xB7) :
    decodeItemLength (win bs c rem)
      = some (1 + ((bs.getD c 0).toNat - 0x80)) := by
  rw [win_cons hrem h]
  unfold decodeItemLength
  simp only []
  rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)), if_pos hhi]

theorem itemLength_short_list {bs : List Byte} {c rem : Nat}
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hlo : 0xC0 ≤ (bs.getD c 0).toNat) (hhi : (bs.getD c 0).toNat ≤ 0xF7) :
    decodeItemLength (win bs c rem)
      = some (1 + ((bs.getD c 0).toNat - 0xC0)) := by
  rw [win_cons hrem h]
  unfold decodeItemLength
  simp only []
  rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)),
    if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xB7)),
    if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xBF)),
    if_pos hhi]

/-- Long-form item header: length-of-length past the window. -/
theorem itemLength_long_trunc {bs : List Byte} {c rem : Nat}
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hlong : 0xB8 ≤ (bs.getD c 0).toNat
      ∧ ((bs.getD c 0).toNat ≤ 0xBF ∨ 0xF8 ≤ (bs.getD c 0).toNat))
    (htr : rem ≤ (bs.getD c 0).toNat
      - (if (bs.getD c 0).toNat ≤ 0xBF then 0xB7 else 0xF7)) :
    decodeItemLength (win bs c rem) = none := by
  have hwl : (win bs (c + 1) (rem - 1)).length = rem - 1 :=
    win_length (by omega)
  rcases hlong.2 with hbf | hf8
  · rw [if_pos hbf] at htr
    rw [win_cons hrem h]
    unfold decodeItemLength
    simp only [List.length_cons, hwl]
    rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xB7)),
      if_pos hbf,
      if_pos (by omega : (bs.getD c 0).toNat - 0xB7 ≥ rem - 1 + 1)]
  · rw [if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xBF))] at htr
    rw [win_cons hrem h]
    unfold decodeItemLength
    simp only [List.length_cons, hwl]
    rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xB7)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xBF)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xF7)),
      if_pos (by omega : (bs.getD c 0).toNat - 0xF7 ≥ rem - 1 + 1)]

/-- Long-form item header: leading zero in the length field. -/
theorem itemLength_long_zero {bs : List Byte} {c rem : Nat}
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hlong : 0xB8 ≤ (bs.getD c 0).toNat
      ∧ ((bs.getD c 0).toNat ≤ 0xBF ∨ 0xF8 ≤ (bs.getD c 0).toNat))
    (htr : (bs.getD c 0).toNat
      - (if (bs.getD c 0).toNat ≤ 0xBF then 0xB7 else 0xF7) < rem)
    (hz : bs.getD (c + 1) 0 = 0) :
    decodeItemLength (win bs c rem) = none := by
  have hwl : (win bs (c + 1) (rem - 1)).length = rem - 1 :=
    win_length (by omega)
  rcases hlong.2 with hbf | hf8
  · rw [if_pos hbf] at htr
    have hz' : (win bs (c + 1) (rem - 1)).getD 0 0 = 0 := by
      rw [win_getD (by omega) (by omega)]
      simpa using hz
    rw [win_cons hrem h]
    unfold decodeItemLength
    simp only [List.length_cons, hwl]
    rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xB7)),
      if_pos hbf,
      if_neg (by omega : ¬((bs.getD c 0).toNat - 0xB7 ≥ rem - 1 + 1)),
      if_pos hz']
  · rw [if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xBF))] at htr
    have hz' : (win bs (c + 1) (rem - 1)).getD 0 0 = 0 := by
      rw [win_getD (by omega) (by omega)]
      simpa using hz
    rw [win_cons hrem h]
    unfold decodeItemLength
    simp only [List.length_cons, hwl]
    rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xB7)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xBF)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xF7)),
      if_neg (by omega : ¬((bs.getD c 0).toNat - 0xF7 ≥ rem - 1 + 1)),
      if_pos hz']

/-- Long-form item header, readable length field. -/
theorem itemLength_long_ok {bs : List Byte} {c rem : Nat}
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hlong : 0xB8 ≤ (bs.getD c 0).toNat
      ∧ ((bs.getD c 0).toNat ≤ 0xBF ∨ 0xF8 ≤ (bs.getD c 0).toNat))
    (htr : (bs.getD c 0).toNat
      - (if (bs.getD c 0).toNat ≤ 0xBF then 0xB7 else 0xF7) < rem)
    (hz : bs.getD (c + 1) 0 ≠ 0) :
    decodeItemLength (win bs c rem)
      = some (1 + ((bs.getD c 0).toNat
            - (if (bs.getD c 0).toNat ≤ 0xBF then 0xB7 else 0xF7))
          + winBE bs (c + 1) ((bs.getD c 0).toNat
            - (if (bs.getD c 0).toNat ≤ 0xBF then 0xB7 else 0xF7))) := by
  have hwl : (win bs (c + 1) (rem - 1)).length = rem - 1 :=
    win_length (by omega)
  simp only [winBE]
  rcases hlong.2 with hbf | hf8
  · have hif : (if (bs.getD c 0).toNat ≤ 0xBF then 0xB7 else 0xF7) = 0xB7 :=
      if_pos hbf
    rw [hif] at htr ⊢
    have hz' : ¬((win bs (c + 1) (rem - 1)).getD 0 0 = 0) := by
      rw [win_getD (by omega) (by omega)]
      simpa using hz
    rw [win_cons hrem h]
    unfold decodeItemLength
    simp only [List.length_cons, hwl]
    rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xB7)),
      if_pos hbf,
      if_neg (by omega : ¬((bs.getD c 0).toNat - 0xB7 ≥ rem - 1 + 1)),
      if_neg hz',
      win_take _ (by omega : (bs.getD c 0).toNat - 0xB7 ≤ rem - 1)]
  · have hif : (if (bs.getD c 0).toNat ≤ 0xBF then 0xB7 else 0xF7) = 0xF7 :=
      if_neg (by omega)
    rw [hif] at htr ⊢
    have hz' : ¬((win bs (c + 1) (rem - 1)).getD 0 0 = 0) := by
      rw [win_getD (by omega) (by omega)]
      simpa using hz
    rw [win_cons hrem h]
    unfold decodeItemLength
    simp only [List.length_cons, hwl]
    rw [if_neg (by omega : ¬((bs.getD c 0).toNat < 0x80)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xB7)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xBF)),
      if_neg (by omega : ¬((bs.getD c 0).toNat ≤ 0xF7)),
      if_neg (by omega : ¬((bs.getD c 0).toNat - 0xF7 ≥ rem - 1 + 1)),
      if_neg hz',
      win_take _ (by omega : (bs.getD c 0).toNat - 0xF7 ≤ rem - 1)]

/-! ## `decodeJoinedEncodingsD` stepping -/

theorem joinedD_nil (d : Nat) (bs : List Byte) (c : Nat) :
    decodeJoinedEncodingsD d (win bs c 0) = some [] := by
  rw [win_nil]
  unfold decodeJoinedEncodingsD
  rfl

/-- No parseable item header: the joined window rejects. -/
theorem joinedD_itemLength_none {bs : List Byte} {c rem : Nat} (d : Nat)
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hL : decodeItemLength (win bs c rem) = none) :
    decodeJoinedEncodingsD d (win bs c rem) = none := by
  have hw : win bs c rem = bs.getD c 0 :: win bs (c + 1) (rem - 1) :=
    win_cons hrem h
  rw [hw] at hL ⊢
  exact decodeJoinedEncodingsD_cons_none hL

/-- Item runs past the window: rejects. -/
theorem joinedD_unfit {bs : List Byte} {c rem L : Nat} (d : Nat)
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hL : decodeItemLength (win bs c rem) = some L)
    (hbig : rem < L) :
    decodeJoinedEncodingsD d (win bs c rem) = none := by
  have hw : win bs c rem = bs.getD c 0 :: win bs (c + 1) (rem - 1) :=
    win_cons hrem h
  have hwl : (win bs (c + 1) (rem - 1)).length = rem - 1 :=
    win_length (by omega)
  rw [hw] at hL ⊢
  refine decodeJoinedEncodingsD_cons_gt hL ?_
  simp only [List.length_cons, hwl]
  omega

/-- The head item slice rejects: the joined window rejects. -/
theorem joinedD_head_none {bs : List Byte} {c rem L : Nat} (d : Nat)
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hL : decodeItemLength (win bs c rem) = some L) (hfit : L ≤ rem)
    (hhead : decodeD d (win bs c L) = none) :
    decodeJoinedEncodingsD d (win bs c rem) = none := by
  have hw : win bs c rem = bs.getD c 0 :: win bs (c + 1) (rem - 1) :=
    win_cons hrem h
  have hwl : (bs.getD c 0 :: win bs (c + 1) (rem - 1)).length = rem := by
    have h1 : (win bs (c + 1) (rem - 1)).length = rem - 1 :=
      win_length (by omega)
    simp only [List.length_cons, h1]
    omega
  rw [hw] at hL
  rw [hw, decodeJoinedEncodingsD_cons_le hL (by rw [hwl]; exact hfit), ← hw,
    win_take _ hfit, hhead]
  rfl

/-- The joined window accepts iff the head item and the rest both do. -/
theorem joinedD_step_isSome {bs : List Byte} {c rem L : Nat} (d : Nat)
    (h : c + rem ≤ bs.length) (hrem : 1 ≤ rem)
    (hL : decodeItemLength (win bs c rem) = some L) (hfit : L ≤ rem) :
    (decodeJoinedEncodingsD d (win bs c rem)).isSome
      ↔ (decodeD d (win bs c L)).isSome
        ∧ (decodeJoinedEncodingsD d (win bs (c + L) (rem - L))).isSome := by
  have hw : win bs c rem = bs.getD c 0 :: win bs (c + 1) (rem - 1) :=
    win_cons hrem h
  have hwl : (bs.getD c 0 :: win bs (c + 1) (rem - 1)).length = rem := by
    have h1 : (win bs (c + 1) (rem - 1)).length = rem - 1 :=
      win_length (by omega)
    simp only [List.length_cons, h1]
    omega
  rw [hw] at hL
  rw [hw, decodeJoinedEncodingsD_cons_le hL (by rw [hwl]; exact hfit), ← hw,
    win_take _ hfit, win_drop]
  cases decodeD d (win bs c L) <;>
    cases decodeJoinedEncodingsD d (win bs (c + L) (rem - L)) <;>
      simp

end EvmAsm.EL.RLP.Ref
