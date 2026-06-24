/-
  EvmAsm.Evm64.MulMod.ReduceCompare

  Pure comparison and subtract-chain bridges for the bit-serial MULMOD
  reducer inner step.
-/

import EvmAsm.Evm64.MulMod.ReduceShift
import EvmAsm.Evm64.EvmWordArith.Arithmetic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Folded predicate for the reducer branch that subtracts the modulus. -/
@[irreducible] def mulModReduceRemGE (r n : EvmWord) : Prop :=
  ¬ BitVec.ult r n

/-- Folded predicate for the reducer branch that skips subtraction. -/
@[irreducible] def mulModReduceRemLT (r n : EvmWord) : Prop :=
  BitVec.ult r n

theorem mulModReduceRemGE_iff_not_ult (r n : EvmWord) :
    mulModReduceRemGE r n ↔ ¬ BitVec.ult r n := by
  unfold mulModReduceRemGE
  exact Iff.rfl

theorem mulModReduceRemLT_iff_ult (r n : EvmWord) :
    mulModReduceRemLT r n ↔ BitVec.ult r n := by
  unfold mulModReduceRemLT
  exact Iff.rfl


theorem word_eq_of_not_ult_not_ult (a b : Word)
    (hab : ¬ BitVec.ult a b) (hba : ¬ BitVec.ult b a) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ult a b ↔ a.toNat < b.toNat from EvmWord.ult_iff] at hab
  rw [show BitVec.ult b a ↔ b.toNat < a.toNat from EvmWord.ult_iff] at hba
  omega

theorem mulModReduceRemGE_of_limb3_gt (r n : EvmWord)
    (h : BitVec.ult (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3)) :
    mulModReduceRemGE r n := by
  unfold mulModReduceRemGE
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  intro h_lt
  have h3 : (EvmWord.getLimbN n 3).toNat < (EvmWord.getLimbN r 3).toNat :=
    EvmWord.ult_iff.mp h
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h_lt
  have hr0 := (EvmWord.getLimbN r 0).isLt
  have hr1 := (EvmWord.getLimbN r 1).isLt
  have hr2 := (EvmWord.getLimbN r 2).isLt
  have hn0 := (EvmWord.getLimbN n 0).isLt
  have hn1 := (EvmWord.getLimbN n 1).isLt
  have hn2 := (EvmWord.getLimbN n 2).isLt
  nlinarith

theorem mulModReduceRemLT_of_limb3_lt (r n : EvmWord)
    (h : BitVec.ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3)) :
    mulModReduceRemLT r n := by
  unfold mulModReduceRemLT
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  have h3 : (EvmWord.getLimbN r 3).toNat < (EvmWord.getLimbN n 3).toNat :=
    EvmWord.ult_iff.mp h
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  have hr0 := (EvmWord.getLimbN r 0).isLt
  have hr1 := (EvmWord.getLimbN r 1).isLt
  have hr2 := (EvmWord.getLimbN r 2).isLt
  have hn0 := (EvmWord.getLimbN n 0).isLt
  have hn1 := (EvmWord.getLimbN n 1).isLt
  have hn2 := (EvmWord.getLimbN n 2).isLt
  nlinarith

theorem mulModReduceRemGE_of_limb2_gt (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h : BitVec.ult (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2)) :
    mulModReduceRemGE r n := by
  unfold mulModReduceRemGE
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  intro h_lt
  have h2 : (EvmWord.getLimbN n 2).toNat < (EvmWord.getLimbN r 2).toNat :=
    EvmWord.ult_iff.mp h
  have h3_nat : (EvmWord.getLimbN r 3).toNat = (EvmWord.getLimbN n 3).toNat :=
    congrArg BitVec.toNat h3_eq
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h_lt
  have hr0 := (EvmWord.getLimbN r 0).isLt
  have hr1 := (EvmWord.getLimbN r 1).isLt
  have hn0 := (EvmWord.getLimbN n 0).isLt
  have hn1 := (EvmWord.getLimbN n 1).isLt
  nlinarith

theorem mulModReduceRemLT_of_limb2_lt (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h : BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)) :
    mulModReduceRemLT r n := by
  unfold mulModReduceRemLT
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  have h2 : (EvmWord.getLimbN r 2).toNat < (EvmWord.getLimbN n 2).toNat :=
    EvmWord.ult_iff.mp h
  have h3_nat : (EvmWord.getLimbN r 3).toNat = (EvmWord.getLimbN n 3).toNat :=
    congrArg BitVec.toNat h3_eq
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  have hr0 := (EvmWord.getLimbN r 0).isLt
  have hr1 := (EvmWord.getLimbN r 1).isLt
  have hn0 := (EvmWord.getLimbN n 0).isLt
  have hn1 := (EvmWord.getLimbN n 1).isLt
  nlinarith

theorem mulModReduceRemGE_of_limb1_gt (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h : BitVec.ult (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1)) :
    mulModReduceRemGE r n := by
  unfold mulModReduceRemGE
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  intro h_lt
  have h1 : (EvmWord.getLimbN n 1).toNat < (EvmWord.getLimbN r 1).toNat :=
    EvmWord.ult_iff.mp h
  have h2_nat : (EvmWord.getLimbN r 2).toNat = (EvmWord.getLimbN n 2).toNat :=
    congrArg BitVec.toNat h2_eq
  have h3_nat : (EvmWord.getLimbN r 3).toNat = (EvmWord.getLimbN n 3).toNat :=
    congrArg BitVec.toNat h3_eq
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h_lt
  have hr0 := (EvmWord.getLimbN r 0).isLt
  have hn0 := (EvmWord.getLimbN n 0).isLt
  nlinarith

theorem mulModReduceRemLT_of_limb1_lt (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h : BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)) :
    mulModReduceRemLT r n := by
  unfold mulModReduceRemLT
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  have h1 : (EvmWord.getLimbN r 1).toNat < (EvmWord.getLimbN n 1).toNat :=
    EvmWord.ult_iff.mp h
  have h2_nat : (EvmWord.getLimbN r 2).toNat = (EvmWord.getLimbN n 2).toNat :=
    congrArg BitVec.toNat h2_eq
  have h3_nat : (EvmWord.getLimbN r 3).toNat = (EvmWord.getLimbN n 3).toNat :=
    congrArg BitVec.toNat h3_eq
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  have hr0 := (EvmWord.getLimbN r 0).isLt
  have hn0 := (EvmWord.getLimbN n 0).isLt
  nlinarith

theorem mulModReduceRemGE_of_limb0_ge (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1)
    (h : ¬ BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    mulModReduceRemGE r n := by
  unfold mulModReduceRemGE
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  intro h_lt
  have h0 : (EvmWord.getLimbN n 0).toNat ≤ (EvmWord.getLimbN r 0).toNat := by
    exact le_of_not_gt (fun hlt => h (EvmWord.ult_iff.mpr hlt))
  have h1_nat : (EvmWord.getLimbN r 1).toNat = (EvmWord.getLimbN n 1).toNat :=
    congrArg BitVec.toNat h1_eq
  have h2_nat : (EvmWord.getLimbN r 2).toNat = (EvmWord.getLimbN n 2).toNat :=
    congrArg BitVec.toNat h2_eq
  have h3_nat : (EvmWord.getLimbN r 3).toNat = (EvmWord.getLimbN n 3).toNat :=
    congrArg BitVec.toNat h3_eq
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h_lt
  nlinarith

theorem mulModReduceRemLT_of_limb0_lt (r n : EvmWord)
    (h3_eq : EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3)
    (h2_eq : EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2)
    (h1_eq : EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1)
    (h : BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) :
    mulModReduceRemLT r n := by
  unfold mulModReduceRemLT
  rw [show BitVec.ult r n ↔ r.toNat < n.toNat from EvmWord.ult_iff]
  rw [EvmWord.toNat_eq_limb_sum r, EvmWord.toNat_eq_limb_sum n]
  have h0 : (EvmWord.getLimbN r 0).toNat < (EvmWord.getLimbN n 0).toNat :=
    EvmWord.ult_iff.mp h
  have h1_nat : (EvmWord.getLimbN r 1).toNat = (EvmWord.getLimbN n 1).toNat :=
    congrArg BitVec.toNat h1_eq
  have h2_nat : (EvmWord.getLimbN r 2).toNat = (EvmWord.getLimbN n 2).toNat :=
    congrArg BitVec.toNat h2_eq
  have h3_nat : (EvmWord.getLimbN r 3).toNat = (EvmWord.getLimbN n 3).toNat :=
    congrArg BitVec.toNat h3_eq
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  nlinarith


theorem mulModReduceRemGE_cases (r n : EvmWord) (hge : mulModReduceRemGE r n) :
    BitVec.ult (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3) ∨
    (EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
      BitVec.ult (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2)) ∨
    (EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
      EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2 ∧
      BitVec.ult (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1)) ∨
    (EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
      EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2 ∧
      EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1 ∧
      ¬ BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) := by
  have hge_ult : ¬ BitVec.ult r n := (mulModReduceRemGE_iff_not_ult r n).1 hge
  by_cases h3_gt : BitVec.ult (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3)
  · exact Or.inl h3_gt
  · by_cases h3_lt : BitVec.ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3)
    · have hlt := (mulModReduceRemLT_iff_ult r n).1 (mulModReduceRemLT_of_limb3_lt r n h3_lt)
      exact False.elim (hge_ult hlt)
    · have h3_eq := word_eq_of_not_ult_not_ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3) h3_lt h3_gt
      by_cases h2_gt : BitVec.ult (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2)
      · exact Or.inr (Or.inl ⟨h3_eq, h2_gt⟩)
      · by_cases h2_lt : BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)
        · have hlt := (mulModReduceRemLT_iff_ult r n).1 (mulModReduceRemLT_of_limb2_lt r n h3_eq h2_lt)
          exact False.elim (hge_ult hlt)
        · have h2_eq := word_eq_of_not_ult_not_ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2) h2_lt h2_gt
          by_cases h1_gt : BitVec.ult (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1)
          · exact Or.inr (Or.inr (Or.inl ⟨h3_eq, h2_eq, h1_gt⟩))
          · by_cases h1_lt : BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)
            · have hlt := (mulModReduceRemLT_iff_ult r n).1 (mulModReduceRemLT_of_limb1_lt r n h3_eq h2_eq h1_lt)
              exact False.elim (hge_ult hlt)
            · have h1_eq := word_eq_of_not_ult_not_ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1) h1_lt h1_gt
              by_cases h0_lt : BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)
              · have hlt := (mulModReduceRemLT_iff_ult r n).1 (mulModReduceRemLT_of_limb0_lt r n h3_eq h2_eq h1_eq h0_lt)
                exact False.elim (hge_ult hlt)
              · exact Or.inr (Or.inr (Or.inr ⟨h3_eq, h2_eq, h1_eq, h0_lt⟩))

theorem mulModReduceRemLT_cases (r n : EvmWord) (hlt : mulModReduceRemLT r n) :
    BitVec.ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3) ∨
    (EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
      BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)) ∨
    (EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
      EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2 ∧
      BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)) ∨
    (EvmWord.getLimbN r 3 = EvmWord.getLimbN n 3 ∧
      EvmWord.getLimbN r 2 = EvmWord.getLimbN n 2 ∧
      EvmWord.getLimbN r 1 = EvmWord.getLimbN n 1 ∧
      BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)) := by
  have hlt_ult : BitVec.ult r n := (mulModReduceRemLT_iff_ult r n).1 hlt
  by_cases h3_lt : BitVec.ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3)
  · exact Or.inl h3_lt
  · by_cases h3_gt : BitVec.ult (EvmWord.getLimbN n 3) (EvmWord.getLimbN r 3)
    · have hge := (mulModReduceRemGE_iff_not_ult r n).1 (mulModReduceRemGE_of_limb3_gt r n h3_gt)
      exact False.elim (hge hlt_ult)
    · have h3_eq := word_eq_of_not_ult_not_ult (EvmWord.getLimbN r 3) (EvmWord.getLimbN n 3) h3_lt h3_gt
      by_cases h2_lt : BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2)
      · exact Or.inr (Or.inl ⟨h3_eq, h2_lt⟩)
      · by_cases h2_gt : BitVec.ult (EvmWord.getLimbN n 2) (EvmWord.getLimbN r 2)
        · have hge := (mulModReduceRemGE_iff_not_ult r n).1 (mulModReduceRemGE_of_limb2_gt r n h3_eq h2_gt)
          exact False.elim (hge hlt_ult)
        · have h2_eq := word_eq_of_not_ult_not_ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2) h2_lt h2_gt
          by_cases h1_lt : BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1)
          · exact Or.inr (Or.inr (Or.inl ⟨h3_eq, h2_eq, h1_lt⟩))
          · by_cases h1_gt : BitVec.ult (EvmWord.getLimbN n 1) (EvmWord.getLimbN r 1)
            · have hge := (mulModReduceRemGE_iff_not_ult r n).1 (mulModReduceRemGE_of_limb1_gt r n h3_eq h2_eq h1_gt)
              exact False.elim (hge hlt_ult)
            · have h1_eq := word_eq_of_not_ult_not_ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1) h1_lt h1_gt
              by_cases h0_lt : BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0)
              · exact Or.inr (Or.inr (Or.inr ⟨h3_eq, h2_eq, h1_eq, h0_lt⟩))
              · have hge := (mulModReduceRemGE_iff_not_ult r n).1 (mulModReduceRemGE_of_limb0_ge r n h3_eq h2_eq h1_eq h0_lt)
                exact False.elim (hge hlt_ult)

@[irreducible] def mulModReduceSubBorrow0 (r n : EvmWord) : Word :=
  if BitVec.ult (EvmWord.getLimbN r 0) (EvmWord.getLimbN n 0) then (1 : Word) else 0

@[irreducible] def mulModReduceSubLimb0 (r n : EvmWord) : Word :=
  EvmWord.getLimbN r 0 - EvmWord.getLimbN n 0

@[irreducible] def mulModReduceSubBorrow1a (r n : EvmWord) : Word :=
  if BitVec.ult (EvmWord.getLimbN r 1) (EvmWord.getLimbN n 1) then (1 : Word) else 0

@[irreducible] def mulModReduceSubTemp1 (r n : EvmWord) : Word :=
  EvmWord.getLimbN r 1 - EvmWord.getLimbN n 1

@[irreducible] def mulModReduceSubBorrow1b (r n : EvmWord) : Word :=
  if BitVec.ult (mulModReduceSubTemp1 r n) (mulModReduceSubBorrow0 r n) then
    (1 : Word)
  else
    0

@[irreducible] def mulModReduceSubBorrow1 (r n : EvmWord) : Word :=
  mulModReduceSubBorrow1a r n ||| mulModReduceSubBorrow1b r n

@[irreducible] def mulModReduceSubLimb1 (r n : EvmWord) : Word :=
  mulModReduceSubTemp1 r n - mulModReduceSubBorrow0 r n

@[irreducible] def mulModReduceSubBorrow2a (r n : EvmWord) : Word :=
  if BitVec.ult (EvmWord.getLimbN r 2) (EvmWord.getLimbN n 2) then (1 : Word) else 0

@[irreducible] def mulModReduceSubTemp2 (r n : EvmWord) : Word :=
  EvmWord.getLimbN r 2 - EvmWord.getLimbN n 2

@[irreducible] def mulModReduceSubBorrow2b (r n : EvmWord) : Word :=
  if BitVec.ult (mulModReduceSubTemp2 r n) (mulModReduceSubBorrow1 r n) then
    (1 : Word)
  else
    0

@[irreducible] def mulModReduceSubBorrow2 (r n : EvmWord) : Word :=
  mulModReduceSubBorrow2a r n ||| mulModReduceSubBorrow2b r n

@[irreducible] def mulModReduceSubLimb2 (r n : EvmWord) : Word :=
  mulModReduceSubTemp2 r n - mulModReduceSubBorrow1 r n

@[irreducible] def mulModReduceSubTemp3 (r n : EvmWord) : Word :=
  EvmWord.getLimbN r 3 - EvmWord.getLimbN n 3

@[irreducible] def mulModReduceSubLimb3 (r n : EvmWord) : Word :=
  mulModReduceSubTemp3 r n - mulModReduceSubBorrow2 r n

theorem mulModReduceSub_getLimbN_zero (r n : EvmWord) :
    EvmWord.getLimbN (r - n) 0 = mulModReduceSubLimb0 r n := by
  have h := EvmWord.sub_borrow_chain_correct r n
  rcases h with ⟨h0, _h1, _h2, _h3⟩
  unfold mulModReduceSubLimb0
  rw [show EvmWord.getLimbN (r - n) 0 = EvmWord.getLimb (r - n) 0 by
    simp [EvmWord.getLimbN]]
  rw [h0]
  simp [EvmWord.getLimb_as_getLimbN_0]

theorem mulModReduceSub_getLimbN_one (r n : EvmWord) :
    EvmWord.getLimbN (r - n) 1 = mulModReduceSubLimb1 r n := by
  have h := EvmWord.sub_borrow_chain_correct r n
  rcases h with ⟨_h0, h1, _h2, _h3⟩
  unfold mulModReduceSubLimb1 mulModReduceSubTemp1 mulModReduceSubBorrow0
  rw [show EvmWord.getLimbN (r - n) 1 = EvmWord.getLimb (r - n) 1 by
    simp [EvmWord.getLimbN]]
  rw [h1]
  simp [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1]

theorem mulModReduceSub_getLimbN_two (r n : EvmWord) :
    EvmWord.getLimbN (r - n) 2 = mulModReduceSubLimb2 r n := by
  have h := EvmWord.sub_borrow_chain_correct r n
  rcases h with ⟨_h0, _h1, h2, _h3⟩
  unfold mulModReduceSubLimb2 mulModReduceSubTemp2 mulModReduceSubBorrow1
    mulModReduceSubBorrow1a mulModReduceSubBorrow1b mulModReduceSubTemp1
    mulModReduceSubBorrow0
  rw [show EvmWord.getLimbN (r - n) 2 = EvmWord.getLimb (r - n) 2 by
    simp [EvmWord.getLimbN]]
  rw [h2]
  simp [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2]

theorem mulModReduceSub_getLimbN_three (r n : EvmWord) :
    EvmWord.getLimbN (r - n) 3 = mulModReduceSubLimb3 r n := by
  have h := EvmWord.sub_borrow_chain_correct r n
  rcases h with ⟨_h0, _h1, _h2, h3⟩
  unfold mulModReduceSubLimb3 mulModReduceSubTemp3 mulModReduceSubBorrow2
    mulModReduceSubBorrow2a mulModReduceSubBorrow2b mulModReduceSubTemp2
    mulModReduceSubBorrow1 mulModReduceSubBorrow1a mulModReduceSubBorrow1b
    mulModReduceSubTemp1 mulModReduceSubBorrow0
  rw [show EvmWord.getLimbN (r - n) 3 = EvmWord.getLimb (r - n) 3 by
    simp [EvmWord.getLimbN]]
  rw [h3]
  simp [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]

end EvmAsm.Evm64
