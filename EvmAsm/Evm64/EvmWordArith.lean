/-
  EvmAsm.Evm64.EvmWordArith

  Mathematical correctness lemmas connecting limb-level computations
  to 256-bit EvmWord operations. Used by stack-level specs.
-/

import EvmAsm.Evm64.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Shared helpers
-- ============================================================================

private theorem bv_or_eq_zero {n : Nat} {x y : BitVec n} (h : x ||| y = 0) :
    x = 0 ∧ y = 0 :=
  BitVec.or_eq_zero_iff.mp h

private theorem ult_one_eq_zero {x : Word} : BitVec.ult x 1 ↔ x = 0 := by
  constructor
  · intro h
    have h1 := of_decide_eq_true h
    change x.toNat < (1 : Word).toNat at h1
    have : (1 : Word).toNat = 1 := by native_decide
    have : x.toNat = 0 := by omega
    have : (0 : Word).toNat = 0 := by native_decide
    exact BitVec.eq_of_toNat_eq (by omega)
  · intro h; subst h; native_decide

private theorem xor_eq_zero_imp {n : Nat} {x y : BitVec n} (h : x ^^^ y = 0) : x = y :=
  BitVec.xor_eq_zero_iff.mp h

-- OR of two borrow/carry flags (0-or-1 valued bitvectors)
private theorem borrow_or_iff (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    ((if c1 then (1 : Word) else 0) ||| (if c2 then (1 : Word) else 0)) =
    (if (c1 ∨ c2) then (1 : Word) else 0) := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp_all

-- The toNat decomposition of a 256-bit value into 4 limbs.
private theorem toNat_eq_limb_sum (v : EvmWord) :
    v.toNat = (v.getLimb 0).toNat + (v.getLimb 1).toNat * 2^64 +
              (v.getLimb 2).toNat * 2^128 + (v.getLimb 3).toNat * 2^192 := by
  simp only [getLimb, BitVec.extractLsb'_toNat,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
    Nat.zero_mul, Nat.shiftRight_zero]
  have hv := v.isLt  -- v.toNat < 2^256
  omega

-- getLimb as toNat division
private theorem getLimb_toNat_eq (v : EvmWord) (i : Fin 4) :
    (v.getLimb i).toNat = (v.toNat / 2 ^ (i.val * 64)) % 2 ^ 64 := by
  simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

-- BitVec.ult ↔ toNat comparison
private theorem ult_iff {n : Nat} (x y : BitVec n) : BitVec.ult x y ↔ x.toNat < y.toNat :=
  ⟨fun h => BitVec.lt_def.mp (of_decide_eq_true h),
   fun h => decide_eq_true (BitVec.lt_def.mpr h)⟩

-- ============================================================================
-- ISZERO correctness
-- ============================================================================

theorem iszero_or_reduce_correct (a : EvmWord) :
    (if BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1
     then (1 : Word) else 0) =
    (if a = 0 then (1 : Word) else 0) := by
  suffices h : BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1 ↔ a = 0 by
    by_cases ha : a = 0 <;> simp_all
  constructor
  · intro h
    have hor := ult_one_eq_zero.mp h
    have h12 := bv_or_eq_zero (show (a.getLimb 0 ||| a.getLimb 1) ||| (a.getLimb 2 ||| a.getLimb 3) = 0 by
      rw [BitVec.or_assoc] at hor; exact hor)
    exact (eq_zero_iff_limbs a).mpr
      ⟨(bv_or_eq_zero h12.1).1, (bv_or_eq_zero h12.1).2,
       (bv_or_eq_zero h12.2).1, (bv_or_eq_zero h12.2).2⟩
  · intro h; subst h; exact ult_one_eq_zero.mpr rfl

-- ============================================================================
-- EQ correctness
-- ============================================================================

theorem eq_xor_or_reduce_correct (a b : EvmWord) :
    let acc0 := a.getLimb 0 ^^^ b.getLimb 0
    let acc1 := acc0 ||| (a.getLimb 1 ^^^ b.getLimb 1)
    let acc2 := acc1 ||| (a.getLimb 2 ^^^ b.getLimb 2)
    let acc3 := acc2 ||| (a.getLimb 3 ^^^ b.getLimb 3)
    (if BitVec.ult acc3 1 then (1 : Word) else 0) =
    (if a = b then (1 : Word) else 0) := by
  intro acc0; intro acc1; intro acc2; intro acc3
  suffices h : BitVec.ult acc3 1 ↔ a = b by
    by_cases hab : a = b <;> simp_all
  constructor
  · intro h
    have hacc : acc3 = 0 := ult_one_eq_zero.mp h
    have hacc_flat : (a.getLimb 0 ^^^ b.getLimb 0) ||| (a.getLimb 1 ^^^ b.getLimb 1) |||
                     (a.getLimb 2 ^^^ b.getLimb 2) ||| (a.getLimb 3 ^^^ b.getLimb 3) = 0 := by
      show acc3 = 0; exact hacc
    have h12 := bv_or_eq_zero (show ((a.getLimb 0 ^^^ b.getLimb 0) ||| (a.getLimb 1 ^^^ b.getLimb 1)) |||
        ((a.getLimb 2 ^^^ b.getLimb 2) ||| (a.getLimb 3 ^^^ b.getLimb 3)) = 0 by
      rw [BitVec.or_assoc] at hacc_flat; exact hacc_flat)
    calc a = fromLimbs a.getLimb := (fromLimbs_getLimb a).symm
      _ = fromLimbs b.getLimb := by unfold fromLimbs; simp only [
            xor_eq_zero_imp (bv_or_eq_zero h12.1).1, xor_eq_zero_imp (bv_or_eq_zero h12.1).2,
            xor_eq_zero_imp (bv_or_eq_zero h12.2).1, xor_eq_zero_imp (bv_or_eq_zero h12.2).2]
      _ = b := fromLimbs_getLimb b
  · intro h; subst h
    show BitVec.ult ((((a.getLimb 0 ^^^ a.getLimb 0) |||
      (a.getLimb 1 ^^^ a.getLimb 1)) |||
      (a.getLimb 2 ^^^ a.getLimb 2)) |||
      (a.getLimb 3 ^^^ a.getLimb 3)) 1
    simp [BitVec.xor_self, BitVec.ult]

-- ============================================================================
-- LT correctness: borrow chain = unsigned less-than
-- ============================================================================

-- Single-step borrow lemma: borrow condition ↔ multi-limb comparison.
-- M is the positional multiplier (2^64 at step 1, 2^128 at step 2, 2^192 at step 3).
-- aH, bH are single limbs (< 2^64). aLo, bLo are partial sums (< M).
private theorem borrow_step_iff (M : Nat)
    {aH bH : Nat} (_haH : aH < 2^64) (_hbH : bH < 2^64)
    {aLo bLo : Nat} (haLo : aLo < M) (hbLo : bLo < M) :
    (aH < bH ∨ (aH + 2^64 - bH) % 2^64 < (if aLo < bLo then 1 else 0)) ↔
    (aLo + aH * M < bLo + bH * M) := by
  constructor
  · intro h; rcases h with h1 | h2
    · nlinarith [Nat.mul_le_mul_right M (show aH + 1 ≤ bH by omega)]
    · split at h2
      · have : (aH + 2^64 - bH) % 2^64 = 0 := by omega
        have : aH + 2^64 - bH < 2 * 2^64 := by omega
        have heq : aH = bH := by omega
        subst heq; omega
      · omega
  · intro h
    by_cases hcmp : aH < bH
    · left; exact hcmp
    · right
      have heq : aH = bH := by
        nlinarith [Nat.mul_le_mul_right M (show bH + 1 ≤ aH + 1 by omega)]
      subst heq
      have hlt : aLo < bLo := by omega
      simp [hlt]

set_option maxHeartbeats 400000 in
theorem lt_borrow_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    borrow3 = if BitVec.ult a b then (1 : Word) else 0 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3
  intro borrow0 borrow1a temp1 borrow1b borrow1
  intro borrow2a temp2 borrow2b borrow2
  intro borrow3a temp3 borrow3b borrow3
  -- Step 1: borrow0 tracks 1-limb comparison
  have hb0_nat : borrow0.toNat = if a0.toNat < b0.toNat then 1 else 0 := by
    simp only [borrow0]; split
    · rename_i h; rw [if_pos ((ult_iff _ _).mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h ((ult_iff _ _).mpr hlt))]; rfl
  -- Step 2: borrow1 tracks 2-limb comparison
  have hb1_or : borrow1 = if (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp1_nat : temp1.toNat = (a1.toNat + 2^64 - b1.toNat) % 2^64 := by
    simp only [temp1, BitVec.toNat_sub]; congr 1; omega
  have hb1_cond : (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0) ↔
      (a0.toNat + a1.toNat * 2^64 < b0.toNat + b1.toNat * 2^64) := by
    rw [show BitVec.ult a1 b1 ↔ a1.toNat < b1.toNat from ult_iff _ _,
        show BitVec.ult temp1 borrow0 ↔ temp1.toNat < borrow0.toNat from ult_iff _ _,
        htemp1_nat, hb0_nat]
    exact borrow_step_iff (2^64) a1.isLt b1.isLt a0.isLt b0.isLt
  have hb1_nat : borrow1.toNat = if (a0.toNat + a1.toNat * 2^64 <
      b0.toNat + b1.toNat * 2^64) then 1 else 0 := by
    rw [hb1_or]; split
    · rename_i h; rw [if_pos (hb1_cond.mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h (hb1_cond.mpr hlt))]; rfl
  -- Step 3: borrow2 tracks 3-limb comparison
  have hb2_or : borrow2 = if (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp2_nat : temp2.toNat = (a2.toNat + 2^64 - b2.toNat) % 2^64 := by
    simp only [temp2, BitVec.toNat_sub]; congr 1; omega
  have hb2_cond : (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1) ↔
      (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
       b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) := by
    rw [show BitVec.ult a2 b2 ↔ a2.toNat < b2.toNat from ult_iff _ _,
        show BitVec.ult temp2 borrow1 ↔ temp2.toNat < borrow1.toNat from ult_iff _ _,
        htemp2_nat, hb1_nat]
    have ha_bound : a0.toNat + a1.toNat * 2^64 < 2^128 := by
      have := a0.isLt; have := a1.isLt; nlinarith
    have hb_bound : b0.toNat + b1.toNat * 2^64 < 2^128 := by
      have := b0.isLt; have := b1.isLt; nlinarith
    convert borrow_step_iff (2^128) a2.isLt b2.isLt ha_bound hb_bound using 2
  have hb2_nat : borrow2.toNat = if (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
      b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) then 1 else 0 := by
    rw [hb2_or]; split
    · rename_i h; rw [if_pos (hb2_cond.mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h (hb2_cond.mpr hlt))]; rfl
  -- Step 4: borrow3 tracks full 4-limb comparison
  have hb3_or : borrow3 = if (BitVec.ult a3 b3 ∨ BitVec.ult temp3 borrow2)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp3_nat : temp3.toNat = (a3.toNat + 2^64 - b3.toNat) % 2^64 := by
    simp only [temp3, BitVec.toNat_sub]; congr 1; omega
  have hb3_cond : (BitVec.ult a3 b3 ∨ BitVec.ult temp3 borrow2) ↔
      (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 <
       b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192) := by
    rw [show BitVec.ult a3 b3 ↔ a3.toNat < b3.toNat from ult_iff _ _,
        show BitVec.ult temp3 borrow2 ↔ temp3.toNat < borrow2.toNat from ult_iff _ _,
        htemp3_nat, hb2_nat]
    have ha_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 < 2^192 := by
      have := a0.isLt; have := a1.isLt; have := a2.isLt; nlinarith
    have hb_bound : b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 < 2^192 := by
      have := b0.isLt; have := b1.isLt; have := b2.isLt; nlinarith
    convert borrow_step_iff (2^192) a3.isLt b3.isLt ha_bound hb_bound using 2
  -- Final: connect borrow3 to BitVec.ult a b
  have hfinal : (BitVec.ult a3 b3 ∨ BitVec.ult temp3 borrow2) ↔ BitVec.ult a b := by
    constructor
    · intro h; rw [ult_iff, toNat_eq_limb_sum a, toNat_eq_limb_sum b]; exact hb3_cond.mp h
    · intro h; rw [ult_iff, toNat_eq_limb_sum a, toNat_eq_limb_sum b] at h; exact hb3_cond.mpr h
  rw [hb3_or]; split
  · rename_i h; rw [if_pos (hfinal.mp h)]
  · rename_i h; rw [if_neg (fun hab => h (hfinal.mpr hab))]

-- ============================================================================
-- ADD correctness: carry chain produces (a + b) limbs
-- ============================================================================

-- Carry from 64-bit addition: (if ult (a+b) b then 1 else 0).toNat = (a.toNat + b.toNat) / 2^64
private theorem carry_toNat (x y : Word) :
    (if BitVec.ult (x + y) y then (1 : Word) else 0).toNat =
    (x.toNat + y.toNat) / 2^64 := by
  have hx := x.isLt; have hy := y.isLt
  have hsum : (x + y).toNat = (x.toNat + y.toNat) % 2^64 := BitVec.toNat_add x y
  split
  · rename_i h; have := (ult_iff _ _).mp h; rw [hsum] at this
    simp [BitVec.toNat_ofNat]; omega
  · rename_i h; have := mt (ult_iff _ _).mpr h; rw [hsum] at this; push_neg at this
    simp [BitVec.toNat_ofNat]; omega

-- OR of two {0,1}-valued Words
private theorem or_01_toNat (x y : Word) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    (x ||| y).toNat = min 1 (x.toNat + y.toNat) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> native_decide

-- {0,1} fact for if-then-else
private theorem ite_word_01 (c : Prop) [Decidable c] :
    (if c then (1 : Word) else 0) = 0 ∨ (if c then (1 : Word) else 0) = 1 := by
  split <;> simp

-- Combined carry: (carry_a ||| carry_b).toNat = (a + b + cin) / 2^64
set_option maxHeartbeats 400000 in
private theorem combined_carry_toNat (x y cin : Word) (hcin : cin.toNat ≤ 1) :
    let psum := x + y
    let ca := if BitVec.ult psum y then (1 : Word) else 0
    let res := psum + cin
    let cb := if BitVec.ult res cin then (1 : Word) else 0
    (ca ||| cb).toNat = (x.toNat + y.toNat + cin.toNat) / 2^64 := by
  intro psum ca res cb
  have hx := x.isLt; have hy := y.isLt
  have hca : ca.toNat = (x.toNat + y.toNat) / 2^64 := carry_toNat x y
  have hpsum : psum.toNat = (x.toNat + y.toNat) % 2^64 := BitVec.toNat_add x y
  have hcb : cb.toNat = (psum.toNat + cin.toNat) / 2^64 := carry_toNat psum cin
  rw [or_01_toNat ca cb (ite_word_01 _) (ite_word_01 _), hca, hcb, hpsum]
  have : (x.toNat + y.toNat) % 2^64 < 2^64 := Nat.mod_lt _ (by omega)
  omega

set_option maxHeartbeats 800000 in
/-- Each limb of a + b equals the carry-chain result at that limb position. -/
theorem add_carry_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let result3 := psum3 + carry2
    (a + b).getLimb 0 = sum0 ∧
    (a + b).getLimb 1 = result1 ∧
    (a + b).getLimb 2 = result2 ∧
    (a + b).getLimb 3 = result3 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3
  intro sum0 carry0 psum1 carry1a result1 carry1b carry1
  intro psum2 carry2a result2 carry2b carry2
  intro psum3 result3
  -- toNat of carry chain
  have hc0 : carry0.toNat = (a0.toNat + b0.toNat) / 2^64 := carry_toNat a0 b0
  have hc0_le : carry0.toNat ≤ 1 := by
    have := a0.isLt; have := b0.isLt; rw [hc0]; omega
  have hc1 : carry1.toNat = (a1.toNat + b1.toNat + carry0.toNat) / 2^64 :=
    combined_carry_toNat a1 b1 carry0 hc0_le
  have hc1_le : carry1.toNat ≤ 1 := by
    have := a1.isLt; have := b1.isLt; rw [hc1]; omega
  have hc2 : carry2.toNat = (a2.toNat + b2.toNat + carry1.toNat) / 2^64 :=
    combined_carry_toNat a2 b2 carry1 hc1_le
  have hc2_le : carry2.toNat ≤ 1 := by
    have := a2.isLt; have := b2.isLt; rw [hc2]; omega
  -- toNat decomposition using local def names (a0, a1, ... not a.getLimb i)
  have hab : (a + b).toNat = (a.toNat + b.toNat) % 2^256 := BitVec.toNat_add a b
  -- Use toNat_eq_limb_sum but since a0 := a.getLimb 0 etc., types match
  have ha : a.toNat = a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 :=
    toNat_eq_limb_sum a
  have hb : b.toNat = b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192 :=
    toNat_eq_limb_sum b
  -- Abbreviate the full sum
  set S := a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 +
           (b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192)
  have hS : (a + b).toNat = S % 2^256 := by rw [hab, ha, hb]
  -- limb bounds
  have ha0 := a0.isLt; have hb0 := b0.isLt
  have ha1 := a1.isLt; have hb1 := b1.isLt
  have ha2 := a2.isLt; have hb2 := b2.isLt
  have ha3 := a3.isLt; have hb3 := b3.isLt
  -- getLimb toNat for (a+b) at each index
  have key0 : ((a + b).getLimb 0).toNat = S % 2^256 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hS]; norm_num
  have key1 : ((a + b).getLimb 1).toNat = S % 2^256 / 2^64 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hS]; norm_num
  have key2 : ((a + b).getLimb 2).toNat = S % 2^256 / 2^128 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hS]; norm_num
  have key3 : ((a + b).getLimb 3).toNat = S % 2^256 / 2^192 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      show (3 : Fin 4).val = 3 from rfl]; rw [hS]
  -- Factor S at each limb boundary using ring, then omega handles div/mod
  set W := (2 : Nat) ^ 64
  have hW : 0 < W := by positivity
  have h128 : (2:Nat)^128 = W * W := by norm_num [W]
  have h192 : (2:Nat)^192 = W * (W * W) := by norm_num [W]
  have h256 : (2:Nat)^256 = W * (W * (W * W)) := by norm_num [W]
  -- Factor S for division at each boundary
  have hS0 : S = (a0.toNat + b0.toNat) +
    ((a1.toNat + b1.toNat) + (a2.toNat + b2.toNat) * W + (a3.toNat + b3.toNat) * (W * W)) * W := by
    simp only [S, h128, h192]; ring
  have hS1 : S = (a0.toNat + b0.toNat) + (a1.toNat + b1.toNat) * W +
    ((a2.toNat + b2.toNat) + (a3.toNat + b3.toNat) * W) * (W * W) := by
    simp only [S, h128, h192]; ring
  have hS2 : S = (a0.toNat + b0.toNat) + (a1.toNat + b1.toNat) * W +
    (a2.toNat + b2.toNat) * (W * W) + (a3.toNat + b3.toNat) * (W * (W * W)) := by
    simp only [S, h128, h192]; ring
  -- Helpers: strip W-multiples from mod W
  have strip4 : ∀ p q r s W, 0 < W →
      (p + (q + r * W + s * (W * W))) % W = (p + q) % W := by
    intro p q r s W hW'
    rw [show p + (q + r * W + s * (W * W)) = (p + q) + (r + s * W) * W from by ring,
        Nat.add_mul_mod_self_right]
  have strip2 : ∀ (p q r W : Nat), (p + (q + r * W)) % W = (p + q) % W := by
    intro p q r W
    rw [show p + (q + r * W) = (p + q) + r * W from by ring, Nat.add_mul_mod_self_right]
  -- Limb 0
  constructor
  · apply BitVec.eq_of_toNat_eq; rw [key0, BitVec.toNat_add, h256]; lia
  -- Limb 1
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [key1, BitVec.toNat_add, BitVec.toNat_add, hc0, h256]
    -- Goal: S % (W*(W*(W*W))) / W % W = ((a1'+b1') % W + (a0'+b0') / W) % W
    -- Use: S % W^4 / W % W = S / W % W, then factor S / W
    rw [show (2:Nat)^64 = W from rfl, Nat.mod_mul_right_div_self]
    -- Goal: S / W % (W * (W * W)) % W = ((a1'+b1') % W + (a0'+b0') / W) % W
    rw [hS0, Nat.add_mul_div_right _ _ hW, Nat.mod_mul_right_mod]
    rw [strip4 _ _ _ _ _ hW]
    -- Goal: (c0 + (a1'+b1')) % W = ((a1'+b1') % W + c0) % W
    have hc0_lt : (a0.toNat + b0.toNat) / W < W := by omega
    rw [Nat.add_comm ((a0.toNat + b0.toNat) / W), Nat.add_mod,
        Nat.mod_eq_of_lt hc0_lt]
  -- Limb 2
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [key2, h128, h256,
        show W * (W * (W * W)) = (W * W) * (W * W) from by ring,
        Nat.mod_mul_right_div_self]
    -- Goal: S / (W*W) % (W*W) % W = result2.toNat
    -- Goal: S / (W*W) % (W*W) % W = result2.toNat
    rw [Nat.mod_mul_right_mod]
    -- Goal: S / (W*W) % W = result2.toNat
    rw [hS1, Nat.add_mul_div_right _ _ (show 0 < W * W by positivity)]
    -- Strip higher terms from mod W
    rw [strip2]
    -- Goal: ((a0'+b0' + (a1'+b1')*W) / (W*W) + (a2'+b2')) % W = result2.toNat
    -- Decompose the 2-limb carry
    rw [show W * W = W * W from rfl, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right _ _ hW, ← hc0,
        show carry0.toNat + (a1.toNat + b1.toNat) = a1.toNat + b1.toNat + carry0.toNat from by omega]
    rw [BitVec.toNat_add, BitVec.toNat_add, hc1, show (2:Nat)^64 = W from rfl]
    have hc1_lt : (a1.toNat + b1.toNat + carry0.toNat) / W < W := by omega
    rw [Nat.add_comm (((a1.toNat + b1.toNat + carry0.toNat) / W)),
        Nat.add_mod, Nat.mod_eq_of_lt hc1_lt]
  -- Limb 3
  · apply BitVec.eq_of_toNat_eq
    rw [key3, h192, h256,
        show W * (W * (W * W)) = (W * (W * W)) * W from by ring,
        Nat.mod_mul_right_div_self]
    -- Goal: S / (W*(W*W)) % W % W = result3.toNat
    rw [Nat.mod_mod]
    -- Goal: S / (W*(W*W)) % W = result3.toNat
    rw [hS2]
    -- S = low3 + (a3'+b3') * (W*(W*W))
    rw [Nat.add_mul_div_right _ _ (show 0 < W * (W * W) by positivity)]
    -- Goal: (low3 / (W*(W*W)) + (a3'+b3')) % W = result3.toNat
    -- Prove that low3 / (W*(W*W)) = carry2.toNat
    have hlow3_div : (a0.toNat + b0.toNat + (a1.toNat + b1.toNat) * W +
        (a2.toNat + b2.toNat) * (W * W)) / (W * (W * W)) =
        carry2.toNat := by
      -- Convert / (W*(W*W)) to three successive / W using div_div_eq_div_mul
      have hdiv3 : ∀ (a : Nat), a / (W * (W * W)) = a / W / W / W := by
        intro a; rw [show W * (W * W) = W * W * W from by ring,
          ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      rw [hdiv3]
      -- Step 1: / W using hS factoring
      rw [show ∀ (p q r : Nat), p + q * W + r * (W * W) = p + (q + r * W) * W from by intros; ring,
          Nat.add_mul_div_right _ _ hW]
      -- After step 1: ((a0'+b0')/W + (a1'+b1') + (a2'+b2')*W) / W / W
      -- Step 2: factor for another / W
      conv_lhs => rw [show ∀ (p q r : Nat), p + (q + r * W) = (p + q) + r * W from by intros; ring]
      rw [Nat.add_mul_div_right _ _ hW]
      -- Step 3: last / W
      rw [← hc0, show carry0.toNat + (a1.toNat + b1.toNat) =
          a1.toNat + b1.toNat + carry0.toNat from by omega, ← hc1,
          show carry1.toNat + (a2.toNat + b2.toNat) =
          a2.toNat + b2.toNat + carry1.toNat from by omega, ← hc2]
    rw [hlow3_div]
    rw [BitVec.toNat_add, BitVec.toNat_add, hc2, show (2:Nat)^64 = W from rfl]
    have hc2_lt : (a2.toNat + b2.toNat + carry1.toNat) / W < W := by omega
    rw [Nat.add_comm (((a2.toNat + b2.toNat + carry1.toNat) / W)),
        Nat.add_mod, Nat.mod_eq_of_lt hc2_lt]

-- ============================================================================
-- SUB correctness: borrow chain produces (a - b) limbs
-- ============================================================================

/-- Helper: subtraction of a single limb with borrow produces the right toNat value. -/
private theorem sub_limb_toNat {a_limb b_limb borrow : Word}
    (hborrow : borrow.toNat = 0 ∨ borrow.toNat = 1) :
    (a_limb - b_limb - borrow).toNat =
    (a_limb.toNat + 2^64 - b_limb.toNat + 2^64 - borrow.toNat) % 2^64 := by
  simp only [BitVec.toNat_sub]
  have ha := a_limb.isLt
  have hb := b_limb.isLt
  rcases hborrow with h | h <;> simp only [h] <;> omega

/-- Helper: borrow flag value is 0 or 1. -/
private theorem borrow_val_01 {c : Prop} [Decidable c] :
    (if c then (1 : Word) else (0 : Word)).toNat = 0 ∨
    (if c then (1 : Word) else (0 : Word)).toNat = 1 := by
  by_cases h : c <;> simp [h]

/-- Helper: OR of two borrow flags is 0 or 1. -/
private theorem borrow_or_val_01 {c1 c2 : Prop} [Decidable c1] [Decidable c2] :
    ((if c1 then (1 : Word) else 0) ||| (if c2 then (1 : Word) else 0)).toNat = 0 ∨
    ((if c1 then (1 : Word) else 0) ||| (if c2 then (1 : Word) else 0)).toNat = 1 := by
  rw [borrow_or_iff]
  exact borrow_val_01

set_option maxHeartbeats 800000 in
/-- Each limb of a - b equals the borrow-chain result at that limb position. -/
theorem sub_borrow_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let diff0 := a0 - b0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let result1 := temp1 - borrow0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let result2 := temp2 - borrow1
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    (a - b).getLimb 0 = diff0 ∧
    (a - b).getLimb 1 = result1 ∧
    (a - b).getLimb 2 = result2 ∧
    (a - b).getLimb 3 = result3 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3
  intro borrow0 diff0
  intro borrow1a temp1 borrow1b result1 borrow1
  intro borrow2a temp2 borrow2b result2 borrow2
  intro _borrow3a temp3 _borrow3b result3
  -- Key: (a - b).toNat = (a.toNat + 2^256 - b.toNat) % 2^256
  have hS : (a - b).toNat = (a.toNat + 2^256 - b.toNat) % 2^256 := by
    simp only [BitVec.toNat_sub]; congr 1; omega
  -- Borrow flag toNat values
  have hb0_nat : borrow0.toNat = if a0.toNat < b0.toNat then 1 else 0 := by
    simp only [borrow0]; split
    · rename_i h; rw [if_pos ((ult_iff _ _).mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h ((ult_iff _ _).mpr hlt))]; rfl
  -- borrow0 is 0 or 1
  have hb0_01 : borrow0.toNat = 0 ∨ borrow0.toNat = 1 := by
    rw [hb0_nat]; split <;> simp
  -- borrow1 tracks 2-limb comparison (reuse from LT proof pattern)
  have hb1_or : borrow1 = if (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp1_nat : temp1.toNat = (a1.toNat + 2^64 - b1.toNat) % 2^64 := by
    simp only [temp1, BitVec.toNat_sub]; congr 1; omega
  have hb1_cond : (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0) ↔
      (a0.toNat + a1.toNat * 2^64 < b0.toNat + b1.toNat * 2^64) := by
    rw [show BitVec.ult a1 b1 ↔ a1.toNat < b1.toNat from ult_iff _ _,
        show BitVec.ult temp1 borrow0 ↔ temp1.toNat < borrow0.toNat from ult_iff _ _,
        htemp1_nat, hb0_nat]
    exact borrow_step_iff (2^64) a1.isLt b1.isLt a0.isLt b0.isLt
  have hb1_nat : borrow1.toNat = if (a0.toNat + a1.toNat * 2^64 <
      b0.toNat + b1.toNat * 2^64) then 1 else 0 := by
    rw [hb1_or]; split
    · rename_i h; rw [if_pos (hb1_cond.mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h (hb1_cond.mpr hlt))]; rfl
  have hb1_01 : borrow1.toNat = 0 ∨ borrow1.toNat = 1 := by
    rw [hb1_nat]; split <;> simp
  -- borrow2 tracks 3-limb comparison
  have hb2_or : borrow2 = if (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1)
      then (1 : Word) else 0 := borrow_or_iff _ _
  have htemp2_nat : temp2.toNat = (a2.toNat + 2^64 - b2.toNat) % 2^64 := by
    simp only [temp2, BitVec.toNat_sub]; congr 1; omega
  have hb2_cond : (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1) ↔
      (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
       b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) := by
    rw [show BitVec.ult a2 b2 ↔ a2.toNat < b2.toNat from ult_iff _ _,
        show BitVec.ult temp2 borrow1 ↔ temp2.toNat < borrow1.toNat from ult_iff _ _,
        htemp2_nat, hb1_nat]
    have ha_bound : a0.toNat + a1.toNat * 2^64 < 2^128 := by
      have := a0.isLt; have := a1.isLt; nlinarith
    have hb_bound : b0.toNat + b1.toNat * 2^64 < 2^128 := by
      have := b0.isLt; have := b1.isLt; nlinarith
    convert borrow_step_iff (2^128) a2.isLt b2.isLt ha_bound hb_bound using 2
  have hb2_nat : borrow2.toNat = if (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
      b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) then 1 else 0 := by
    rw [hb2_or]; split
    · rename_i h; rw [if_pos (hb2_cond.mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h (hb2_cond.mpr hlt))]; rfl
  have hb2_01 : borrow2.toNat = 0 ∨ borrow2.toNat = 1 := by
    rw [hb2_nat]; split <;> simp
  -- Now prove each limb
  -- Useful bounds
  have ha0 := a0.isLt; have hb0' := b0.isLt
  have ha1 := a1.isLt; have hb1' := b1.isLt
  have ha2 := a2.isLt; have hb2' := b2.isLt
  have ha3 := a3.isLt; have hb3' := b3.isLt
  have ha_sum := toNat_eq_limb_sum a
  have hb_sum := toNat_eq_limb_sum b
  have hab_lt : b.toNat < 2^256 := b.isLt
  have hab_le : b.toNat ≤ a.toNat + 2^256 := by omega
  -- diff0 toNat
  have hdiff0_nat : diff0.toNat = (a0.toNat + 2^64 - b0.toNat) % 2^64 := by
    simp only [diff0, BitVec.toNat_sub]; congr 1; omega
  -- result1 toNat
  have hresult1_nat : result1.toNat =
      (a1.toNat + 2^64 - b1.toNat + 2^64 - borrow0.toNat) % 2^64 := by
    exact sub_limb_toNat hb0_01
  -- result2 toNat
  have hresult2_nat : result2.toNat =
      (a2.toNat + 2^64 - b2.toNat + 2^64 - borrow1.toNat) % 2^64 := by
    exact sub_limb_toNat hb1_01
  -- result3 toNat
  have hresult3_nat : result3.toNat =
      (a3.toNat + 2^64 - b3.toNat + 2^64 - borrow2.toNat) % 2^64 := by
    exact sub_limb_toNat hb2_01
  -- Use same W-factoring approach as ADD
  set W := (2 : Nat) ^ 64
  have hW : 0 < W := by positivity
  have h128 : (2:Nat)^128 = W * W := by norm_num [W]
  have h192 : (2:Nat)^192 = W * (W * W) := by norm_num [W]
  have h256 : (2:Nat)^256 = W * (W * (W * W)) := by norm_num [W]
  -- Set D = a.toNat + 2^256 - b.toNat (the raw difference before mod)
  set D := a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 +
           2^256 - (b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192)
  have hD : (a - b).toNat = D % 2^256 := by rw [hS, ha_sum, hb_sum]
  -- Factor D at each boundary (like hS0..hS2 in ADD but for subtraction)
  -- D = (a0 + W - b0) + ((a1 + W - b1) + ((a2 + W - b2) + (a3 + W - b3) * W) * W) * W - 3*W
  -- This is more complex than ADD because of the borrows. Instead, just use
  -- the key* lemmas + hresult*_nat and close with the toNat approach.
  -- getLimb toNat for (a-b) at each index
  have key0 : ((a - b).getLimb 0).toNat = D % 2^256 % W := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hD]; norm_num
  have key1 : ((a - b).getLimb 1).toNat = D % 2^256 / W % W := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hD]; norm_num
  have key2 : ((a - b).getLimb 2).toNat = D % 2^256 / 2^128 % W := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hD]; norm_num
  have key3 : ((a - b).getLimb 3).toNat = D % 2^256 / 2^192 % W := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      show (3 : Fin 4).val = 3 from rfl]; rw [hD]
  -- Factor D using omega (ring doesn't work for Nat subtraction)
  have hD0 : D = (a0.toNat + W - b0.toNat) +
    (a1.toNat + W - 1 - b1.toNat + (a2.toNat + W - 1 - b2.toNat +
      (a3.toNat + W - 1 - b3.toNat) * W) * W) * W := by
    simp only [D, h128, h192, h256]; omega
  have hD1 : D = (a0.toNat + W - b0.toNat) + (a1.toNat + W - 1 - b1.toNat) * W +
    (a2.toNat + W - 1 - b2.toNat + (a3.toNat + W - 1 - b3.toNat) * W) * (W * W) := by
    rw [hD0, show ∀ a b c : Nat, (a + b * c) * c = a * c + b * (c * c) from by intros; ring]
    omega
  have hD2 : D = (a0.toNat + W - b0.toNat) + (a1.toNat + W - 1 - b1.toNat) * W +
    (a2.toNat + W - 1 - b2.toNat) * (W * W) +
    (a3.toNat + W - 1 - b3.toNat) * (W * (W * W)) := by
    rw [hD1, show ∀ p a b c : Nat, p + (a + b * c) * (c * c) = p + a * (c * c) + b * (c * (c * c)) from by intros; ring]
  -- Strip helpers
  have strip4 : ∀ (p q r s W : Nat), 0 < W →
      (p + (q + r * W + s * (W * W))) % W = (p + q) % W := by
    intro p q r s W hW'; rw [show p + (q + r * W + s * (W * W)) = (p + q) + (r + s * W) * W from by ring,
      Nat.add_mul_mod_self_right]
  have strip2 : ∀ (p q r W : Nat), (p + (q + r * W)) % W = (p + q) % W := by
    intro p q r W; rw [show p + (q + r * W) = (p + q) + r * W from by ring, Nat.add_mul_mod_self_right]
  -- Complement borrow: (a0+W-b0)/W = 0 if a0<b0, 1 otherwise
  have hdiv0 : (a0.toNat + W - b0.toNat) / W = if a0.toNat < b0.toNat then 0 else 1 := by
    split
    · rename_i h; exact Nat.div_eq_of_lt (by omega)
    · rename_i h; push_neg at h
      rw [show a0.toNat + W - b0.toNat = (a0.toNat - b0.toNat) + 1 * W from by omega,
          Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt (by omega)]
  -- 2-limb complement borrow
  have hdiv1 : ((a0.toNat + W - b0.toNat) / W + (a1.toNat + W - 1 - b1.toNat)) / W =
      if a0.toNat + a1.toNat * W < b0.toNat + b1.toNat * W then 0 else 1 := by
    rw [hdiv0]; split <;> (rename_i h; split <;> rename_i h2)
    · exact Nat.div_eq_of_lt (by omega)
    · rw [show (0 + (a1.toNat + W - 1 - b1.toNat)) =
            (a1.toNat - 1 - b1.toNat) + 1 * W from by omega,
          Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt (by omega)]
    · exact Nat.div_eq_of_lt (by omega)
    · rw [show 1 + (a1.toNat + W - 1 - b1.toNat) = (a1.toNat - b1.toNat) + 1 * W from by omega,
          Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt (by omega)]
  -- 3-limb complement borrow
  have hdiv2 : (((a0.toNat + W - b0.toNat) / W + (a1.toNat + W - 1 - b1.toNat)) / W +
      (a2.toNat + W - 1 - b2.toNat)) / W =
      if a0.toNat + a1.toNat * W + a2.toNat * (W * W) <
         b0.toNat + b1.toNat * W + b2.toNat * (W * W) then 0 else 1 := by
    rw [hdiv1]; split <;> (rename_i h; split <;> rename_i h2)
    · exact Nat.div_eq_of_lt (by omega)
    · rw [show (0 + (a2.toNat + W - 1 - b2.toNat)) =
            (a2.toNat - 1 - b2.toNat) + 1 * W from by omega,
          Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt (by omega)]
    · exact Nat.div_eq_of_lt (by omega)
    · rw [show 1 + (a2.toNat + W - 1 - b2.toNat) = (a2.toNat - b2.toNat) + 1 * W from by omega,
          Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt (by omega)]
  constructor
  -- Limb 0
  · apply BitVec.eq_of_toNat_eq
    rw [key0, hdiff0_nat, h256, Nat.mod_mul_right_mod, hD0, Nat.add_mul_mod_self_right]
  constructor
  -- Limb 1
  · apply BitVec.eq_of_toNat_eq
    rw [key1, hresult1_nat, hb0_nat, h256, Nat.mod_mul_right_div_self]
    rw [hD0, Nat.add_mul_div_right _ _ hW, Nat.mod_mul_right_mod, strip2, hdiv0]
    split
    · -- a0 < b0: LHS = (0 + (a1'+W-1-b1')) % W, RHS = (a1'+W-b1'+W-1) % W
      rw [show (0 + (a1.toNat + W - 1 - b1.toNat)) = a1.toNat + W - 1 - b1.toNat from by omega,
          show a1.toNat + W - b1.toNat + W - 1 =
            (a1.toNat + W - 1 - b1.toNat) + 1 * W from by omega,
          Nat.add_mul_mod_self_right]
    · -- a0 ≥ b0: LHS = (1 + (a1'+W-1-b1')) % W, RHS = (a1'+W-b1'+W) % W
      rw [show 1 + (a1.toNat + W - 1 - b1.toNat) = a1.toNat + W - b1.toNat from by omega,
          show a1.toNat + W - b1.toNat + W - 0 =
            (a1.toNat + W - b1.toNat) + 1 * W from by omega,
          Nat.add_mul_mod_self_right]
  constructor
  -- Limb 2
  · apply BitVec.eq_of_toNat_eq
    rw [key2, hresult2_nat, hb1_nat, h128, h256,
        show W * (W * (W * W)) = (W * W) * (W * W) from by ring,
        Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
    rw [hD1, Nat.add_mul_div_right _ _ (show 0 < W * W by positivity), strip2]
    rw [show W * W = W * W from rfl, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right _ _ hW]
    rw [hdiv1]
    split
    · rw [show (0 + (a2.toNat + W - 1 - b2.toNat)) = a2.toNat + W - 1 - b2.toNat from by omega,
          show a2.toNat + W - b2.toNat + W - 1 =
            (a2.toNat + W - 1 - b2.toNat) + 1 * W from by omega,
          Nat.add_mul_mod_self_right]
    · rw [show 1 + (a2.toNat + W - 1 - b2.toNat) = a2.toNat + W - b2.toNat from by omega,
          show a2.toNat + W - b2.toNat + W - 0 =
            (a2.toNat + W - b2.toNat) + 1 * W from by omega,
          Nat.add_mul_mod_self_right]
  -- Limb 3
  · apply BitVec.eq_of_toNat_eq
    rw [key3, hresult3_nat, hb2_nat, h192, h256,
        show W * (W * (W * W)) = (W * (W * W)) * W from by ring,
        Nat.mod_mul_right_div_self, Nat.mod_mod]
    rw [hD2, Nat.add_mul_div_right _ _ (show 0 < W * (W * W) by positivity)]
    have hdiv3 : ∀ (x : Nat), x / (W * (W * W)) = x / W / W / W := by
      intro x; rw [show W * (W * W) = W * W * W from by ring,
        ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [hdiv3, show ∀ (p q r : Nat), p + q * W + r * (W * W) = p + (q + r * W) * W from by intros; ring,
        Nat.add_mul_div_right _ _ hW]
    conv_lhs => rw [show ∀ (p q r : Nat), p + (q + r * W) = (p + q) + r * W from by intros; ring]
    rw [Nat.add_mul_div_right _ _ hW]
    rw [hdiv2, ← h128]
    split
    · rw [show (0 + (a3.toNat + W - 1 - b3.toNat)) = a3.toNat + W - 1 - b3.toNat from by omega,
          show a3.toNat + W - b3.toNat + W - 1 =
            (a3.toNat + W - 1 - b3.toNat) + 1 * W from by omega,
          Nat.add_mul_mod_self_right]
    · rw [show 1 + (a3.toNat + W - 1 - b3.toNat) = a3.toNat + W - b3.toNat from by omega,
          show a3.toNat + W - b3.toNat + W - 0 =
            (a3.toNat + W - b3.toNat) + 1 * W from by omega,
          Nat.add_mul_mod_self_right]

-- ============================================================================
-- SLT correctness: signed comparison decomposition
-- ============================================================================

/-- The SLT result equals `if BitVec.slt a b then 1 else 0`. -/
theorem slt_result_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let b0 := b.getLimb 0
    let a1 := a.getLimb 1; let b1 := b.getLimb 1
    let a2 := a.getLimb 2; let b2 := b.getLimb 2
    let a3 := a.getLimb 3; let b3 := b.getLimb 3
    -- Lower 3 limbs borrow chain
    let borrow0 := if BitVec.ult a0 b0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult a1 b1 then (1 : Word) else 0
    let temp1 := a1 - b1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult a2 b2 then (1 : Word) else 0
    let temp2 := a2 - b2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    -- Signed comparison of MSB limbs
    let slt_msb := if BitVec.slt a3 b3 then (1 : Word) else 0
    let result := if a3 = b3 then borrow2 else slt_msb
    result = if BitVec.slt a b then (1 : Word) else 0 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3
  intro borrow0 borrow1a temp1 borrow1b borrow1
  intro borrow2a temp2 borrow2b borrow2
  intro slt_msb result
  -- Key: a.msb = a3.msb (bit 255 of a = bit 63 of a3 = MSB of getLimb 3)
  have hmsb_a : a.msb = a3.msb := by
    show a.getLsbD (256 - 1) = (a.extractLsb' (3 * 64) 64).getLsbD (64 - 1)
    simp [BitVec.getLsbD_extractLsb']
  have hmsb_b : b.msb = b3.msb := by
    show b.getLsbD (256 - 1) = (b.extractLsb' (3 * 64) 64).getLsbD (64 - 1)
    simp [BitVec.getLsbD_extractLsb']
  -- Get borrow2 as the 3-limb LT comparison
  -- borrow2 tracks: lower 3 limbs of a < lower 3 limbs of b
  -- This is the same borrow chain as in lt_borrow_chain_correct (first 3 limbs)
  have hborrow2_iff : borrow2 = (1 : Word) ↔
      a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
      b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 := by
    -- Same structure as lt_borrow_chain_correct steps 1-3
    have hb0_nat : borrow0.toNat = if a0.toNat < b0.toNat then 1 else 0 := by
      simp only [borrow0]; split
      · rename_i hh; rw [if_pos ((ult_iff _ _).mp hh)]; rfl
      · rename_i hh; rw [if_neg (fun hlt => hh ((ult_iff _ _).mpr hlt))]; rfl
    have hb1_cond : (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0) ↔
        (a0.toNat + a1.toNat * 2^64 < b0.toNat + b1.toNat * 2^64) := by
      rw [show BitVec.ult a1 b1 ↔ a1.toNat < b1.toNat from ult_iff _ _,
          show BitVec.ult temp1 borrow0 ↔ temp1.toNat < borrow0.toNat from ult_iff _ _]
      simp only [temp1, BitVec.toNat_sub]; rw [hb0_nat]
      convert borrow_step_iff (2^64) a1.isLt b1.isLt a0.isLt b0.isLt using 2; omega
    have hb1_nat : borrow1.toNat = if (a0.toNat + a1.toNat * 2^64 <
        b0.toNat + b1.toNat * 2^64) then 1 else 0 := by
      rw [show borrow1 = _ from borrow_or_iff _ _]; split
      · rename_i hh; rw [if_pos (hb1_cond.mp hh)]; rfl
      · rename_i hh; rw [if_neg (fun hlt => hh (hb1_cond.mpr hlt))]; rfl
    have hb2_cond : (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1) ↔
        (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
         b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) := by
      rw [show BitVec.ult a2 b2 ↔ a2.toNat < b2.toNat from ult_iff _ _,
          show BitVec.ult temp2 borrow1 ↔ temp2.toNat < borrow1.toNat from ult_iff _ _]
      simp only [temp2, BitVec.toNat_sub]; rw [hb1_nat]
      have ha_bound : a0.toNat + a1.toNat * 2^64 < 2^128 := by
        have := a0.isLt; have := a1.isLt; nlinarith
      have hb_bound : b0.toNat + b1.toNat * 2^64 < 2^128 := by
        have := b0.isLt; have := b1.isLt; nlinarith
      convert borrow_step_iff (2^128) a2.isLt b2.isLt ha_bound hb_bound using 2
      congr 1; omega
    -- borrow2 = borrow2a ||| borrow2b encodes hb2_cond
    constructor
    · intro hb2
      have hb2_or : borrow2 = if (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1)
          then (1 : Word) else 0 := borrow_or_iff _ _
      rw [hb2_or] at hb2; split at hb2
      · exact hb2_cond.mp ‹_›
      · simp at hb2
    · intro hlt
      have hb2_or : borrow2 = if (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1)
          then (1 : Word) else 0 := borrow_or_iff _ _
      rw [hb2_or, if_pos (hb2_cond.mpr hlt)]
  by_cases h : a3 = b3
  · -- MSB limbs equal
    simp only [result, h, ite_true]
    -- slt a b = ult a b (same MSB)
    have hmsb_eq : a.msb = b.msb := by rw [hmsb_a, hmsb_b, h]
    rw [show BitVec.slt a b = BitVec.ult a b from BitVec.slt_eq_ult_of_msb_eq hmsb_eq]
    -- ult a b ↔ a.toNat < b.toNat ↔ lower3(a) < lower3(b) (since a3 = b3)
    have hult_lower : BitVec.ult a b ↔
        (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
         b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) := by
      rw [ult_iff, toNat_eq_limb_sum a, toNat_eq_limb_sum b]
      have ha3b3 : a3.toNat = b3.toNat := congrArg BitVec.toNat h
      constructor <;> intro hlt <;> nlinarith
    -- borrow2 = if ult a b then 1 else 0
    rcases Decidable.em (BitVec.ult a b) with h | h
    · rw [if_pos h]; exact hborrow2_iff.mpr (hult_lower.mp h)
    · rw [if_neg h]
      have hb2_01 := borrow_or_val_01 (c1 := BitVec.ult a2 b2) (c2 := BitVec.ult temp2 borrow1)
      by_contra hne
      have hb2_eq1 : borrow2 = 1 := by
        rcases hb2_01 with h0 | h1
        · exact absurd (BitVec.eq_of_toNat_eq h0) hne
        · exact BitVec.eq_of_toNat_eq h1
      exact h (hult_lower.mpr (hborrow2_iff.mp hb2_eq1))
  · -- MSB limbs differ
    simp only [result, h, ite_false]
    -- slt a b ↔ slt a3 b3
    have hmsb_neq : a.msb ≠ b.msb ↔ a3.msb ≠ b3.msb := by rw [hmsb_a, hmsb_b]
    -- slt = msb_xor ⊕ ult for both 256-bit and 64-bit
    simp only [slt_msb]
    rw [BitVec.slt_eq_ult (x := a) (y := b), BitVec.slt_eq_ult (x := a3) (y := b3)]
    rw [hmsb_a, hmsb_b]
    -- msb terms now match. Suffices: ult a3 b3 = ult a b
    congr 1; congr 1; congr 1
    -- Goal: ult a3 b3 = ult a b (Bool equality)
    simp only [BitVec.ult, decide_eq_decide]
    rw [toNat_eq_limb_sum a, toNat_eq_limb_sum b]
    constructor
    · intro h3; nlinarith [a0.isLt, b0.isLt, a1.isLt, b1.isLt, a2.isLt, b2.isLt]
    · intro hab
      by_contra h3; push_neg at h3
      have hge : b3.toNat ≤ a3.toNat := h3
      have hne : a3.toNat ≠ b3.toNat := fun heq => h (BitVec.eq_of_toNat_eq heq)
      have hgt : a3.toNat ≥ b3.toNat + 1 := by omega
      -- a3*2^192 ≥ (b3+1)*2^192 = b3*2^192 + 2^192
      -- lower limbs < 2^192, so a.toNat ≥ a3*2^192 > b.toNat
      have := a0.isLt; have := b0.isLt; have := a1.isLt; have := b1.isLt
      have := a2.isLt; have := b2.isLt
      have h192_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 < 2^192 := by nlinarith
      have h192_bound' : b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 < 2^192 := by nlinarith
      nlinarith [Nat.mul_le_mul_right (2^192) hgt]

-- ============================================================================
-- BYTE correctness: limb-level byte extraction = 256-bit byte extraction
-- ============================================================================

/-- Extracting a byte from a 64-bit limb within a larger value gives the same
    result as extracting directly from the larger value, because the mod 2^64
    doesn't affect bytes that fit within the limb.

    Key identity: `a % 2^64 / 2^B % 256 = a / 2^B % 256` when `B + 8 ≤ 64`.
    Proof: `2^64 = 2^B * 2^(64-B)`, and `2^(64-B) ≥ 256`, so the high quotient
    `(a / 2^64) * 2^(64-B)` is a multiple of 256 and vanishes under `% 256`. -/
private theorem mod_pow64_div_mod256_eq (a B : Nat) (hB : B + 8 ≤ 64) :
    a % 2 ^ 64 / 2 ^ B % 256 = a / 2 ^ B % 256 := by
  -- a = q * 2^64 + r, and 2^64 = 2^B * 2^(64-B)
  -- So a / 2^B = q * 2^(64-B) + r / 2^B
  -- Since 2^(64-B) is a multiple of 256 (because 64-B ≥ 8),
  -- the q * 2^(64-B) term vanishes under % 256.
  set q := a / 2 ^ 64
  set r := a % 2 ^ 64
  have hr : r < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  have ha : a = q * 2 ^ 64 + r := by omega
  have h64 : (2 : Nat) ^ 64 = 2 ^ B * 2 ^ (64 - B) := by
    rw [← Nat.pow_add]; congr 1; omega
  -- a / 2^B = q * 2^(64-B) + r / 2^B
  have hdiv : a / 2 ^ B = q * 2 ^ (64 - B) + r / 2 ^ B := by
    conv_lhs => rw [ha, h64]
    rw [show q * (2 ^ B * 2 ^ (64 - B)) + r = r + 2 ^ B * (q * 2 ^ (64 - B)) from by ring]
    rw [Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ B)]
    omega
  -- 256 divides q * 2^(64-B)
  have hdvd : 256 ∣ q * 2 ^ (64 - B) := by
    refine Dvd.dvd.mul_left ?_ q
    exact ⟨2 ^ (64 - B - 8), by
      rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_add]; congr 1; omega⟩
  rw [hdiv]
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, show 256 * k + r / 2 ^ B = r / 2 ^ B + k * 256 from by omega]
  rw [Nat.add_mul_mod_self_right]

/-- The BYTE operation: limb-level byte extraction equals direct 256-bit extraction.

    For byte index `i` (0 ≤ i < 32, big-endian), the limb-level computation:
    - `limb_from_msb = i / 8`, selecting limb `3 - i/8`
    - `bit_shift = 56 - (i%8) * 8`, shift within the 64-bit limb
    - result = `(getLimb (3 - i/8) >>> bit_shift) % 256`

    equals the direct 256-bit extraction: `(x >>> ((31-i)*8)) % 256`.
    This connects the RISC-V limb-level BYTE implementation to the
    EVM-level BYTE semantics. -/
theorem byte_extract_correct (x : EvmWord) (i : Nat) (hi : i < 32) :
    let limb_idx : Fin 4 := ⟨3 - i / 8, by omega⟩
    let bit_shift := 56 - (i % 8) * 8
    ((x.getLimb limb_idx).toNat / 2 ^ bit_shift) % 256 =
    (x.toNat / 2 ^ ((31 - i) * 8)) % 256 := by
  simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  -- Goal: x.toNat / 2^((3-i/8)*64) % 2^64 / 2^(56-(i%8)*8) % 256 =
  --       x.toNat / 2^((31-i)*8) % 256
  have hshift : (3 - i / 8) * 64 + (56 - i % 8 * 8) = (31 - i) * 8 := by omega
  rw [mod_pow64_div_mod256_eq _ _ (by omega)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hshift]

end EvmWord

end EvmAsm.Rv64
