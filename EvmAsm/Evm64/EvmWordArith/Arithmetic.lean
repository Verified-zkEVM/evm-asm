/-
  EvmAsm.Evm64.EvmWordArith.Arithmetic

  ADD and SUB correctness: carry/borrow chains produce correct limbs.
-/

import EvmAsm.Evm64.EvmWordArith.Common
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- ADD correctness: carry chain produces (a + b) limbs
-- ============================================================================

-- Carry from 64-bit addition: (if ult (a+b) b then 1 else 0).toNat = (a.toNat + b.toNat) / 2^64
theorem carry_toNat {x y : Word} :
    (if BitVec.ult (x + y) y then (1 : Word) else 0).toNat =
    (x.toNat + y.toNat) / 2^64 := by
  have := x.isLt; have := y.isLt
  have hsum : (x + y).toNat = (x.toNat + y.toNat) % 2^64 := BitVec.toNat_add x y
  split
  · rename_i h; have := (ult_iff).mp h; rw [hsum] at this
    simp [BitVec.toNat_ofNat]; omega
  · rename_i h; have := mt (ult_iff).mpr h; rw [hsum] at this; push Not at this
    simp [BitVec.toNat_ofNat]; omega

-- OR of two {0,1}-valued Words
private theorem or_01_toNat (x y : Word) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    (x ||| y).toNat = min 1 (x.toNat + y.toNat) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

-- {0,1} fact for if-then-else
private theorem ite_word_01 (c : Prop) [Decidable c] :
    (if c then (1 : Word) else 0) = 0 ∨ (if c then (1 : Word) else 0) = 1 := by
  split <;> simp

-- Combined carry: (carry_a ||| carry_b).toNat = (a + b + cin) / 2^64
private theorem combined_carry_toNat {x y cin : Word} (hcin : cin.toNat ≤ 1) :
    let psum := x + y
    let ca := if BitVec.ult psum y then (1 : Word) else 0
    let res := psum + cin
    let cb := if BitVec.ult res cin then (1 : Word) else 0
    (ca ||| cb).toNat = (x.toNat + y.toNat + cin.toNat) / 2^64 := by
  intro psum ca res cb
  have := x.isLt; have := y.isLt
  have hca : ca.toNat = (x.toNat + y.toNat) / 2^64 := carry_toNat
  have hpsum : psum.toNat = (x.toNat + y.toNat) % 2^64 := BitVec.toNat_add x y
  have hcb : cb.toNat = (psum.toNat + cin.toNat) / 2^64 := carry_toNat
  rw [or_01_toNat ca cb (ite_word_01 _) (ite_word_01 _), hca, hcb, hpsum]
  have : (x.toNat + y.toNat) % 2^64 < 2^64 := Nat.mod_lt _ (by omega)
  omega

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
  intro a0 b0 a1 b1 a2 b2 a3 b3 sum0 carry0 psum1 carry1a result1 carry1b carry1 psum2 carry2a result2 carry2b carry2 psum3 result3
  -- toNat of carry chain
  have hc0 : carry0.toNat = (a0.toNat + b0.toNat) / 2^64 := carry_toNat
  have hc0_le : carry0.toNat ≤ 1 := by
    have := a0.isLt; have := b0.isLt; rw [hc0]; omega
  have hc1 : carry1.toNat = (a1.toNat + b1.toNat + carry0.toNat) / 2^64 :=
    combined_carry_toNat hc0_le
  have hc1_le : carry1.toNat ≤ 1 := by
    have := a1.isLt; have := b1.isLt; rw [hc1]; omega
  have hc2 : carry2.toNat = (a2.toNat + b2.toNat + carry1.toNat) / 2^64 :=
    combined_carry_toNat hc1_le
  have : carry2.toNat ≤ 1 := by
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
  have := a0.isLt; have := b0.isLt
  have := a1.isLt; have := b1.isLt
  have := a2.isLt; have := b2.isLt
  have := a3.isLt; have := b3.isLt
  -- getLimb toNat for (a+b) at each index
  have key0 : ((a + b).getLimb 0).toNat = S % 2^256 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hS]; norm_num
  have key1 : ((a + b).getLimb 1).toNat = S % 2^256 / 2^64 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hS]; norm_num
  have key2 : ((a + b).getLimb 2).toNat = S % 2^256 / 2^128 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]; rw [hS]; norm_num
  have key3 : ((a + b).getLimb 3).toNat = S % 2^256 / 2^192 % 2^64 := by
    simp only [getLimb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      fin4_val_3]; rw [hS]
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
private theorem sub_limb_toNat {aLimb bLimb borrow : Word}
    (hborrow : borrow.toNat = 0 ∨ borrow.toNat = 1) :
    (aLimb - bLimb - borrow).toNat =
    (aLimb.toNat + 2^64 - bLimb.toNat + 2^64 - borrow.toNat) % 2^64 := by
  simp only [BitVec.toNat_sub]
  have := aLimb.isLt
  have := bLimb.isLt
  rcases hborrow with h | h <;> simp only [h] <;> omega

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
    let _borrow3a := if BitVec.ult a3 b3 then (1 : Word) else 0
    let temp3 := a3 - b3
    let _borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let result3 := temp3 - borrow2
    (a - b).getLimb 0 = diff0 ∧
    (a - b).getLimb 1 = result1 ∧
    (a - b).getLimb 2 = result2 ∧
    (a - b).getLimb 3 = result3 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3 borrow0 diff0 borrow1a temp1 borrow1b result1 borrow1 borrow2a temp2 borrow2b result2 borrow2 _borrow3a temp3 _borrow3b result3
  -- Key: (a - b).toNat = (a.toNat + 2^256 - b.toNat) % 2^256
  have hS : (a - b).toNat = (a.toNat + 2^256 - b.toNat) % 2^256 := by
    simp only [BitVec.toNat_sub]; congr 1; omega
  -- Borrow flag toNat values
  have hb0_nat : borrow0.toNat = if a0.toNat < b0.toNat then 1 else 0 := by
    simp only [borrow0]; split
    · rename_i h; rw [if_pos ((ult_iff).mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h ((ult_iff).mpr hlt))]; rfl
  -- borrow0 is 0 or 1
  have hb0_01 : borrow0.toNat = 0 ∨ borrow0.toNat = 1 := by
    rw [hb0_nat]; split <;> simp
  -- borrow1 tracks 2-limb comparison (reuse from LT proof pattern)
  have hb1_or : borrow1 = if (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0)
      then (1 : Word) else 0 := borrow_or_iff
  have htemp1_nat : temp1.toNat = (a1.toNat + 2^64 - b1.toNat) % 2^64 := by
    simp only [temp1, BitVec.toNat_sub]; congr 1; omega
  have hb1_cond : (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0) ↔
      (a0.toNat + a1.toNat * 2^64 < b0.toNat + b1.toNat * 2^64) := by
    rw [show BitVec.ult a1 b1 ↔ a1.toNat < b1.toNat from ult_iff,
        show BitVec.ult temp1 borrow0 ↔ temp1.toNat < borrow0.toNat from ult_iff,
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
      then (1 : Word) else 0 := borrow_or_iff
  have htemp2_nat : temp2.toNat = (a2.toNat + 2^64 - b2.toNat) % 2^64 := by
    simp only [temp2, BitVec.toNat_sub]; congr 1; omega
  have hb2_cond : (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1) ↔
      (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 <
       b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128) := by
    rw [show BitVec.ult a2 b2 ↔ a2.toNat < b2.toNat from ult_iff,
        show BitVec.ult temp2 borrow1 ↔ temp2.toNat < borrow1.toNat from ult_iff,
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
  have := a0.isLt; have := b0.isLt
  have := a1.isLt; have := b1.isLt
  have := a2.isLt; have := b2.isLt
  have := a3.isLt; have := b3.isLt
  have := b.isLt
  have : b.toNat ≤ a.toNat + 2^256 := by omega
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
  have hD : (a - b).toNat = D % 2^256 := by
    rw [hS, toNat_eq_limb_sum a, toNat_eq_limb_sum b]
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
      fin4_val_3]; rw [hD]
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
    · rename_i h; push Not at h
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

end EvmWord

end EvmAsm.Evm64
