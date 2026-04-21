/-
  EvmAsm.Evm64.EvmWordArith.Comparison

  LT and SLT correctness: borrow chain = unsigned/signed less-than.
-/

import EvmAsm.Evm64.EvmWordArith.Common

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- LT correctness: borrow chain = unsigned less-than
-- ============================================================================

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
  intro a0 b0 a1 b1 a2 b2 a3 b3 borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 borrow3a temp3 borrow3b borrow3
  -- Step 1: borrow0 tracks 1-limb comparison
  have hb0_nat : borrow0.toNat = if a0.toNat < b0.toNat then 1 else 0 := by
    simp only [borrow0]; split
    · rename_i h; rw [if_pos ((ult_iff _ _).mp h)]; rfl
    · rename_i h; rw [if_neg (fun hlt => h ((ult_iff _ _).mpr hlt))]; rfl
  -- Step 2: borrow1 tracks 2-limb comparison
  have hb1_or : borrow1 = if (BitVec.ult a1 b1 ∨ BitVec.ult temp1 borrow0)
      then (1 : Word) else 0 := borrow_or_iff
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
      then (1 : Word) else 0 := borrow_or_iff
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
      then (1 : Word) else 0 := borrow_or_iff
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
    let sltMsb := if BitVec.slt a3 b3 then (1 : Word) else 0
    let result := if a3 = b3 then borrow2 else sltMsb
    result = if BitVec.slt a b then (1 : Word) else 0 := by
  intro a0 b0 a1 b1 a2 b2 a3 b3 borrow0 borrow1a temp1 borrow1b borrow1 borrow2a temp2 borrow2b borrow2 sltMsb result
  -- Key: a.msb = a3.msb (bit 255 of a = bit 63 of a3 = MSB of getLimb 3)
  have hmsb_a : a.msb = a3.msb := by
    show a.getLsbD (256 - 1) = (a.extractLsb' (3 * 64) 64).getLsbD (64 - 1)
    simp
  have hmsb_b : b.msb = b3.msb := by
    show b.getLsbD (256 - 1) = (b.extractLsb' (3 * 64) 64).getLsbD (64 - 1)
    simp
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
      rw [show borrow1 = _ from borrow_or_iff]; split
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
      omega
    -- borrow2 = borrow2a ||| borrow2b encodes hb2_cond
    constructor
    · intro hb2
      have hb2_or : borrow2 = if (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1)
          then (1 : Word) else 0 := borrow_or_iff
      rw [hb2_or] at hb2; split at hb2
      · exact hb2_cond.mp ‹_›
      · simp at hb2
    · intro hlt
      have hb2_or : borrow2 = if (BitVec.ult a2 b2 ∨ BitVec.ult temp2 borrow1)
          then (1 : Word) else 0 := borrow_or_iff
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
    simp only [sltMsb]
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
      by_contra h3; push Not at h3
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

end EvmWord

end EvmAsm.Evm64
