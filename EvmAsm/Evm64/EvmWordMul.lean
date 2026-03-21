/-
  EvmAsm.Evm64.EvmWordMul

  Mathematical correctness lemmas connecting the schoolbook 4×4 limb
  multiplication carry-chain to the 256-bit (a * b) product.
  Used by the stack-level MUL spec (Multiply/Spec.lean).
-/

import EvmAsm.Evm64.EvmWordArith
import EvmAsm.Rv64.Instructions

namespace EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Helpers
-- ============================================================================

/-- MULHU toNat: the upper 64 bits of a 64×64 product. -/
theorem mulhu_toNat (a b : Word) :
    (rv64_mulhu a b).toNat = a.toNat * b.toNat / 2^64 := by
  unfold rv64_mulhu
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_mul,
             BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2^128 := by nlinarith
  have ha128 : a.toNat % 2 ^ 128 = a.toNat := Nat.mod_eq_of_lt (by linarith)
  have hb128 : b.toNat % 2 ^ 128 = b.toNat := Nat.mod_eq_of_lt (by linarith)
  rw [ha128, hb128, Nat.mod_eq_of_lt hab]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by linarith))

/-- 64×64 product splits into low word + high word * 2^64. -/
theorem mul_limb_split (a b : Word) :
    a.toNat * b.toNat = (a * b).toNat + (rv64_mulhu a b).toNat * 2^64 := by
  rw [BitVec.toNat_mul, mulhu_toNat]
  have h := Nat.mod_add_div (a.toNat * b.toNat) (2^64)
  omega

/-- Replacing b%m with b inside an outer %m. -/
private theorem add_mod_replace (a b m : Nat) :
    (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- a.toNat mod W = limb 0 toNat. -/
private theorem toNat_mod_W (v : EvmWord) :
    v.toNat % 2^64 = (v.getLimb 0).toNat := by
  have h := toNat_eq_limb_sum v
  have h0 := (v.getLimb 0).isLt
  rw [h, show (v.getLimb 0).toNat + (v.getLimb 1).toNat * 2^64 +
    (v.getLimb 2).toNat * 2^128 + (v.getLimb 3).toNat * 2^192 =
    (v.getLimb 0).toNat + ((v.getLimb 1).toNat + (v.getLimb 2).toNat * 2^64 +
    (v.getLimb 3).toNat * 2^128) * 2^64 from by ring,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h0]

-- ============================================================================
-- Per-limb correctness
-- ============================================================================

/-- Limb 0 of the product: just the low 64 bits of a0 * b0. -/
private theorem mul_getLimb_0 (a b : EvmWord) :
    (a * b).getLimb 0 = a.getLimb 0 * b.getLimb 0 := by
  sorry

set_option maxHeartbeats 800000 in
/-- Limb 1 of the product: cross-terms at position 1. -/
private theorem mul_getLimb_1 (a b : EvmWord) :
    (a * b).getLimb 1 =
    (rv64_mulhu (a.getLimb 0) (b.getLimb 0) + a.getLimb 1 * b.getLimb 0) +
    a.getLimb 0 * b.getLimb 1 := by
  sorry

set_option maxHeartbeats 1600000 in
/-- Limb 2 of the product equals the carry-chain c2_r2. -/
private theorem mul_getLimb_2 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1; let a2 := a.getLimb 2
    let b0 := b.getLimb 0; let b1 := b.getLimb 1; let b2 := b.getLimb 2
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_lo2 := a1 * b1
    let c1_r2 := c1_r2a + c1_lo2
    let c2_lo := a0 * b2
    (a * b).getLimb 2 = c1_r2 + c2_lo := by
  sorry

set_option maxHeartbeats 1600000 in
/-- Limb 3 of the product equals the carry-chain r3_final. -/
private theorem mul_getLimb_3 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1
    let a2 := a.getLimb 2; let a3 := a.getLimb 3
    let b0 := b.getLimb 0; let b1 := b.getLimb 1
    let b2 := b.getLimb 2; let b3 := b.getLimb 3
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    (a * b).getLimb 3 = c2_r3 + a0 * b3 := by
  sorry

-- ============================================================================
-- Combined theorem
-- ============================================================================

/-- Each limb of a * b equals the schoolbook carry-chain result at that limb position. -/
theorem mul_carry_chain_correct (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1
    let a2 := a.getLimb 2; let a3 := a.getLimb 3
    let b0 := b.getLimb 0; let b1 := b.getLimb 1
    let b2 := b.getLimb 2; let b3 := b.getLimb 3
    let c0_r0 := a0 * b0
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c0_lo_a2b0 := a2 * b0
    let c0_hi_a2b0 := rv64_mulhu a2 b0
    let c0_r2 := c0_hi_a1b0 + c0_c1 + c0_lo_a2b0
    let c0_c2 := if BitVec.ult c0_r2 c0_lo_a2b0 then (1 : Word) else 0
    let c0_r3p := c0_hi_a2b0 + c0_c2 + a3 * b0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c1_rc := c1_hi + c1_c1
    let c1_r2a := c0_r2 + c1_rc
    let c1_cr1 := if BitVec.ult c1_r2a c1_rc then (1 : Word) else 0
    let c1_lo2 := a1 * b1
    let c1_hi2 := rv64_mulhu a1 b1
    let c1_r2 := c1_r2a + c1_lo2
    let c1_cr2 := if BitVec.ult c1_r2 c1_lo2 then (1 : Word) else 0
    let c1_rc2 := c1_hi2 + c1_cr2
    let c1_r3p := c1_cr1 + c1_rc2 + a2 * b1 + c0_r3p
    let c2_lo := a0 * b2
    let c2_hi := rv64_mulhu a0 b2
    let c2_r2 := c1_r2 + c2_lo
    let c2_c := if BitVec.ult c2_r2 c2_lo then (1 : Word) else 0
    let c2_rc := c2_hi + c2_c + a1 * b2
    let c2_r3 := c1_r3p + c2_rc
    let r3_final := c2_r3 + a0 * b3
    (a * b).getLimb 0 = c0_r0 ∧
    (a * b).getLimb 1 = c1_r1 ∧
    (a * b).getLimb 2 = c2_r2 ∧
    (a * b).getLimb 3 = r3_final := by
  intro a0 a1 a2 a3 b0 b1 b2 b3
  intro c0_r0 c0_hi_a0b0 c0_lo_a1b0 c0_hi_a1b0
  intro c0_r1 c0_c1 c0_lo_a2b0 c0_hi_a2b0 c0_r2 c0_c2 c0_r3p
  intro c1_lo c1_hi c1_r1 c1_c1 c1_rc c1_r2a c1_cr1
  intro c1_lo2 c1_hi2 c1_r2 c1_cr2 c1_rc2 c1_r3p
  intro c2_lo c2_hi c2_r2 c2_c c2_rc c2_r3
  intro r3_final
  exact ⟨mul_getLimb_0 a b, mul_getLimb_1 a b, mul_getLimb_2 a b, mul_getLimb_3 a b⟩

end EvmWord

end EvmAsm.Rv64
