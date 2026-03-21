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
  apply BitVec.eq_of_toNat_eq
  -- LHS: ((a*b).getLimb 0).toNat = (a*b).toNat / 2^0 % 2^64 = (a*b).toNat % 2^64
  rw [getLimb_toNat_eq, show (0 : Fin 4).val = 0 from rfl,
      show 0 * 64 = 0 from rfl, Nat.pow_zero, Nat.div_one]
  -- LHS: (a * b).toNat % 2^64 = (a.toNat * b.toNat % 2^256) % 2^64
  conv_lhs => rw [BitVec.toNat_mul,
    show (2:Nat)^256 = 2^64 * (2^64 * (2^64 * 2^64)) from by norm_num,
    Nat.mod_mul_right_mod]
  -- LHS: (a.toNat * b.toNat) % 2^64
  -- RHS: (a.getLimb 0 * b.getLimb 0).toNat = ((a.getLimb 0).toNat * (b.getLimb 0).toNat) % 2^64
  conv_rhs => rw [BitVec.toNat_mul]
  -- Both sides: _ % 2^64. Show inner expressions equal mod 2^64.
  conv_lhs => rw [Nat.mul_mod, toNat_mod_W a, toNat_mod_W b]

set_option maxHeartbeats 800000 in
/-- Limb 1 of the product: cross-terms at position 1. -/
private theorem mul_getLimb_1 (a b : EvmWord) :
    (a * b).getLimb 1 =
    (rv64_mulhu (a.getLimb 0) (b.getLimb 0) + a.getLimb 1 * b.getLimb 0) +
    a.getLimb 0 * b.getLimb 1 := by
  set W := (2:Nat)^64
  have hW : 0 < W := by positivity
  -- Expand both sides via eq_of_toNat_eq
  apply BitVec.eq_of_toNat_eq
  -- ================================================================
  -- LHS: ((a*b).getLimb 1).toNat
  -- ================================================================
  conv_lhs =>
    rw [getLimb_toNat_eq, show (1 : Fin 4).val = 1 from rfl,
        show 1 * 64 = 64 from rfl]
  -- LHS = (a*b).toNat / 2^64 % 2^64
  conv_lhs =>
    rw [BitVec.toNat_mul,
        show (2:Nat)^256 = W * (W * (W * W)) from by norm_num,
        show (2:Nat)^64 = W from rfl,
        Nat.mod_mul_right_div_self]
  -- LHS = (a.toNat * b.toNat) / W % (W * (W * W)) % W
  conv_lhs => rw [Nat.mod_mul_right_mod]
  -- LHS = (a.toNat * b.toNat) / W % W
  -- Expand a.toNat and b.toNat via limb sums and factor
  have ha_sum := toNat_eq_limb_sum a
  have hb_sum := toNat_eq_limb_sum b
  -- Factor the product using limb .toNat values
  -- We write the product in Horner form: a0*b0 + (cross1 + (cross2 + ...)*W)*W
  have hprod : a.toNat * b.toNat =
      (a.getLimb 0).toNat * (b.getLimb 0).toNat +
      ((a.getLimb 1).toNat * (b.getLimb 0).toNat +
       (a.getLimb 0).toNat * (b.getLimb 1).toNat +
       ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
        (a.getLimb 1).toNat * (b.getLimb 1).toNat +
        (a.getLimb 0).toNat * (b.getLimb 2).toNat +
        ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
         (a.getLimb 2).toNat * (b.getLimb 1).toNat +
         (a.getLimb 1).toNat * (b.getLimb 2).toNat +
         (a.getLimb 0).toNat * (b.getLimb 3).toNat +
         ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
          (a.getLimb 2).toNat * (b.getLimb 2).toNat +
          (a.getLimb 1).toNat * (b.getLimb 3).toNat +
          ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
           (a.getLimb 2).toNat * (b.getLimb 3).toNat +
           (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W) * W := by
    rw [ha_sum, hb_sum]; show _ = _; ring
  conv_lhs => rw [hprod, Nat.add_mul_div_right _ _ hW]
  -- LHS = (a0*b0/W + cross1 + higher*W) % W
  -- Strip higher-order W-multiples using ring + Nat.add_mul_mod_self_right
  have hstrip :
    ((a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
     ((a.getLimb 1).toNat * (b.getLimb 0).toNat +
      (a.getLimb 0).toNat * (b.getLimb 1).toNat +
      ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
       (a.getLimb 1).toNat * (b.getLimb 1).toNat +
       (a.getLimb 0).toNat * (b.getLimb 2).toNat +
       ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
        (a.getLimb 2).toNat * (b.getLimb 1).toNat +
        (a.getLimb 1).toNat * (b.getLimb 2).toNat +
        (a.getLimb 0).toNat * (b.getLimb 3).toNat +
        ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
         (a.getLimb 2).toNat * (b.getLimb 2).toNat +
         (a.getLimb 1).toNat * (b.getLimb 3).toNat +
         ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
          (a.getLimb 2).toNat * (b.getLimb 3).toNat +
          (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W)) % W =
    ((a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
     (a.getLimb 1).toNat * (b.getLimb 0).toNat +
     (a.getLimb 0).toNat * (b.getLimb 1).toNat) % W := by
    rw [show (a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
        ((a.getLimb 1).toNat * (b.getLimb 0).toNat +
         (a.getLimb 0).toNat * (b.getLimb 1).toNat +
         ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
          (a.getLimb 1).toNat * (b.getLimb 1).toNat +
          (a.getLimb 0).toNat * (b.getLimb 2).toNat +
          ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
           (a.getLimb 2).toNat * (b.getLimb 1).toNat +
           (a.getLimb 1).toNat * (b.getLimb 2).toNat +
           (a.getLimb 0).toNat * (b.getLimb 3).toNat +
           ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
            (a.getLimb 2).toNat * (b.getLimb 2).toNat +
            (a.getLimb 1).toNat * (b.getLimb 3).toNat +
            ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
             (a.getLimb 2).toNat * (b.getLimb 3).toNat +
             (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W) =
        ((a.getLimb 0).toNat * (b.getLimb 0).toNat / W +
         (a.getLimb 1).toNat * (b.getLimb 0).toNat +
         (a.getLimb 0).toNat * (b.getLimb 1).toNat) +
        ((a.getLimb 2).toNat * (b.getLimb 0).toNat +
         (a.getLimb 1).toNat * (b.getLimb 1).toNat +
         (a.getLimb 0).toNat * (b.getLimb 2).toNat +
         ((a.getLimb 3).toNat * (b.getLimb 0).toNat +
          (a.getLimb 2).toNat * (b.getLimb 1).toNat +
          (a.getLimb 1).toNat * (b.getLimb 2).toNat +
          (a.getLimb 0).toNat * (b.getLimb 3).toNat +
          ((a.getLimb 3).toNat * (b.getLimb 1).toNat +
           (a.getLimb 2).toNat * (b.getLimb 2).toNat +
           (a.getLimb 1).toNat * (b.getLimb 3).toNat +
           ((a.getLimb 3).toNat * (b.getLimb 2).toNat +
            (a.getLimb 2).toNat * (b.getLimb 3).toNat +
            (a.getLimb 3).toNat * (b.getLimb 3).toNat * W) * W) * W) * W) * W from by ring,
        Nat.add_mul_mod_self_right]
  conv_lhs => rw [hstrip]
  -- LHS = (a0*b0/W + a1*b0 + a0*b1) % W
  -- ================================================================
  -- RHS
  -- ================================================================
  conv_rhs =>
    rw [BitVec.toNat_add, BitVec.toNat_add, mulhu_toNat,
        BitVec.toNat_mul, BitVec.toNat_mul,
        show (2:Nat)^64 = W from rfl]
  -- RHS = ((a0*b0/W + (a1*b0) % W) % W + (a0*b1) % W) % W
  -- Flatten all nested mods: ((x + y%m) % m + z%m) % m = (x + y + z) % m
  have flatten_rhs : ∀ (x y z m : Nat),
      ((x + y % m) % m + z % m) % m = (x + y + z) % m := by
    intro x y z m
    conv_lhs =>
      rw [show (x + y % m) % m = (x + y) % m from by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]]
    -- Goal: ((x + y) % m + z % m) % m = (x + y + z) % m
    rw [Nat.add_mod ((x + y) % m), Nat.mod_mod, ← Nat.add_mod,
        Nat.add_mod (x + y), Nat.mod_mod, ← Nat.add_mod]
  conv_rhs => rw [flatten_rhs]

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
