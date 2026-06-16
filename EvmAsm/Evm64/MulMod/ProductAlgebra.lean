/-
  EvmAsm.Evm64.MulMod.ProductAlgebra

  Pure model for the eight-limb 512-bit product produced by
  `evm_mulmod_product_layout`.

  This file is intentionally only the foundation for the later algebra bridge:
  it fixes the little-endian product-limb order and the concrete product-window
  offsets used by the runtime program. Later slices prove these limbs match the
  low `(a * b)` word and high `EvmWord.mulHigh` word.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Evm64.EvmWordArith.MulCorrect

namespace EvmAsm.Evm64.MulMod.ProductAlgebra

open EvmAsm.Evm64
open EvmAsm.Rv64

/-- Natural-number value of the full 512-bit product before any truncation. -/
def productNat (a b : EvmWord) : Nat :=
  a.toNat * b.toNat

/-- The `i`th little-endian 64-bit limb of the full product. -/
def productLimb (a b : EvmWord) (i : Nat) : Word :=
  BitVec.ofNat 64 ((productNat a b) / 2 ^ (64 * i))

/-- The eight little-endian limbs emitted by `evm_mulmod_product_layout`. -/
def productLimbs (a b : EvmWord) : List Word :=
  [productLimb a b 0,
   productLimb a b 1,
   productLimb a b 2,
   productLimb a b 3,
   productLimb a b 4,
   productLimb a b 5,
   productLimb a b 6,
   productLimb a b 7]

/-- Runtime product-window offsets paired with the algebraic limb index. -/
def productOffsetIndices : List (BitVec 12 × Nat) :=
  [(96, 0), (104, 1), (112, 2), (120, 3),
   (128, 4), (136, 5), (144, 6), (152, 7)]

/-- The low 256-bit half, as four little-endian 64-bit limbs. -/
def productLowLimbs (a b : EvmWord) : List Word :=
  (productLimbs a b).take 4

/-- The high 256-bit half, as four little-endian 64-bit limbs. -/
def productHighLimbs (a b : EvmWord) : List Word :=
  (productLimbs a b).drop 4

@[simp] theorem productLimbs_length (a b : EvmWord) :
    (productLimbs a b).length = 8 := by
  rfl

@[simp] theorem productOffsetIndices_length :
    productOffsetIndices.length = 8 := by
  rfl

@[simp] theorem productLowLimbs_length (a b : EvmWord) :
    (productLowLimbs a b).length = 4 := by
  rfl

@[simp] theorem productHighLimbs_length (a b : EvmWord) :
    (productHighLimbs a b).length = 4 := by
  rfl

/-- The algebraic model uses the same product-window offsets as the runtime
    program. -/
theorem productOffsetIndices_offsets :
    productOffsetIndices.map Prod.fst = mulmodProductOffsets := by
  rfl

@[simp] theorem productLimbs_get_zero (a b : EvmWord) :
    (productLimbs a b)[0] = productLimb a b 0 := by
  rfl

@[simp] theorem productLimbs_get_one (a b : EvmWord) :
    (productLimbs a b)[1] = productLimb a b 1 := by
  rfl

@[simp] theorem productLimbs_get_two (a b : EvmWord) :
    (productLimbs a b)[2] = productLimb a b 2 := by
  rfl

@[simp] theorem productLimbs_get_three (a b : EvmWord) :
    (productLimbs a b)[3] = productLimb a b 3 := by
  rfl

@[simp] theorem productLimbs_get_four (a b : EvmWord) :
    (productLimbs a b)[4] = productLimb a b 4 := by
  rfl

@[simp] theorem productLimbs_get_five (a b : EvmWord) :
    (productLimbs a b)[5] = productLimb a b 5 := by
  rfl

@[simp] theorem productLimbs_get_six (a b : EvmWord) :
    (productLimbs a b)[6] = productLimb a b 6 := by
  rfl

@[simp] theorem productLimbs_get_seven (a b : EvmWord) :
    (productLimbs a b)[7] = productLimb a b 7 := by
  rfl

@[simp] theorem productLowLimbs_eq (a b : EvmWord) :
    productLowLimbs a b =
      [productLimb a b 0, productLimb a b 1, productLimb a b 2,
       productLimb a b 3] := by
  rfl

@[simp] theorem productHighLimbs_eq (a b : EvmWord) :
    productHighLimbs a b =
      [productLimb a b 4, productLimb a b 5, productLimb a b 6,
       productLimb a b 7] := by
  rfl


/-- Low limbs of the 512-bit product agree with the corresponding limbs of the
    truncated 256-bit EVM multiplication. -/
private theorem productLimb_low_eq_getLimb (a b : EvmWord) (i : Fin 4) :
    productLimb a b i.val = (a * b).getLimb i := by
  apply BitVec.eq_of_toNat_eq
  simp only [productLimb, productNat, EvmWord.getLimb, BitVec.toNat_ofNat,
    BitVec.extractLsb'_toNat, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  have himul : i.val * 64 = 64 * i.val := by omega
  rw [himul]
  have hpow : 2 ^ 256 = 2 ^ (64 * i.val) * 2 ^ (256 - 64 * i.val) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow, Nat.mod_mul_right_div_self]
  have hpow2 :
      2 ^ (256 - 64 * i.val) = 2 ^ 64 * 2 ^ (256 - 64 * i.val - 64) := by
    rw [← Nat.pow_add]
    congr 1
    have := i.isLt
    omega
  rw [hpow2, Nat.mod_mul_right_mod]

@[simp] theorem productLimb_zero_eq_mul_getLimb (a b : EvmWord) :
    productLimb a b 0 = (a * b).getLimb 0 := by
  exact productLimb_low_eq_getLimb a b 0

@[simp] theorem productLimb_one_eq_mul_getLimb (a b : EvmWord) :
    productLimb a b 1 = (a * b).getLimb 1 := by
  exact productLimb_low_eq_getLimb a b 1

@[simp] theorem productLimb_two_eq_mul_getLimb (a b : EvmWord) :
    productLimb a b 2 = (a * b).getLimb 2 := by
  exact productLimb_low_eq_getLimb a b 2

@[simp] theorem productLimb_three_eq_mul_getLimb (a b : EvmWord) :
    productLimb a b 3 = (a * b).getLimb 3 := by
  exact productLimb_low_eq_getLimb a b 3

@[simp] theorem productLowLimbs_eq_mul_getLimbs (a b : EvmWord) :
    productLowLimbs a b =
      [(a * b).getLimb 0, (a * b).getLimb 1,
       (a * b).getLimb 2, (a * b).getLimb 3] := by
  simp only [productLowLimbs_eq, productLimb_zero_eq_mul_getLimb,
    productLimb_one_eq_mul_getLimb, productLimb_two_eq_mul_getLimb,
    productLimb_three_eq_mul_getLimb]

@[simp] theorem productLimb_zero_eq_mul_correct_limb0 (a b : EvmWord) :
    productLimb a b 0 = a.getLimb 0 * b.getLimb 0 := by
  rw [productLimb_zero_eq_mul_getLimb, EvmWord.mul_correct_limb0]

theorem productLimb_one_eq_mul_correct_limb1 (a b : EvmWord) :
    let a0 := a.getLimb 0; let a1 := a.getLimb 1
    let b0 := b.getLimb 0; let b1 := b.getLimb 1
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c1_lo := a0 * b1
    let c1_r1 := c0_r1 + c1_lo
    productLimb a b 1 = c1_r1 := by
  rw [productLimb_one_eq_mul_getLimb]
  exact EvmWord.mul_correct_limb1 a b

theorem productLimb_two_eq_mul_correct_limb2 (a b : EvmWord) :
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
    let c2_r2 := c1_r2 + c2_lo
    productLimb a b 2 = c2_r2 := by
  rw [productLimb_two_eq_mul_getLimb]
  exact EvmWord.mul_correct_limb2 a b

theorem productLimb_three_eq_mul_correct_limb3 (a b : EvmWord) :
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
    let r3_final := c2_r3 + a0 * b3
    productLimb a b 3 = r3_final := by
  rw [productLimb_three_eq_mul_getLimb]
  exact EvmWord.mul_correct_limb3 a b

end EvmAsm.Evm64.MulMod.ProductAlgebra
