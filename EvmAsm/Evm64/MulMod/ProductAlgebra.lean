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
import EvmAsm.Evm64.EvmWordArith.MulHigh
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
  [(3936, 0), (3944, 1), (3952, 2), (3960, 3),
   (3968, 4), (3976, 5), (3984, 6), (3992, 7)]

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

/-- Runtime product-window offsets paired with the corresponding algebraic limb value. -/
def productOffsetValues (a b : EvmWord) : List (BitVec 12 × Word) :=
  productOffsetIndices.map (fun offsetIndex => (offsetIndex.1, productLimb a b offsetIndex.2))

@[simp] theorem productOffsetValues_length (a b : EvmWord) :
    (productOffsetValues a b).length = 8 := by
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


/-- High limbs of the 512-bit product agree with the limbs of `mulHigh`. -/
private theorem productLimb_high_eq_mulHigh_getLimb (a b : EvmWord) (i : Fin 4) :
    productLimb a b (i.val + 4) = (EvmWord.mulHigh a b).getLimb i := by
  apply BitVec.eq_of_toNat_eq
  simp only [productLimb, productNat, EvmWord.getLimb, EvmWord.mulHigh_correct,
    BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  have hmul : 2 ^ 256 * 2 ^ (i.val * 64) = 2 ^ (64 * (i.val + 4)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hmul]

@[simp] theorem productLimb_four_eq_mulHigh_getLimb_zero (a b : EvmWord) :
    productLimb a b 4 = (EvmWord.mulHigh a b).getLimb 0 := by
  exact productLimb_high_eq_mulHigh_getLimb a b 0

@[simp] theorem productLimb_five_eq_mulHigh_getLimb_one (a b : EvmWord) :
    productLimb a b 5 = (EvmWord.mulHigh a b).getLimb 1 := by
  exact productLimb_high_eq_mulHigh_getLimb a b 1

@[simp] theorem productLimb_six_eq_mulHigh_getLimb_two (a b : EvmWord) :
    productLimb a b 6 = (EvmWord.mulHigh a b).getLimb 2 := by
  exact productLimb_high_eq_mulHigh_getLimb a b 2

@[simp] theorem productLimb_seven_eq_mulHigh_getLimb_three (a b : EvmWord) :
    productLimb a b 7 = (EvmWord.mulHigh a b).getLimb 3 := by
  exact productLimb_high_eq_mulHigh_getLimb a b 3

@[simp] theorem productLimb_four_eq_mulHigh_getLimbN_zero (a b : EvmWord) :
    productLimb a b 4 = (EvmWord.mulHigh a b).getLimbN 0 := by
  rw [productLimb_four_eq_mulHigh_getLimb_zero, EvmWord.getLimb_as_getLimbN_0]

@[simp] theorem productLimb_five_eq_mulHigh_getLimbN_one (a b : EvmWord) :
    productLimb a b 5 = (EvmWord.mulHigh a b).getLimbN 1 := by
  rw [productLimb_five_eq_mulHigh_getLimb_one, EvmWord.getLimb_as_getLimbN_1]

@[simp] theorem productLimb_six_eq_mulHigh_getLimbN_two (a b : EvmWord) :
    productLimb a b 6 = (EvmWord.mulHigh a b).getLimbN 2 := by
  rw [productLimb_six_eq_mulHigh_getLimb_two, EvmWord.getLimb_as_getLimbN_2]

@[simp] theorem productLimb_seven_eq_mulHigh_getLimbN_three (a b : EvmWord) :
    productLimb a b 7 = (EvmWord.mulHigh a b).getLimbN 3 := by
  rw [productLimb_seven_eq_mulHigh_getLimb_three, EvmWord.getLimb_as_getLimbN_3]

@[simp] theorem productLimbs_get_four_eq_mulHigh_getLimbN_zero (a b : EvmWord) :
    (productLimbs a b)[4] = (EvmWord.mulHigh a b).getLimbN 0 := by
  rw [productLimbs_get_four, productLimb_four_eq_mulHigh_getLimbN_zero]

@[simp] theorem productLimbs_get_five_eq_mulHigh_getLimbN_one (a b : EvmWord) :
    (productLimbs a b)[5] = (EvmWord.mulHigh a b).getLimbN 1 := by
  rw [productLimbs_get_five, productLimb_five_eq_mulHigh_getLimbN_one]

@[simp] theorem productLimbs_get_six_eq_mulHigh_getLimbN_two (a b : EvmWord) :
    (productLimbs a b)[6] = (EvmWord.mulHigh a b).getLimbN 2 := by
  rw [productLimbs_get_six, productLimb_six_eq_mulHigh_getLimbN_two]

@[simp] theorem productLimbs_get_seven_eq_mulHigh_getLimbN_three (a b : EvmWord) :
    (productLimbs a b)[7] = (EvmWord.mulHigh a b).getLimbN 3 := by
  rw [productLimbs_get_seven, productLimb_seven_eq_mulHigh_getLimbN_three]

@[simp] theorem productHighLimbs_eq_mulHigh_getLimbs (a b : EvmWord) :
    productHighLimbs a b =
      [(EvmWord.mulHigh a b).getLimb 0, (EvmWord.mulHigh a b).getLimb 1,
       (EvmWord.mulHigh a b).getLimb 2, (EvmWord.mulHigh a b).getLimb 3] := by
  simp only [productHighLimbs_eq, productLimb_four_eq_mulHigh_getLimb_zero,
    productLimb_five_eq_mulHigh_getLimb_one, productLimb_six_eq_mulHigh_getLimb_two,
    productLimb_seven_eq_mulHigh_getLimb_three]

@[simp] theorem productHighLimbs_eq_mulHigh_getLimbNs (a b : EvmWord) :
    productHighLimbs a b =
      [(EvmWord.mulHigh a b).getLimbN 0, (EvmWord.mulHigh a b).getLimbN 1,
       (EvmWord.mulHigh a b).getLimbN 2, (EvmWord.mulHigh a b).getLimbN 3] := by
  simp only [productHighLimbs_eq, productLimb_four_eq_mulHigh_getLimbN_zero,
    productLimb_five_eq_mulHigh_getLimbN_one, productLimb_six_eq_mulHigh_getLimbN_two,
    productLimb_seven_eq_mulHigh_getLimbN_three]

@[simp] theorem productHighLimbs_get_zero (a b : EvmWord) :
    (productHighLimbs a b)[0] = (EvmWord.mulHigh a b).getLimbN 0 := by
  simp [productHighLimbs, EvmWord.getLimb_as_getLimbN_0]

@[simp] theorem productHighLimbs_get_one (a b : EvmWord) :
    (productHighLimbs a b)[1] = (EvmWord.mulHigh a b).getLimbN 1 := by
  simp [productHighLimbs, EvmWord.getLimb_as_getLimbN_1]

@[simp] theorem productHighLimbs_get_two (a b : EvmWord) :
    (productHighLimbs a b)[2] = (EvmWord.mulHigh a b).getLimbN 2 := by
  simp [productHighLimbs, EvmWord.getLimb_as_getLimbN_2]

@[simp] theorem productHighLimbs_get_three (a b : EvmWord) :
    (productHighLimbs a b)[3] = (EvmWord.mulHigh a b).getLimbN 3 := by
  simp [productHighLimbs, EvmWord.getLimb_as_getLimbN_3]

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

/-- The full product window splits into the low EVM multiplication word followed by
    the high multiplication word. -/
@[simp] theorem productLimbs_eq_mul_split_getLimbs (a b : EvmWord) :
    productLimbs a b =
      [(a * b).getLimb 0, (a * b).getLimb 1,
       (a * b).getLimb 2, (a * b).getLimb 3,
       (EvmWord.mulHigh a b).getLimb 0, (EvmWord.mulHigh a b).getLimb 1,
       (EvmWord.mulHigh a b).getLimb 2, (EvmWord.mulHigh a b).getLimb 3] := by
  simp only [productLimbs, productLimb_zero_eq_mul_getLimb,
    productLimb_one_eq_mul_getLimb, productLimb_two_eq_mul_getLimb,
    productLimb_three_eq_mul_getLimb, productLimb_four_eq_mulHigh_getLimb_zero,
    productLimb_five_eq_mulHigh_getLimb_one, productLimb_six_eq_mulHigh_getLimb_two,
    productLimb_seven_eq_mulHigh_getLimb_three]

/-- Product-window offsets mapped to the low/high split expected by the folded
    `evm_mulmod_product_layout` postcondition. -/
@[simp] theorem productOffsetValues_eq_mul_split_getLimbs (a b : EvmWord) :
    productOffsetValues a b =
      [((3936 : BitVec 12), (a * b).getLimb 0),
       ((3944 : BitVec 12), (a * b).getLimb 1),
       ((3952 : BitVec 12), (a * b).getLimb 2),
       ((3960 : BitVec 12), (a * b).getLimb 3),
       ((3968 : BitVec 12), (EvmWord.mulHigh a b).getLimb 0),
       ((3976 : BitVec 12), (EvmWord.mulHigh a b).getLimb 1),
       ((3984 : BitVec 12), (EvmWord.mulHigh a b).getLimb 2),
       ((3992 : BitVec 12), (EvmWord.mulHigh a b).getLimb 3)] := by
  simp [productOffsetValues, productOffsetIndices, productLimb_zero_eq_mul_getLimb,
    productLimb_one_eq_mul_getLimb, productLimb_two_eq_mul_getLimb,
    productLimb_three_eq_mul_getLimb, productLimb_four_eq_mulHigh_getLimb_zero,
    productLimb_five_eq_mulHigh_getLimb_one, productLimb_six_eq_mulHigh_getLimb_two,
    productLimb_seven_eq_mulHigh_getLimb_three]

@[simp] theorem productOffsetValues_eq_mul_split_getLimbNs (a b : EvmWord) :
    productOffsetValues a b =
      [((3936 : BitVec 12), (a * b).getLimbN 0),
       ((3944 : BitVec 12), (a * b).getLimbN 1),
       ((3952 : BitVec 12), (a * b).getLimbN 2),
       ((3960 : BitVec 12), (a * b).getLimbN 3),
       ((3968 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 0),
       ((3976 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 1),
       ((3984 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 2),
       ((3992 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 3)] := by
  rw [productOffsetValues_eq_mul_split_getLimbs]
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]

@[simp] theorem productOffsetValues_get_four (a b : EvmWord) :
    (productOffsetValues a b)[4] = ((3968 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 0) := by
  simp [productOffsetValues, productOffsetIndices, EvmWord.getLimb_as_getLimbN_0]

@[simp] theorem productOffsetValues_get_five (a b : EvmWord) :
    (productOffsetValues a b)[5] = ((3976 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 1) := by
  simp [productOffsetValues, productOffsetIndices, EvmWord.getLimb_as_getLimbN_1]

@[simp] theorem productOffsetValues_get_six (a b : EvmWord) :
    (productOffsetValues a b)[6] = ((3984 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 2) := by
  simp [productOffsetValues, productOffsetIndices, EvmWord.getLimb_as_getLimbN_2]

@[simp] theorem productOffsetValues_get_seven (a b : EvmWord) :
    (productOffsetValues a b)[7] = ((3992 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 3) := by
  simp [productOffsetValues, productOffsetIndices, EvmWord.getLimb_as_getLimbN_3]

@[simp] theorem productOffsetValues_offsets (a b : EvmWord) :
    (productOffsetValues a b).map Prod.fst = mulmodProductOffsets := by
  simp [productOffsetValues, productOffsetIndices, mulmodProductOffsets]

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
