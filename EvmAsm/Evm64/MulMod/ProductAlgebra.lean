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

@[simp] theorem productHighLimbs_eq_mulHigh_getLimbs (a b : EvmWord) :
    productHighLimbs a b =
      [(EvmWord.mulHigh a b).getLimb 0, (EvmWord.mulHigh a b).getLimb 1,
       (EvmWord.mulHigh a b).getLimb 2, (EvmWord.mulHigh a b).getLimb 3] := by
  simp only [productHighLimbs_eq, productLimb_four_eq_mulHigh_getLimb_zero,
    productLimb_five_eq_mulHigh_getLimb_one, productLimb_six_eq_mulHigh_getLimb_two,
    productLimb_seven_eq_mulHigh_getLimb_three]

end EvmAsm.Evm64.MulMod.ProductAlgebra
