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

end EvmAsm.Evm64.MulMod.ProductAlgebra
