/-
  EvmAsm.Evm64.MulMod.ProductLayoutPublicAlgebra

  Algebra bridges from the concrete product-layout aliases to the public
  low-limb postcondition cells.
-/

import EvmAsm.Evm64.MulMod.ProductLayoutCall15
import EvmAsm.Evm64.MulMod.ProductAlgebra

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

theorem mulModProductLayoutCall00P96_eq_mul_limb0 (a b : EvmWord) :
    mulModProductLayoutCall00P96 a b = (a * b).getLimbN 0 := by
  rw [← EvmWord.getLimb_as_getLimbN_0, ← productLimb_zero_eq_mul_getLimb]
  rw [productLimb_zero_eq_mul_correct_limb0]
  rw [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_0]
  simp [mulModProductLayoutCall00P96, mulModAddPartialLoValue,
    mulModAddPartialLoProduct]

theorem mulModProductLayoutCall02P104_eq_mul_limb1 (a b : EvmWord) :
    mulModProductLayoutCall02P104 a b = (a * b).getLimbN 1 := by
  rw [← EvmWord.getLimb_as_getLimbN_1, ← productLimb_one_eq_mul_getLimb]
  rw [productLimb_one_eq_mul_correct_limb1]
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1]
  simp [mulModProductLayoutCall02P104, mulModProductLayoutCall01P104,
    mulModProductLayoutCall00P104, mulModAddPartialLoValue,
    mulModAddPartialHiValue, mulModAddPartialLoProduct,
    mulModAddPartialHiProduct, mulModAddPartialHiBaseValue,
    mulModAddPartialLoCarry, BitVec.ult]

theorem mulModProductLayoutCall05P112_eq_mul_limb2 (a b : EvmWord) :
    mulModProductLayoutCall05P112 a b = (a * b).getLimbN 2 := by
  rw [← EvmWord.getLimb_as_getLimbN_2, ← productLimb_two_eq_mul_getLimb]
  rw [productLimb_two_eq_mul_correct_limb2]
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2]
  simp [mulModProductLayoutCall05P112, mulModProductLayoutCall04P112,
    mulModProductLayoutCall03P112, mulModProductLayoutCall02P112,
    mulModProductLayoutCall01P112, mulModProductLayoutCall00P112,
    mulModProductLayoutCall01P104, mulModProductLayoutCall00P104,
    mulModProductLayoutCall00Carry104, mulModAddPartialLoValue,
    mulModAddPartialHiValue, mulModAddPartialLoProduct,
    mulModAddPartialHiProduct, mulModAddPartialHiBaseValue,
    mulModAddPartialHiBaseCarry, mulModAddPartialHiCarryFromLo,
    mulModAddPartialHiCarry, mulModAddPartialLoCarry,
    mulModCarryStepValue, BitVec.ult]
  ac_rfl

end EvmAsm.Evm64
