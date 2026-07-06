/-
  EvmAsm.Evm64.MulMod.Compose.ProductReduceBridge

  Bridge between the `limbChain` product-limb window primitive and the explicit
  eight-cell separation-logic layout of the 512-bit product. Unfolding the
  window of eight limbs starting at `sp - 104` (each cell 8 bytes lower) with
  the limb function `fun i => productLimb a b (7 - i)` yields the high four
  limbs of `mulHigh a b` followed by the low four limbs of the truncated
  product `a * b`, laid out from `sp - 104` down to `sp - 160`.
-/

import EvmAsm.Evm64.MulMod.ReduceOuterInduction
import EvmAsm.Evm64.MulMod.ProductAlgebra

namespace EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

theorem limbChain_productLimb_eq (sp : Word) (a b : EvmWord) :
    limbChain (sp + signExtend12 (3992 : BitVec 12)) (fun i => productLimb a b (7 - i)) 8
      = (((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 3) **
         ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 2) **
         ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 1) **
         ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ (EvmWord.mulHigh a b).getLimbN 0) **
         ((sp + signExtend12 (3960 : BitVec 12)) ↦ₘ (a * b).getLimbN 3) **
         ((sp + signExtend12 (3952 : BitVec 12)) ↦ₘ (a * b).getLimbN 2) **
         ((sp + signExtend12 (3944 : BitVec 12)) ↦ₘ (a * b).getLimbN 1) **
         ((sp + signExtend12 (3936 : BitVec 12)) ↦ₘ (a * b).getLimbN 0)) := by
  simp only [limbChain, sepConj_emp_right', Nat.reduceAdd, Nat.reduceSub,
    productLimb_four_eq_mulHigh_getLimbN_zero, productLimb_five_eq_mulHigh_getLimbN_one,
    productLimb_six_eq_mulHigh_getLimbN_two, productLimb_seven_eq_mulHigh_getLimbN_three,
    productLimb_zero_eq_mul_getLimb, productLimb_one_eq_mul_getLimb,
    productLimb_two_eq_mul_getLimb, productLimb_three_eq_mul_getLimb,
    EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  have e1 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3992 : BitVec 12) := by
    rw [BitVec.add_assoc]; congr 1
  have e2 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3984 : BitVec 12) := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1
  have e3 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3976 : BitVec 12) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; congr 1
  have e4 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3968 : BitVec 12) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; congr 1
  have e5 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3960 : BitVec 12) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      BitVec.add_assoc]; congr 1
  have e6 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3952 : BitVec 12) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.add_assoc]; congr 1
  have e7 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3944 : BitVec 12) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; congr 1
  have e8 : sp + signExtend12 (3992 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (4088 : BitVec 12) + signExtend12 (4088 : BitVec 12)
        + signExtend12 (0 : BitVec 12)
      = sp + signExtend12 (3936 : BitVec 12) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; congr 1
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

end EvmAsm.Evm64
