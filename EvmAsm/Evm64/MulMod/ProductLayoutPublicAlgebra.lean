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

private theorem carryOrEqAdd {x y cin : Word} (hcin : cin.toNat ≤ 1) :
    let psum := x + y
    let ca := if BitVec.ult psum y then (1 : Word) else 0
    let res := psum + cin
    let cb := if BitVec.ult res cin then (1 : Word) else 0
    ca ||| cb = ca + cb := by
  intro psum ca res cb
  apply BitVec.eq_of_toNat_eq
  rw [EvmWord.combined_carry_toNat hcin]
  have hca : ca.toNat = (x.toNat + y.toNat) / 2^64 := EvmWord.carry_toNat
  have hpsum : psum.toNat = (x.toNat + y.toNat) % 2^64 := BitVec.toNat_add x y
  have hcb : cb.toNat = (psum.toNat + cin.toNat) / 2^64 := EvmWord.carry_toNat
  rw [BitVec.toNat_add, hca, hcb, hpsum]
  have hx := x.isLt
  have hy := y.isLt
  have hcin_lt := cin.isLt
  have hmod : (x.toNat + y.toNat) % 2^64 < 2^64 := Nat.mod_lt _ (by omega)
  omega

/-- The RV64 `OR` used to combine the two carry bits of an add-partial high limb
    agrees with ordinary Word addition. -/
theorem mulModAddPartialHiCarry_eq_add (hi lo a b : Word) :
    mulModAddPartialHiCarry hi lo a b =
      mulModAddPartialHiBaseCarry hi a b + mulModAddPartialHiCarryFromLo hi lo a b := by
  have h_carry : (mulModAddPartialLoCarry lo a b).toNat ≤ 1 := by
    unfold mulModAddPartialLoCarry
    split <;> decide
  simpa [mulModAddPartialHiCarry, mulModAddPartialHiBaseCarry,
    mulModAddPartialHiCarryFromLo, mulModAddPartialHiValue,
    mulModAddPartialHiBaseValue, mulModAddPartialHiProduct] using
      (carryOrEqAdd (x := hi) (y := mulModAddPartialHiProduct a b)
        (cin := mulModAddPartialLoCarry lo a b) h_carry)

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
