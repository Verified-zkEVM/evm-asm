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


private theorem mulhuToNatLe (a b : Word) : (rv64_mulhu a b).toNat ≤ 2^64 - 2 := by
  rw [EvmWord.rv64_mulhu_toNat]
  have h1 : a.toNat ≤ 2^64 - 1 := by
    have := a.isLt
    omega
  have h2 : b.toNat ≤ 2^64 - 1 := by
    have := b.isLt
    omega
  have h3 : a.toNat * b.toNat ≤ (2^64 - 1) * (2^64 - 1) := Nat.mul_le_mul h1 h2
  suffices (2^64 - 1) * (2^64 - 1) / 2^64 = 2^64 - 2 by
    exact Nat.le_trans (Nat.div_le_div_right h3) (Nat.le_of_eq this)
  norm_num

/-- The two-step high carry of an add-partial is the same carry bit as adding
    the high product and incoming low carry before checking overflow. -/
theorem mulModAddPartialHiCarry_eq_singleCarry (hi lo a b : Word) :
    mulModAddPartialHiCarry hi lo a b =
      if BitVec.ult (hi + (mulModAddPartialHiProduct a b + mulModAddPartialLoCarry lo a b))
          (mulModAddPartialHiProduct a b + mulModAddPartialLoCarry lo a b) then
        (1 : Word)
      else
        0 := by
  apply BitVec.eq_of_toNat_eq
  rw [mulModAddPartialHiCarry_eq_add]
  rw [BitVec.toNat_add]
  simp only [mulModAddPartialHiBaseCarry, mulModAddPartialHiCarryFromLo,
    mulModAddPartialHiValue, mulModAddPartialHiBaseValue, mulModAddPartialHiProduct]
  have h_carry : (mulModAddPartialLoCarry lo a b).toNat ≤ 1 := by
    unfold mulModAddPartialLoCarry
    split <;> decide
  have h_prod : (rv64_mulhu a b).toNat ≤ 2^64 - 2 := mulhuToNatLe a b
  have h_sum_lt : (rv64_mulhu a b + mulModAddPartialLoCarry lo a b).toNat =
      (rv64_mulhu a b).toNat + (mulModAddPartialLoCarry lo a b).toNat := by
    rw [BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt]
    omega
  change ((if BitVec.ult (hi + rv64_mulhu a b) (rv64_mulhu a b) then (1 : Word) else 0).toNat +
        (if BitVec.ult ((hi + rv64_mulhu a b) + mulModAddPartialLoCarry lo a b)
          (mulModAddPartialLoCarry lo a b) then (1 : Word) else 0).toNat) % 2 ^ 64 =
    (if BitVec.ult (hi + (rv64_mulhu a b + mulModAddPartialLoCarry lo a b))
      (rv64_mulhu a b + mulModAddPartialLoCarry lo a b) then (1 : Word) else 0).toNat
  rw [EvmWord.carry_toNat (x := hi) (y := rv64_mulhu a b)]
  rw [EvmWord.carry_toNat (x := hi + rv64_mulhu a b) (y := mulModAddPartialLoCarry lo a b)]
  rw [EvmWord.carry_toNat (x := hi) (y := rv64_mulhu a b + mulModAddPartialLoCarry lo a b)]
  rw [BitVec.toNat_add, h_sum_lt]
  have hhi := hi.isLt
  omega

/-- Variant of `mulModAddPartialHiCarry_eq_singleCarry` with the incoming high
    limb on the right, matching the product-algebra expansions. -/
theorem mulModAddPartialHiCarry_eq_singleCarry_right (hi lo a b : Word) :
    mulModAddPartialHiCarry hi lo a b =
      if BitVec.ult ((mulModAddPartialHiProduct a b + mulModAddPartialLoCarry lo a b) + hi)
          (mulModAddPartialHiProduct a b + mulModAddPartialLoCarry lo a b) then
        (1 : Word)
      else
        0 := by
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  rw [BitVec.add_comm hi]

theorem mulModAddPartialLoCarry_zero (a b : Word) :
    mulModAddPartialLoCarry 0 a b = 0 := by
  unfold mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  simp [BitVec.ult]

theorem mulModAddPartialHiCarry_zero_zero (a b : Word) :
    mulModAddPartialHiCarry 0 0 a b = 0 := by
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  simp [BitVec.ult]

theorem mulModCarryStepCarry_zero_zero :
    mulModCarryStepCarry 0 0 = (0 : Word) := by
  unfold mulModCarryStepCarry
  decide

theorem mulModProductLayoutCall00Carry104_zero (a b : EvmWord) :
    mulModProductLayoutCall00Carry104 a b = 0 := by
  unfold mulModProductLayoutCall00Carry104
  exact mulModAddPartialHiCarry_zero_zero (a.getLimbN 0) (b.getLimbN 0)

theorem mulModProductLayoutCall00Carry112_zero (a b : EvmWord) :
    mulModProductLayoutCall00Carry112 a b = 0 := by
  unfold mulModProductLayoutCall00Carry112
  rw [mulModProductLayoutCall00Carry104_zero]
  exact mulModCarryStepCarry_zero_zero

theorem mulModProductLayoutCall00P112_zero (a b : EvmWord) :
    mulModProductLayoutCall00P112 a b = 0 := by
  unfold mulModProductLayoutCall00P112 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry104_zero]
  rfl

theorem mulModProductLayoutCall00P120_zero (a b : EvmWord) :
    mulModProductLayoutCall00P120 a b = 0 := by
  unfold mulModProductLayoutCall00P120 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry112_zero]
  rfl

theorem mulModProductLayoutCall00P104_eq_mulhu (a b : EvmWord) :
    mulModProductLayoutCall00P104 a b = rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) := by
  unfold mulModProductLayoutCall00P104 mulModAddPartialHiValue mulModAddPartialHiBaseValue
  rw [mulModAddPartialLoCarry_zero]
  simp [mulModAddPartialHiProduct]

theorem mulModProductLayoutCall01Carry112_zero (a b : EvmWord) :
    mulModProductLayoutCall01Carry112 a b = 0 := by
  unfold mulModProductLayoutCall01Carry112
  rw [mulModAddPartialHiCarry_eq_singleCarry, mulModProductLayoutCall00P112_zero,
    mulModProductLayoutCall00P104_eq_mulhu]
  simp [mulModAddPartialHiProduct, BitVec.ult_eq_decide]

theorem mulModProductLayoutCall01P120_zero (a b : EvmWord) :
    mulModProductLayoutCall01P120 a b = 0 := by
  unfold mulModProductLayoutCall01P120 mulModCarryStepValue
  rw [mulModProductLayoutCall01Carry112_zero, mulModProductLayoutCall00P120_zero]
  rfl

theorem mulModProductLayoutCall02Carry112_eq_singleCarry_right (a b : EvmWord) :
    mulModProductLayoutCall02Carry112 a b =
      if BitVec.ult ((mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 1) +
            mulModAddPartialLoCarry (mulModProductLayoutCall01P104 a b)
              (a.getLimbN 0) (b.getLimbN 1)) + mulModProductLayoutCall01P112 a b)
          (mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 1) +
            mulModAddPartialLoCarry (mulModProductLayoutCall01P104 a b)
              (a.getLimbN 0) (b.getLimbN 1)) then
        (1 : Word)
      else
        0 := by
  unfold mulModProductLayoutCall02Carry112
  rw [mulModAddPartialHiCarry_eq_singleCarry_right]

theorem mulModProductLayoutCall02P120_eq_carry112 (a b : EvmWord) :
    mulModProductLayoutCall02P120 a b = mulModProductLayoutCall02Carry112 a b := by
  unfold mulModProductLayoutCall02P120 mulModCarryStepValue
  rw [mulModProductLayoutCall01P120_zero]
  simp

theorem mulModProductLayoutCall02Carry112_eq_add (a b : EvmWord) :
    mulModProductLayoutCall02Carry112 a b =
      mulModAddPartialHiBaseCarry (mulModProductLayoutCall01P112 a b)
        (a.getLimbN 0) (b.getLimbN 1) +
      mulModAddPartialHiCarryFromLo (mulModProductLayoutCall01P112 a b)
        (mulModProductLayoutCall01P104 a b) (a.getLimbN 0) (b.getLimbN 1) := by
  unfold mulModProductLayoutCall02Carry112
  exact mulModAddPartialHiCarry_eq_add _ _ _ _

theorem mulModProductLayoutCall03Carry120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall03Carry120 a b =
      mulModAddPartialHiBaseCarry (mulModProductLayoutCall02P120 a b)
        (a.getLimbN 2) (b.getLimbN 0) +
      mulModAddPartialHiCarryFromLo (mulModProductLayoutCall02P120 a b)
        (mulModProductLayoutCall02P112 a b) (a.getLimbN 2) (b.getLimbN 0) := by
  unfold mulModProductLayoutCall03Carry120
  exact mulModAddPartialHiCarry_eq_add _ _ _ _

theorem mulModProductLayoutCall04Carry120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall04Carry120 a b =
      mulModAddPartialHiBaseCarry (mulModProductLayoutCall03P120 a b)
        (a.getLimbN 1) (b.getLimbN 1) +
      mulModAddPartialHiCarryFromLo (mulModProductLayoutCall03P120 a b)
        (mulModProductLayoutCall03P112 a b) (a.getLimbN 1) (b.getLimbN 1) := by
  unfold mulModProductLayoutCall04Carry120
  exact mulModAddPartialHiCarry_eq_add _ _ _ _

theorem mulModProductLayoutCall05Carry120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall05Carry120 a b =
      mulModAddPartialHiBaseCarry (mulModProductLayoutCall04P120 a b)
        (a.getLimbN 0) (b.getLimbN 2) +
      mulModAddPartialHiCarryFromLo (mulModProductLayoutCall04P120 a b)
        (mulModProductLayoutCall04P112 a b) (a.getLimbN 0) (b.getLimbN 2) := by
  unfold mulModProductLayoutCall05Carry120
  exact mulModAddPartialHiCarry_eq_add _ _ _ _

theorem mulModProductLayoutCall03P120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall03P120 a b =
      mulModProductLayoutCall02P120 a b +
        (mulModAddPartialHiProduct (a.getLimbN 2) (b.getLimbN 0) +
          mulModAddPartialLoCarry (mulModProductLayoutCall02P112 a b)
            (a.getLimbN 2) (b.getLimbN 0)) := by
  unfold mulModProductLayoutCall03P120 mulModAddPartialHiValue mulModAddPartialHiBaseValue
  ac_rfl

theorem mulModProductLayoutCall04P120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall04P120 a b =
      mulModProductLayoutCall03P120 a b +
        (mulModAddPartialHiProduct (a.getLimbN 1) (b.getLimbN 1) +
          mulModAddPartialLoCarry (mulModProductLayoutCall03P112 a b)
            (a.getLimbN 1) (b.getLimbN 1)) := by
  unfold mulModProductLayoutCall04P120 mulModAddPartialHiValue mulModAddPartialHiBaseValue
  ac_rfl

theorem mulModProductLayoutCall05P120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall05P120 a b =
      mulModProductLayoutCall04P120 a b +
        (mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 2) +
          mulModAddPartialLoCarry (mulModProductLayoutCall04P112 a b)
            (a.getLimbN 0) (b.getLimbN 2)) := by
  unfold mulModProductLayoutCall05P120 mulModAddPartialHiValue mulModAddPartialHiBaseValue
  ac_rfl

theorem mulModProductLayoutCall06P120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall06P120 a b =
      mulModProductLayoutCall05P120 a b +
        mulModAddPartialLoProduct (a.getLimbN 3) (b.getLimbN 0) := by
  unfold mulModProductLayoutCall06P120 mulModAddPartialLoValue
  ac_rfl

theorem mulModProductLayoutCall07P120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall07P120 a b =
      mulModProductLayoutCall06P120 a b +
        mulModAddPartialLoProduct (a.getLimbN 2) (b.getLimbN 1) := by
  unfold mulModProductLayoutCall07P120 mulModAddPartialLoValue
  ac_rfl

theorem mulModProductLayoutCall08P120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall08P120 a b =
      mulModProductLayoutCall07P120 a b +
        mulModAddPartialLoProduct (a.getLimbN 1) (b.getLimbN 2) := by
  unfold mulModProductLayoutCall08P120 mulModAddPartialLoValue
  ac_rfl

theorem mulModProductLayoutCall09P120_eq_add (a b : EvmWord) :
    mulModProductLayoutCall09P120 a b =
      mulModProductLayoutCall08P120 a b +
        mulModAddPartialLoProduct (a.getLimbN 0) (b.getLimbN 3) := by
  unfold mulModProductLayoutCall09P120 mulModAddPartialLoValue
  ac_rfl

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
