/-
  EvmAsm.Evm64.MulMod.ProductLayoutPublicAlgebra

  Algebra bridges from the concrete product-layout aliases to the public
  low-limb postcondition cells.
-/

import EvmAsm.Evm64.MulMod.ProductLayoutCall15
import EvmAsm.Evm64.MulMod.ProductLayoutCarryChain
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

private theorem carryAddAssocLeft (x y z : Word) :
    (if BitVec.ult (x + y) x then (1 : Word) else 0) +
        (if BitVec.ult ((x + y) + z) z then (1 : Word) else 0) =
      (if BitVec.ult (y + z) z then (1 : Word) else 0) +
        (if BitVec.ult ((y + z) + x) x then (1 : Word) else 0) := by
  rw [show (if BitVec.ult (x + y) x then (1 : Word) else 0) =
      (if BitVec.ult (y + x) x then (1 : Word) else 0) by rw [BitVec.add_comm x y]]
  rw [show ((x + y) + z) = ((y + x) + z) by rw [BitVec.add_comm x y]]
  apply BitVec.eq_of_toNat_eq
  repeat rw [BitVec.toNat_add]
  repeat rw [EvmWord.carry_toNat]
  repeat rw [BitVec.toNat_add]
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
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

theorem mulModAddPartialHiCarry_bvzero_zero (a b : Word) :
    mulModAddPartialHiCarry (0#64) (0#64) a b = 0 := by
  unfold mulModAddPartialHiCarry mulModAddPartialHiBaseCarry mulModAddPartialHiCarryFromLo
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseValue mulModAddPartialLoCarry
  unfold mulModAddPartialLoValue mulModAddPartialLoProduct mulModAddPartialHiProduct
  simp [BitVec.ult]

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

theorem mulModProductLayoutCall00Carry120_zero (a b : EvmWord) :
    mulModProductLayoutCall00Carry120 a b = 0 := by
  unfold mulModProductLayoutCall00Carry120
  rw [mulModProductLayoutCall00Carry112_zero]
  exact mulModCarryStepCarry_zero_zero

theorem mulModProductLayoutCall00P128_zero (a b : EvmWord) :
    mulModProductLayoutCall00P128 a b = 0 := by
  unfold mulModProductLayoutCall00P128 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry120_zero]
  rfl

theorem mulModProductLayoutCall01Carry120_zero (a b : EvmWord) :
    mulModProductLayoutCall01Carry120 a b = 0 := by
  unfold mulModProductLayoutCall01Carry120
  rw [mulModProductLayoutCall01Carry112_zero, mulModProductLayoutCall00P120_zero]
  exact mulModCarryStepCarry_zero_zero

theorem mulModProductLayoutCall01P128_zero (a b : EvmWord) :
    mulModProductLayoutCall01P128 a b = 0 := by
  unfold mulModProductLayoutCall01P128 mulModCarryStepValue
  rw [mulModProductLayoutCall01Carry120_zero, mulModProductLayoutCall00P128_zero]
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

theorem mulModProductLayoutCall02P112_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall02P112 a b =
      rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
        rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) +
        (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
              a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
            (a.getLimbN 0 * b.getLimbN 1) then
            (1 : Word)
          else
            0) +
        (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
              a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
            (1 : Word)
          else
            0) := by
  simp [mulModProductLayoutCall02P112, mulModProductLayoutCall01P112,
    mulModProductLayoutCall01P104, mulModProductLayoutCall00P104,
    mulModProductLayoutCall00P112, mulModProductLayoutCall00Carry104,
    mulModAddPartialHiCarry_bvzero_zero,
    mulModAddPartialLoValue, mulModAddPartialHiValue,
    mulModAddPartialLoProduct, mulModAddPartialHiProduct,
    mulModAddPartialHiBaseValue, mulModAddPartialLoCarry,
    mulModCarryStepValue, BitVec.ult]
  ac_rfl

theorem mulModProductLayoutCall02Carry120_zero (a b : EvmWord) :
    mulModProductLayoutCall02Carry120 a b = 0 := by
  unfold mulModProductLayoutCall02Carry120
  rw [mulModProductLayoutCall01P120_zero]
  rw [mulModProductLayoutCall02Carry112_eq_singleCarry_right]
  by_cases h : BitVec.ult ((mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 1) +
        mulModAddPartialLoCarry (mulModProductLayoutCall01P104 a b) (a.getLimbN 0) (b.getLimbN 1)) +
      mulModProductLayoutCall01P112 a b)
      (mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 1) +
        mulModAddPartialLoCarry (mulModProductLayoutCall01P104 a b) (a.getLimbN 0) (b.getLimbN 1))
  · simp [mulModCarryStepCarry, BitVec.ult]
  · simp [h, mulModCarryStepCarry]

theorem mulModProductLayoutCall02P128_zero (a b : EvmWord) :
    mulModProductLayoutCall02P128 a b = 0 := by
  unfold mulModProductLayoutCall02P128 mulModCarryStepValue
  rw [mulModProductLayoutCall02Carry120_zero, mulModProductLayoutCall01P128_zero]
  rfl

theorem mulModProductLayoutCall02P120_eq_carry112 (a b : EvmWord) :
    mulModProductLayoutCall02P120 a b = mulModProductLayoutCall02Carry112 a b := by
  unfold mulModProductLayoutCall02P120 mulModCarryStepValue
  rw [mulModProductLayoutCall01P120_zero]
  simp

theorem mulModProductLayoutCall02P120_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall02P120 a b =
      if BitVec.ult
          ((rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
                  (a.getLimbN 0 * b.getLimbN 1) then
                  (1 : Word)
                else
                  0)) +
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0)
                  (a.getLimbN 1 * b.getLimbN 0) then
                  (1 : Word)
                else
                  0)))
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
            (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                  a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
                (a.getLimbN 0 * b.getLimbN 1) then
                (1 : Word)
              else
                0)) then
        (1 : Word)
      else
        0 := by
  rw [mulModProductLayoutCall02P120_eq_carry112]
  rw [mulModProductLayoutCall02Carry112_eq_singleCarry_right]
  simp [mulModProductLayoutCall01P104, mulModProductLayoutCall01P112,
    mulModProductLayoutCall00P104, mulModProductLayoutCall00P112,
    mulModProductLayoutCall00Carry104, mulModAddPartialHiCarry_bvzero_zero,
    mulModAddPartialLoValue, mulModAddPartialHiValue,
    mulModAddPartialLoProduct, mulModAddPartialHiProduct,
    mulModAddPartialHiBaseValue, mulModAddPartialLoCarry, mulModCarryStepValue,
    BitVec.ult]

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

theorem mulModProductLayoutCall03P112_eq_add (a b : EvmWord) :
    mulModProductLayoutCall03P112 a b =
      mulModProductLayoutCall02P112 a b +
        mulModAddPartialLoProduct (a.getLimbN 2) (b.getLimbN 0) := by
  unfold mulModProductLayoutCall03P112 mulModAddPartialLoValue
  ac_rfl

theorem mulModProductLayoutCall04P112_eq_add (a b : EvmWord) :
    mulModProductLayoutCall04P112 a b =
      mulModProductLayoutCall03P112 a b +
        mulModAddPartialLoProduct (a.getLimbN 1) (b.getLimbN 1) := by
  unfold mulModProductLayoutCall04P112 mulModAddPartialLoValue
  ac_rfl

theorem mulModProductLayoutCall05P112_eq_add (a b : EvmWord) :
    mulModProductLayoutCall05P112 a b =
      mulModProductLayoutCall04P112 a b +
        mulModAddPartialLoProduct (a.getLimbN 0) (b.getLimbN 2) := by
  unfold mulModProductLayoutCall05P112 mulModAddPartialLoValue
  ac_rfl

theorem mulModProductLayoutCall03P112_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall03P112 a b =
      rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
        rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) +
        (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
              a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
            (a.getLimbN 0 * b.getLimbN 1) then
            (1 : Word)
          else
            0) +
        (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
              a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
            (1 : Word)
          else
            0) +
        a.getLimbN 2 * b.getLimbN 0 := by
  rw [mulModProductLayoutCall03P112_eq_add]
  rw [mulModProductLayoutCall02P112_eq_expanded]
  simp only [mulModAddPartialLoProduct]

theorem mulModProductLayoutCall04P112_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall04P112 a b =
      rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
        rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) +
        (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
              a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
            (a.getLimbN 0 * b.getLimbN 1) then
            (1 : Word)
          else
            0) +
        (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
              a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
            (1 : Word)
          else
            0) +
        a.getLimbN 2 * b.getLimbN 0 +
        a.getLimbN 1 * b.getLimbN 1 := by
  rw [mulModProductLayoutCall04P112_eq_add]
  rw [mulModProductLayoutCall03P112_eq_expanded]
  simp only [mulModAddPartialLoProduct]

theorem mulModProductLayoutCall03LoCarry_eq_expanded (a b : EvmWord) :
    mulModAddPartialLoCarry (mulModProductLayoutCall02P112 a b)
        (a.getLimbN 2) (b.getLimbN 0) =
      if BitVec.ult
          ((rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
              rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
                  (a.getLimbN 0 * b.getLimbN 1) then
                  (1 : Word)
                else
                  0) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
                  (1 : Word)
                else
                  0)) +
            a.getLimbN 2 * b.getLimbN 0)
          (a.getLimbN 2 * b.getLimbN 0) then
        (1 : Word)
      else
        0 := by
  unfold mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  rw [mulModProductLayoutCall02P112_eq_expanded]

theorem mulModProductLayoutCall04LoCarry_eq_expanded (a b : EvmWord) :
    mulModAddPartialLoCarry (mulModProductLayoutCall03P112 a b)
        (a.getLimbN 1) (b.getLimbN 1) =
      if BitVec.ult
          ((rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
              rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
                  (a.getLimbN 0 * b.getLimbN 1) then
                  (1 : Word)
                else
                  0) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
                  (1 : Word)
                else
                  0) +
              a.getLimbN 2 * b.getLimbN 0) +
            a.getLimbN 1 * b.getLimbN 1)
          (a.getLimbN 1 * b.getLimbN 1) then
        (1 : Word)
      else
        0 := by
  unfold mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  rw [mulModProductLayoutCall03P112_eq_expanded]

theorem mulModProductLayoutCall05LoCarry_eq_expanded (a b : EvmWord) :
    mulModAddPartialLoCarry (mulModProductLayoutCall04P112 a b)
        (a.getLimbN 0) (b.getLimbN 2) =
      if BitVec.ult
          ((rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
              rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
                  (a.getLimbN 0 * b.getLimbN 1) then
                  (1 : Word)
                else
                  0) +
              (if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
                    a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
                  (1 : Word)
                else
                  0) +
              a.getLimbN 2 * b.getLimbN 0 +
              a.getLimbN 1 * b.getLimbN 1) +
            a.getLimbN 0 * b.getLimbN 2)
          (a.getLimbN 0 * b.getLimbN 2) then
        (1 : Word)
      else
        0 := by
  unfold mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  rw [mulModProductLayoutCall04P112_eq_expanded]

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

theorem mulModProductLayoutCall09P120_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall09P120 a b =
      mulModProductLayoutCall02P120 a b +
        (mulModAddPartialHiProduct (a.getLimbN 2) (b.getLimbN 0) +
          mulModAddPartialLoCarry (mulModProductLayoutCall02P112 a b)
            (a.getLimbN 2) (b.getLimbN 0)) +
        (mulModAddPartialHiProduct (a.getLimbN 1) (b.getLimbN 1) +
          mulModAddPartialLoCarry (mulModProductLayoutCall03P112 a b)
            (a.getLimbN 1) (b.getLimbN 1)) +
        (mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 2) +
          mulModAddPartialLoCarry (mulModProductLayoutCall04P112 a b)
            (a.getLimbN 0) (b.getLimbN 2)) +
        mulModAddPartialLoProduct (a.getLimbN 3) (b.getLimbN 0) +
        mulModAddPartialLoProduct (a.getLimbN 2) (b.getLimbN 1) +
        mulModAddPartialLoProduct (a.getLimbN 1) (b.getLimbN 2) +
        mulModAddPartialLoProduct (a.getLimbN 0) (b.getLimbN 3) := by
  rw [mulModProductLayoutCall09P120_eq_add]
  rw [mulModProductLayoutCall08P120_eq_add]
  rw [mulModProductLayoutCall07P120_eq_add]
  rw [mulModProductLayoutCall06P120_eq_add]
  rw [mulModProductLayoutCall05P120_eq_add]
  rw [mulModProductLayoutCall04P120_eq_add]
  rw [mulModProductLayoutCall03P120_eq_add]

theorem mulModProductLayoutCall09P120_eq_expanded_raw (a b : EvmWord) :
    mulModProductLayoutCall09P120 a b =
      mulModProductLayoutCall02P120 a b +
        (mulModAddPartialHiProduct (a.getLimbN 2) (b.getLimbN 0) +
          mulModAddPartialLoCarry (mulModProductLayoutCall02P112 a b)
            (a.getLimbN 2) (b.getLimbN 0)) +
        (mulModAddPartialHiProduct (a.getLimbN 1) (b.getLimbN 1) +
          mulModAddPartialLoCarry (mulModProductLayoutCall03P112 a b)
            (a.getLimbN 1) (b.getLimbN 1)) +
        (mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 2) +
          mulModAddPartialLoCarry (mulModProductLayoutCall04P112 a b)
            (a.getLimbN 0) (b.getLimbN 2)) +
        a.getLimbN 3 * b.getLimbN 0 +
        a.getLimbN 2 * b.getLimbN 1 +
        a.getLimbN 1 * b.getLimbN 2 +
        a.getLimbN 0 * b.getLimbN 3 := by
  rw [mulModProductLayoutCall09P120_eq_expanded]
  simp only [mulModAddPartialLoProduct]

theorem mulModProductLayoutCall09P120_eq_expanded_lowCarries (a b : EvmWord) :
    mulModProductLayoutCall09P120 a b =
      mulModProductLayoutCall02P120 a b +
        (mulModAddPartialHiProduct (a.getLimbN 2) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall02P112 a b +
                a.getLimbN 2 * b.getLimbN 0) (a.getLimbN 2 * b.getLimbN 0) then
              (1 : Word)
            else
              0)) +
        (mulModAddPartialHiProduct (a.getLimbN 1) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall03P112 a b +
                a.getLimbN 1 * b.getLimbN 1) (a.getLimbN 1 * b.getLimbN 1) then
              (1 : Word)
            else
              0)) +
        (mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall04P112 a b +
                a.getLimbN 0 * b.getLimbN 2) (a.getLimbN 0 * b.getLimbN 2) then
              (1 : Word)
            else
              0)) +
        a.getLimbN 3 * b.getLimbN 0 +
        a.getLimbN 2 * b.getLimbN 1 +
        a.getLimbN 1 * b.getLimbN 2 +
        a.getLimbN 0 * b.getLimbN 3 := by
  rw [mulModProductLayoutCall09P120_eq_expanded_raw]
  unfold mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  ac_rfl

theorem mulModProductLayoutCall09P120_eq_layoutCarryChain (a b : EvmWord) :
    let a0 := a.getLimbN 0; let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2; let a3 := a.getLimbN 3
    let b0 := b.getLimbN 0; let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2; let b3 := b.getLimbN 3
    let c0_hi_a0b0 := rv64_mulhu a0 b0
    let c0_lo_a1b0 := a1 * b0
    let c0_r1 := c0_hi_a0b0 + c0_lo_a1b0
    let c0_c1 := if BitVec.ult c0_r1 c0_lo_a1b0 then (1 : Word) else 0
    let c1_lo := a0 * b1
    let c1_hi := rv64_mulhu a0 b1
    let c1_r1 := c0_r1 + c1_lo
    let c1_c1 := if BitVec.ult c1_r1 c1_lo then (1 : Word) else 0
    let c0_hi_a1b0 := rv64_mulhu a1 b0
    let p112 := c1_hi + c0_hi_a1b0 + c1_c1 + c0_c1
    let call02P120 := if BitVec.ult (c1_hi + c1_c1 + (c0_hi_a1b0 + c0_c1))
        (c1_hi + c1_c1) then (1 : Word) else 0
    let p112a := p112 + a2 * b0
    let carry03 := if BitVec.ult p112a (a2 * b0) then (1 : Word) else 0
    let p112b := p112a + a1 * b1
    let carry04 := if BitVec.ult p112b (a1 * b1) then (1 : Word) else 0
    let p112c := p112b + a0 * b2
    let carry05 := if BitVec.ult p112c (a0 * b2) then (1 : Word) else 0
    mulModProductLayoutCall09P120 a b =
      call02P120 + (rv64_mulhu a2 b0 + carry03) +
        (rv64_mulhu a1 b1 + carry04) +
        (rv64_mulhu a0 b2 + carry05) +
        a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 := by
  simp only
  rw [mulModProductLayoutCall09P120_eq_expanded_lowCarries]
  rw [mulModProductLayoutCall02P120_eq_expanded]
  rw [mulModProductLayoutCall02P112_eq_expanded]
  rw [mulModProductLayoutCall03P112_eq_expanded]
  rw [mulModProductLayoutCall04P112_eq_expanded]
  simp only [mulModAddPartialHiProduct]

theorem mulModProductLayoutCall09P120_eq_mul_limb3 (a b : EvmWord) :
    mulModProductLayoutCall09P120 a b = (a * b).getLimbN 3 := by
  rw [← EvmWord.getLimb_as_getLimbN_3, ← productLimb_three_eq_mul_getLimb]
  rw [productLimb_three_eq_mul_correct_limb3]
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  rw [mulModProductLayoutCall09P120_eq_layoutCarryChain]
  set ca : Word := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
      (a.getLimbN 0 * b.getLimbN 1) then (1 : Word) else 0
  set cb : Word := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
    (1 : Word) else 0
  set A : Word := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) + ca
  set B : Word := rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) + cb
  set P : Word := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1) +
    rv64_mulhu (a.getLimbN 1) (b.getLimbN 0) + ca + cb
  set Z : Word := a.getLimbN 2 * b.getLimbN 0
  have hP : P = A + B := by
    subst P; subst A; subst B; ac_rfl
  rw [hP]
  rw [show (if BitVec.ult (A + B) A then (1 : Word) else 0) +
      (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
        (if BitVec.ult ((A + B) + Z) Z then (1 : Word) else 0)) =
      ((if BitVec.ult (A + B) A then (1 : Word) else 0) +
        (if BitVec.ult ((A + B) + Z) Z then (1 : Word) else 0)) +
        rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) by ac_rfl]
  rw [carryAddAssocLeft A B Z]
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

theorem mulModProductLayoutCall03P128_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall03P128 a b =
      mulModProductLayoutCall02P128 a b +
        (if BitVec.ult (mulModProductLayoutCall02P120 a b +
            (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
              (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                  (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
              (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                  (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) := by
  unfold mulModProductLayoutCall03P128 mulModCarryStepValue mulModProductLayoutCall03Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutCall03P128_eq_highCarry (a b : EvmWord) :
    mulModProductLayoutCall03P128 a b =
        (if BitVec.ult (mulModProductLayoutCall02P120 a b +
            (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
              (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                  (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
              (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                  (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) := by
  rw [mulModProductLayoutCall03P128_eq_expanded]
  rw [mulModProductLayoutCall02P128_zero]
  simp

theorem mulModProductLayoutCall04P128_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall04P128 a b =
      mulModProductLayoutCall03P128 a b +
        (if BitVec.ult (mulModProductLayoutCall03P120 a b +
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) := by
  unfold mulModProductLayoutCall04P128 mulModCarryStepValue mulModProductLayoutCall04Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutCall04P128_eq_highCarry (a b : EvmWord) :
    mulModProductLayoutCall04P128 a b =
      (if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
        (if BitVec.ult (mulModProductLayoutCall03P120 a b +
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) := by
  rw [mulModProductLayoutCall04P128_eq_expanded]
  rw [mulModProductLayoutCall03P128_eq_highCarry]

theorem mulModProductLayoutCall05P128_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall05P128 a b =
      mulModProductLayoutCall04P128 a b +
        (if BitVec.ult (mulModProductLayoutCall04P120 a b +
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) := by
  unfold mulModProductLayoutCall05P128 mulModCarryStepValue mulModProductLayoutCall05Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutCall05P128_eq_highCarry (a b : EvmWord) :
    mulModProductLayoutCall05P128 a b =
      ((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
        (if BitVec.ult (mulModProductLayoutCall03P120 a b +
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0)) +
        (if BitVec.ult (mulModProductLayoutCall04P120 a b +
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) := by
  rw [mulModProductLayoutCall05P128_eq_expanded]
  rw [mulModProductLayoutCall04P128_eq_highCarry]

theorem mulModProductLayoutCall09P128_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall09P128 a b =
      mulModProductLayoutCall05P128 a b +
        (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
              (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
              (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
              (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
          (if BitVec.ult (mulModProductLayoutCall08P120 a b + a.getLimbN 0 * b.getLimbN 3)
              (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0)) := by
  unfold mulModProductLayoutCall09P128 mulModProductLayoutCall08P128
    mulModProductLayoutCall07P128 mulModProductLayoutCall06P128
  simp only [mulModAddPartialHiValue, mulModAddPartialHiBaseValue,
    mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  ac_rfl

theorem mulModProductLayoutCall09P128_eq_highCarry (a b : EvmWord) :
    mulModProductLayoutCall09P128 a b =
      (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
        (if BitVec.ult (mulModProductLayoutCall03P120 a b +
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0)) +
        (if BitVec.ult (mulModProductLayoutCall04P120 a b +
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0)) +
        (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
              (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
              (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
              (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
          (if BitVec.ult (mulModProductLayoutCall08P120 a b + a.getLimbN 0 * b.getLimbN 3)
              (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0)) := by
  rw [mulModProductLayoutCall09P128_eq_expanded]
  rw [mulModProductLayoutCall05P128_eq_highCarry]

/-- Folded column-4 value of the product-layout accumulator.  This is the
    first high product limb before the later column-5/6/7 carries are applied. -/
@[irreducible] def mulModProductLayoutColumn4Value (a b : EvmWord) : Word :=
  mulModProductLayoutCall09P128 a b +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

/-- Carry prefix entering column 4 from the three final low-column-3 additions. -/
@[irreducible] def mulModProductLayoutColumn4PrefixCarry (a b : EvmWord) : Word :=
  ((if BitVec.ult (mulModProductLayoutCall02P120 a b +
        (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
              (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
        (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
              (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
      (1 : Word)
    else
      0) +
    (if BitVec.ult (mulModProductLayoutCall03P120 a b +
        (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
              (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
        (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
              (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
      (1 : Word)
    else
      0)) +
    (if BitVec.ult (mulModProductLayoutCall04P120 a b +
        (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
              (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
        (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
              (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
      (1 : Word)
    else
      0)

/-- Column-4 value with all prefix carries exposed and folded behind a stable name. -/
@[irreducible] def mulModProductLayoutColumn4ExpandedValue (a b : EvmWord) : Word :=
  mulModProductLayoutColumn4PrefixCarry a b +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult (mulModProductLayoutCall08P120 a b + a.getLimbN 0 * b.getLimbN 3)
          (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

/-- Column-4 value with the low-column-3 feed cells expanded into the
    running sums that generate the carry bits. -/
@[irreducible] def mulModProductLayoutColumn4LowFeedValue (a b : EvmWord) : Word :=
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed05 := mulModProductLayoutCall04P120 a b + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  let feed08 := feed07 + a.getLimbN 1 * b.getLimbN 2
  mulModProductLayoutColumn4PrefixCarry a b +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (feed05 + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (feed06 + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (feed07 + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult (feed08 + a.getLimbN 0 * b.getLimbN 3)
          (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

/-- Column-4 low-feed value with the final low-column-3 sum replaced by
    the already proven low product limb 3. -/
@[irreducible] def mulModProductLayoutColumn4Limb3FeedValue (a b : EvmWord) : Word :=
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed05 := mulModProductLayoutCall04P120 a b + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  mulModProductLayoutColumn4PrefixCarry a b +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (feed05 + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (feed06 + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (feed07 + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult ((a * b).getLimbN 3) (a.getLimbN 0 * b.getLimbN 3) then
        (1 : Word)
      else
        0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

/-- Column-4 limb-3-feed value with the prefix carry unfolded into
    the same `feed05` column-2 carry that feeds the following high-column additions. -/
@[irreducible] def mulModProductLayoutColumn4PrefixFeedValue (a b : EvmWord) : Word :=
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed05 := mulModProductLayoutCall04P120 a b + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
      (if BitVec.ult (mulModProductLayoutCall03P120 a b +
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
      (if BitVec.ult feed05 (hi02 + carry02) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (feed05 + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (feed06 + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (feed07 + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult ((a * b).getLimbN 3) (a.getLimbN 0 * b.getLimbN 3) then
        (1 : Word)
      else
        0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

/-- Column-4 prefix-feed value with the call04 high feed expanded into
    the preceding call03 feed plus the `a1*b1` high/carry contribution. -/
@[irreducible] def mulModProductLayoutColumn4Call04FeedValue (a b : EvmWord) : Word :=
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed04 := mulModProductLayoutCall03P120 a b + (hi11 + carry11)
  let feed05 := feed04 + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
      (if BitVec.ult feed04 (hi11 + carry11) then (1 : Word) else 0)) +
      (if BitVec.ult feed05 (hi02 + carry02) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (feed05 + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (feed06 + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (feed07 + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult ((a * b).getLimbN 3) (a.getLimbN 0 * b.getLimbN 3) then
        (1 : Word)
      else
        0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

/-- Column-4 call04-feed value with the call03 high feed expanded into
    the preceding call02 feed plus the `a2*b0` high/carry contribution. -/
@[irreducible] def mulModProductLayoutColumn4Call03FeedValue (a b : EvmWord) : Word :=
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
      (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed03 := mulModProductLayoutCall02P120 a b + (hi20 + carry20)
  let feed04 := feed03 + (hi11 + carry11)
  let feed05 := feed04 + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult feed03 (hi20 + carry20) then (1 : Word) else 0) +
      (if BitVec.ult feed04 (hi11 + carry11) then (1 : Word) else 0)) +
      (if BitVec.ult feed05 (hi02 + carry02) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (feed05 + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (feed06 + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (feed07 + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult ((a * b).getLimbN 3) (a.getLimbN 0 * b.getLimbN 3) then
        (1 : Word)
      else
        0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

theorem mulModProductLayoutCall12P128_eq_expanded (a b : EvmWord) :
    mulModProductLayoutCall12P128 a b =
      mulModProductLayoutCall09P128 a b +
        a.getLimbN 3 * b.getLimbN 1 +
        a.getLimbN 2 * b.getLimbN 2 +
        a.getLimbN 1 * b.getLimbN 3 := by
  unfold mulModProductLayoutCall12P128 mulModProductLayoutCall11P128
    mulModProductLayoutCall10P128
  simp only [mulModAddPartialLoValue, mulModAddPartialLoProduct]

theorem mulModProductLayoutCall12P128_eq_column4Value (a b : EvmWord) :
    mulModProductLayoutCall12P128 a b = mulModProductLayoutColumn4Value a b := by
  rw [mulModProductLayoutCall12P128_eq_expanded]
  unfold mulModProductLayoutColumn4Value
  rfl

/-- Adapter for the remaining column-4 arithmetic proof: once the folded column
    value is shown to match `mulHigh` limb 0, the concrete call12 cell follows. -/
theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_column4Value
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Value a b = (EvmWord.mulHigh a b).getLimbN 0) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  rw [mulModProductLayoutCall12P128_eq_column4Value, h_col]

theorem mulModProductLayoutColumn4Value_eq_mulHigh_getLimbN_zero_of_productLimb_four
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Value a b = productLimb a b 4) :
    mulModProductLayoutColumn4Value a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  rw [h_col, productLimb_four_eq_mulHigh_getLimbN_zero]

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_productLimb_four
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Value a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_column4Value
    (mulModProductLayoutColumn4Value_eq_mulHigh_getLimbN_zero_of_productLimb_four h_col)

theorem mulModProductLayoutCall12P128_eq_highCarry (a b : EvmWord) :
    mulModProductLayoutCall12P128 a b =
      ((((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
        (if BitVec.ult (mulModProductLayoutCall03P120 a b +
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
              (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                  (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0)) +
        (if BitVec.ult (mulModProductLayoutCall04P120 a b +
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0)) +
        (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
              (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
              (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
              (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
          (if BitVec.ult (mulModProductLayoutCall08P120 a b + a.getLimbN 0 * b.getLimbN 3)
              (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0))) +
        a.getLimbN 3 * b.getLimbN 1 +
        a.getLimbN 2 * b.getLimbN 2 +
        a.getLimbN 1 * b.getLimbN 3 := by
  rw [mulModProductLayoutCall12P128_eq_expanded]
  rw [mulModProductLayoutCall09P128_eq_highCarry]

theorem mulModProductLayoutCall12P128_eq_expanded_highCarries (a b : EvmWord) :
    mulModProductLayoutCall12P128 a b =
      mulModProductLayoutCall04P128 a b +
        (if BitVec.ult (mulModProductLayoutCall04P120 a b +
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) +
        (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
              (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
              (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
              (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
          (if BitVec.ult (mulModProductLayoutCall08P120 a b + a.getLimbN 0 * b.getLimbN 3)
              (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0)) +
        a.getLimbN 3 * b.getLimbN 1 +
        a.getLimbN 2 * b.getLimbN 2 +
        a.getLimbN 1 * b.getLimbN 3 := by
  rw [mulModProductLayoutCall12P128_eq_expanded]
  rw [mulModProductLayoutCall09P128_eq_expanded]
  rw [mulModProductLayoutCall05P128_eq_expanded]

theorem mulModProductLayoutColumn4Value_eq_expanded_highCarries (a b : EvmWord) :
    mulModProductLayoutColumn4Value a b =
      mulModProductLayoutCall04P128 a b +
        (if BitVec.ult (mulModProductLayoutCall04P120 a b +
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
            (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
              (if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
                  (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
          (1 : Word)
        else
          0) +
        (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
          (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
              (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
          (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
              (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
          (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
              (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
        (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
          (if BitVec.ult (mulModProductLayoutCall08P120 a b + a.getLimbN 0 * b.getLimbN 3)
              (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0)) +
        a.getLimbN 3 * b.getLimbN 1 +
        a.getLimbN 2 * b.getLimbN 2 +
        a.getLimbN 1 * b.getLimbN 3 := by
  rw [← mulModProductLayoutCall12P128_eq_column4Value]
  exact mulModProductLayoutCall12P128_eq_expanded_highCarries a b

theorem mulModProductLayoutColumn4Value_eq_expandedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Value a b = mulModProductLayoutColumn4ExpandedValue a b := by
  rw [mulModProductLayoutColumn4Value_eq_expanded_highCarries]
  rw [mulModProductLayoutCall04P128_eq_highCarry]
  unfold mulModProductLayoutColumn4ExpandedValue mulModProductLayoutColumn4PrefixCarry
  ac_rfl

theorem mulModProductLayoutColumn4ExpandedValue_eq_lowFeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4ExpandedValue a b =
      mulModProductLayoutColumn4LowFeedValue a b := by
  unfold mulModProductLayoutColumn4ExpandedValue mulModProductLayoutColumn4LowFeedValue
  rw [mulModProductLayoutCall08P120_eq_add]
  rw [mulModProductLayoutCall07P120_eq_add]
  rw [mulModProductLayoutCall06P120_eq_add]
  rw [mulModProductLayoutCall05P120_eq_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue
    mulModAddPartialLoProduct
  rfl

theorem mulModProductLayoutColumn4LowFeedValue_eq_limb3FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4LowFeedValue a b =
      mulModProductLayoutColumn4Limb3FeedValue a b := by
  unfold mulModProductLayoutColumn4LowFeedValue mulModProductLayoutColumn4Limb3FeedValue
  rw [← mulModProductLayoutCall09P120_eq_mul_limb3]
  rw [mulModProductLayoutCall09P120_eq_add]
  rw [mulModProductLayoutCall08P120_eq_add]
  rw [mulModProductLayoutCall07P120_eq_add]
  rw [mulModProductLayoutCall06P120_eq_add]
  rw [mulModProductLayoutCall05P120_eq_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue
    mulModAddPartialLoProduct
  rfl

theorem mulModProductLayoutColumn4Limb3FeedValue_eq_prefixFeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Limb3FeedValue a b =
      mulModProductLayoutColumn4PrefixFeedValue a b := by
  unfold mulModProductLayoutColumn4Limb3FeedValue mulModProductLayoutColumn4PrefixFeedValue
    mulModProductLayoutColumn4PrefixCarry
  rfl

theorem mulModProductLayoutColumn4PrefixFeedValue_eq_call04FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4PrefixFeedValue a b =
      mulModProductLayoutColumn4Call04FeedValue a b := by
  unfold mulModProductLayoutColumn4PrefixFeedValue mulModProductLayoutColumn4Call04FeedValue
  rw [mulModProductLayoutCall04P120_eq_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue
    mulModAddPartialLoProduct
  rfl

theorem mulModProductLayoutColumn4Call04FeedValue_eq_call03FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Call04FeedValue a b =
      mulModProductLayoutColumn4Call03FeedValue a b := by
  unfold mulModProductLayoutColumn4Call04FeedValue mulModProductLayoutColumn4Call03FeedValue
  rw [mulModProductLayoutCall03P120_eq_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue
    mulModAddPartialLoProduct
  rfl

theorem mulModProductLayoutColumn4Value_eq_productLimb_four_of_expandedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Value a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Value_eq_expandedValue, h_col]

theorem mulModProductLayoutColumn4Value_eq_mulHigh_getLimbN_zero_of_expandedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Value a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutColumn4Value_eq_mulHigh_getLimbN_zero_of_productLimb_four
    (mulModProductLayoutColumn4Value_eq_productLimb_four_of_expandedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_expandedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_column4Value
    (mulModProductLayoutColumn4Value_eq_mulHigh_getLimbN_zero_of_expandedValue h_col)

theorem mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_lowFeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4LowFeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4ExpandedValue_eq_lowFeedValue, h_col]

theorem mulModProductLayoutColumn4Value_eq_productLimb_four_of_lowFeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4LowFeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Value a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Value_eq_productLimb_four_of_expandedValue
    (mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_lowFeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_lowFeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4LowFeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_expandedValue
    (mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_lowFeedValue h_col)

theorem mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_limb3FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb3FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4LowFeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4LowFeedValue_eq_limb3FeedValue, h_col]

theorem mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_limb3FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb3FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_lowFeedValue
    (mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_limb3FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_limb3FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb3FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_lowFeedValue
    (mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_limb3FeedValue h_col)

theorem mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_prefixFeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4PrefixFeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Limb3FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Limb3FeedValue_eq_prefixFeedValue, h_col]

theorem mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_prefixFeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4PrefixFeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4LowFeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_limb3FeedValue
    (mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_prefixFeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_prefixFeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4PrefixFeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_limb3FeedValue
    (mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_prefixFeedValue h_col)

theorem mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_call04FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4PrefixFeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4PrefixFeedValue_eq_call04FeedValue, h_col]

theorem mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_call04FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Limb3FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_prefixFeedValue
    (mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_call04FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call04FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_prefixFeedValue
    (mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_call04FeedValue h_col)

theorem mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_call03FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call04FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call04FeedValue_eq_call03FeedValue, h_col]

theorem mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_call03FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4PrefixFeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_call04FeedValue
    (mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_call03FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call03FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call04FeedValue
    (mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_call03FeedValue h_col)

end EvmAsm.Evm64
