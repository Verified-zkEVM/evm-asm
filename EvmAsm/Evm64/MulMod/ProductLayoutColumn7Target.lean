import EvmAsm.Evm64.MulMod.ProductLayoutColumn6Target

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra


private theorem mulModAddPartialHiCarry_toNat_le_one_forColumn7 (hi lo x y : Word) :
    (mulModAddPartialHiCarry hi lo x y).toNat ≤ 1 := by
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  rw [mulModProductLayoutCarryRightEqTrue_toNat]
  rw [BitVec.toNat_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue
    mulModAddPartialLoProduct
  rw [mulModProductLayoutCarryRightEqTrue_toNat]
  have h_hi := hi.isLt
  have h_term : ((rv64_mulhu x y).toNat + (lo.toNat + (x * y).toNat) / 2 ^ 64) %
      2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  omega

private theorem mulModCarryStepCarry_zero_of_small_forColumn7
    (limb carry : Word) (h_limb : limb.toNat ≤ 3) (h_carry : carry.toNat ≤ 1) :
    mulModCarryStepCarry limb carry = 0 := by
  apply BitVec.eq_of_toNat_eq
  change (mulModCarryStepCarry limb carry).toNat = 0
  unfold mulModCarryStepCarry
  rw [mulModProductLayoutCarryRight_toNat]
  omega

private theorem mulModCarryStepValue_zero_zero_forColumn7 :
    mulModCarryStepValue (0 : Word) (0 : Word) = 0 := by
  rfl


private theorem mulModCarryStepCarry_twoBits_zero_forColumn7 (p q : Bool) :
    mulModCarryStepCarry (if p then (1 : Word) else 0) (if q then (1 : Word) else 0) =
      0 := by
  cases p <;> cases q <;> decide

private theorem mulModCarryStepCarry_twoPlusOneBits_zero_forColumn7 (p q r : Bool) :
    mulModCarryStepCarry ((if p then (1 : Word) else 0) + (if q then (1 : Word) else 0))
      (if r then (1 : Word) else 0) = 0 := by
  cases p <;> cases q <;> cases r <;> decide

private theorem mulModProductLayoutCall00Carry128_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall00Carry128 a b = 0 := by
  unfold mulModProductLayoutCall00Carry128
  rw [mulModProductLayoutCall00Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall00P136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall00P136 a b = 0 := by
  unfold mulModProductLayoutCall00P136 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry128_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall00Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall00Carry136 a b = 0 := by
  unfold mulModProductLayoutCall00Carry136
  rw [mulModProductLayoutCall00Carry128_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall00P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall00P144 a b = 0 := by
  unfold mulModProductLayoutCall00P144 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall00Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall00Carry144 a b = 0 := by
  unfold mulModProductLayoutCall00Carry144
  rw [mulModProductLayoutCall00Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall00P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall00P152 a b = 0 := by
  unfold mulModProductLayoutCall00P152 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall01Carry128_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall01Carry128 a b = 0 := by
  unfold mulModProductLayoutCall01Carry128
  rw [mulModProductLayoutCall00P128_zero, mulModProductLayoutCall01Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall01P136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall01P136 a b = 0 := by
  unfold mulModProductLayoutCall01P136 mulModCarryStepValue
  rw [mulModProductLayoutCall00P136_zero_forColumn7, mulModProductLayoutCall01Carry128_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall01Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall01Carry136 a b = 0 := by
  unfold mulModProductLayoutCall01Carry136
  rw [mulModProductLayoutCall00P136_zero_forColumn7, mulModProductLayoutCall01Carry128_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall01P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall01P144 a b = 0 := by
  unfold mulModProductLayoutCall01P144 mulModCarryStepValue
  rw [mulModProductLayoutCall00P144_zero_forColumn7, mulModProductLayoutCall01Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall01Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall01Carry144 a b = 0 := by
  unfold mulModProductLayoutCall01Carry144
  rw [mulModProductLayoutCall00P144_zero_forColumn7, mulModProductLayoutCall01Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall01P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall01P152 a b = 0 := by
  unfold mulModProductLayoutCall01P152 mulModCarryStepValue
  rw [mulModProductLayoutCall00P152_zero_forColumn7, mulModProductLayoutCall01Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall02Carry128_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall02Carry128 a b = 0 := by
  unfold mulModProductLayoutCall02Carry128
  rw [mulModProductLayoutCall01P128_zero, mulModProductLayoutCall02Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall02P136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall02P136 a b = 0 := by
  unfold mulModProductLayoutCall02P136 mulModCarryStepValue
  rw [mulModProductLayoutCall01P136_zero_forColumn7, mulModProductLayoutCall02Carry128_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall02Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall02Carry136 a b = 0 := by
  unfold mulModProductLayoutCall02Carry136
  rw [mulModProductLayoutCall01P136_zero_forColumn7, mulModProductLayoutCall02Carry128_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall02P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall02P144 a b = 0 := by
  unfold mulModProductLayoutCall02P144 mulModCarryStepValue
  rw [mulModProductLayoutCall01P144_zero_forColumn7, mulModProductLayoutCall02Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall02Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall02Carry144 a b = 0 := by
  unfold mulModProductLayoutCall02Carry144
  rw [mulModProductLayoutCall01P144_zero_forColumn7, mulModProductLayoutCall02Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall02P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall02P152 a b = 0 := by
  unfold mulModProductLayoutCall02P152 mulModCarryStepValue
  rw [mulModProductLayoutCall01P152_zero_forColumn7, mulModProductLayoutCall02Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall03Carry128_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall03Carry128 a b = 0 := by
  unfold mulModProductLayoutCall03Carry128
  rw [mulModProductLayoutCall02P128_zero]
  unfold mulModCarryStepCarry
  simp [BitVec.ult]

private theorem mulModProductLayoutCall03P136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall03P136 a b = 0 := by
  unfold mulModProductLayoutCall03P136 mulModCarryStepValue
  rw [mulModProductLayoutCall02P136_zero_forColumn7, mulModProductLayoutCall03Carry128_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall03Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall03Carry136 a b = 0 := by
  unfold mulModProductLayoutCall03Carry136
  rw [mulModProductLayoutCall02P136_zero_forColumn7, mulModProductLayoutCall03Carry128_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall03P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall03P144 a b = 0 := by
  unfold mulModProductLayoutCall03P144 mulModCarryStepValue
  rw [mulModProductLayoutCall02P144_zero_forColumn7, mulModProductLayoutCall03Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall03Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall03Carry144 a b = 0 := by
  unfold mulModProductLayoutCall03Carry144
  rw [mulModProductLayoutCall02P144_zero_forColumn7, mulModProductLayoutCall03Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall03P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall03P152 a b = 0 := by
  unfold mulModProductLayoutCall03P152 mulModCarryStepValue
  rw [mulModProductLayoutCall02P152_zero_forColumn7, mulModProductLayoutCall03Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall04Carry128_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall04Carry128 a b = 0 := by
  unfold mulModProductLayoutCall04Carry128
  rw [mulModProductLayoutCall03P128_eq_highCarry]
  unfold mulModProductLayoutCall04Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  exact mulModCarryStepCarry_twoBits_zero_forColumn7 _ _

private theorem mulModProductLayoutCall04P136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall04P136 a b = 0 := by
  unfold mulModProductLayoutCall04P136 mulModCarryStepValue
  rw [mulModProductLayoutCall03P136_zero_forColumn7, mulModProductLayoutCall04Carry128_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall04Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall04Carry136 a b = 0 := by
  unfold mulModProductLayoutCall04Carry136
  rw [mulModProductLayoutCall03P136_zero_forColumn7, mulModProductLayoutCall04Carry128_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall04P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall04P144 a b = 0 := by
  unfold mulModProductLayoutCall04P144 mulModCarryStepValue
  rw [mulModProductLayoutCall03P144_zero_forColumn7, mulModProductLayoutCall04Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall04Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall04Carry144 a b = 0 := by
  unfold mulModProductLayoutCall04Carry144
  rw [mulModProductLayoutCall03P144_zero_forColumn7, mulModProductLayoutCall04Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall04P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall04P152 a b = 0 := by
  unfold mulModProductLayoutCall04P152 mulModCarryStepValue
  rw [mulModProductLayoutCall03P152_zero_forColumn7, mulModProductLayoutCall04Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall05Carry128_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall05Carry128 a b = 0 := by
  unfold mulModProductLayoutCall05Carry128
  rw [mulModProductLayoutCall04P128_eq_highCarry]
  unfold mulModProductLayoutCall05Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  exact mulModCarryStepCarry_twoPlusOneBits_zero_forColumn7 _ _ _

private theorem mulModProductLayoutCall05P136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall05P136 a b = 0 := by
  unfold mulModProductLayoutCall05P136 mulModCarryStepValue
  rw [mulModProductLayoutCall04P136_zero_forColumn7, mulModProductLayoutCall05Carry128_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall05Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall05Carry136 a b = 0 := by
  unfold mulModProductLayoutCall05Carry136
  rw [mulModProductLayoutCall04P136_zero_forColumn7, mulModProductLayoutCall05Carry128_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall05P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall05P144 a b = 0 := by
  unfold mulModProductLayoutCall05P144 mulModCarryStepValue
  rw [mulModProductLayoutCall04P144_zero_forColumn7, mulModProductLayoutCall05Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall05Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall05Carry144 a b = 0 := by
  unfold mulModProductLayoutCall05Carry144
  rw [mulModProductLayoutCall04P144_zero_forColumn7, mulModProductLayoutCall05Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall05P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall05P152 a b = 0 := by
  unfold mulModProductLayoutCall05P152 mulModCarryStepValue
  rw [mulModProductLayoutCall04P152_zero_forColumn7, mulModProductLayoutCall05Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall06Carry128_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall06Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall06Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn7 _ _ _ _

private theorem mulModProductLayoutCall07Carry128_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall07Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall07Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn7 _ _ _ _

private theorem mulModProductLayoutCall08Carry128_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall08Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall08Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn7 _ _ _ _

private theorem mulModProductLayoutCall09Carry128_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall09Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall09Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn7 _ _ _ _

private theorem mulModProductLayoutCall06P136_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall06P136 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall06P136 mulModCarryStepValue
  rw [mulModProductLayoutCall05P136_zero_forColumn7]
  simpa using mulModProductLayoutCall06Carry128_toNat_le_one_forColumn7 a b

private theorem mulModProductLayoutCall06Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall06Carry136 a b = 0 := by
  unfold mulModProductLayoutCall06Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn7 _ _
    (by rw [mulModProductLayoutCall05P136_zero_forColumn7]; decide)
    (mulModProductLayoutCall06Carry128_toNat_le_one_forColumn7 a b)

private theorem mulModProductLayoutCall06P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall06P144 a b = 0 := by
  unfold mulModProductLayoutCall06P144 mulModCarryStepValue
  rw [mulModProductLayoutCall05P144_zero_forColumn7, mulModProductLayoutCall06Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall06Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall06Carry144 a b = 0 := by
  unfold mulModProductLayoutCall06Carry144
  rw [mulModProductLayoutCall05P144_zero_forColumn7, mulModProductLayoutCall06Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall06P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall06P152 a b = 0 := by
  unfold mulModProductLayoutCall06P152 mulModCarryStepValue
  rw [mulModProductLayoutCall05P152_zero_forColumn7, mulModProductLayoutCall06Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall07P136_toNat_le_two_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall07P136 a b).toNat ≤ 2 := by
  unfold mulModProductLayoutCall07P136 mulModCarryStepValue
  rw [BitVec.toNat_add]
  have h6 := mulModProductLayoutCall06P136_toNat_le_one_forColumn7 a b
  have h7 := mulModProductLayoutCall07Carry128_toNat_le_one_forColumn7 a b
  omega

private theorem mulModProductLayoutCall07Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall07Carry136 a b = 0 := by
  unfold mulModProductLayoutCall07Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn7 _ _
    (by exact Nat.le_trans (mulModProductLayoutCall06P136_toNat_le_one_forColumn7 a b) (by decide))
    (mulModProductLayoutCall07Carry128_toNat_le_one_forColumn7 a b)

private theorem mulModProductLayoutCall07P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall07P144 a b = 0 := by
  unfold mulModProductLayoutCall07P144 mulModCarryStepValue
  rw [mulModProductLayoutCall06P144_zero_forColumn7, mulModProductLayoutCall07Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall07Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall07Carry144 a b = 0 := by
  unfold mulModProductLayoutCall07Carry144
  rw [mulModProductLayoutCall06P144_zero_forColumn7, mulModProductLayoutCall07Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall07P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall07P152 a b = 0 := by
  unfold mulModProductLayoutCall07P152 mulModCarryStepValue
  rw [mulModProductLayoutCall06P152_zero_forColumn7, mulModProductLayoutCall07Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall08P136_toNat_le_three_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall08P136 a b).toNat ≤ 3 := by
  unfold mulModProductLayoutCall08P136 mulModCarryStepValue
  rw [BitVec.toNat_add]
  have h7 := mulModProductLayoutCall07P136_toNat_le_two_forColumn7 a b
  have h8 := mulModProductLayoutCall08Carry128_toNat_le_one_forColumn7 a b
  omega

private theorem mulModProductLayoutCall08Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall08Carry136 a b = 0 := by
  unfold mulModProductLayoutCall08Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn7 _ _
    (by exact Nat.le_trans (mulModProductLayoutCall07P136_toNat_le_two_forColumn7 a b) (by decide))
    (mulModProductLayoutCall08Carry128_toNat_le_one_forColumn7 a b)

private theorem mulModProductLayoutCall08P144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall08P144 a b = 0 := by
  unfold mulModProductLayoutCall08P144 mulModCarryStepValue
  rw [mulModProductLayoutCall07P144_zero_forColumn7, mulModProductLayoutCall08Carry136_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall08Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall08Carry144 a b = 0 := by
  unfold mulModProductLayoutCall08Carry144
  rw [mulModProductLayoutCall07P144_zero_forColumn7, mulModProductLayoutCall08Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall08P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall08P152 a b = 0 := by
  unfold mulModProductLayoutCall08P152 mulModCarryStepValue
  rw [mulModProductLayoutCall07P152_zero_forColumn7, mulModProductLayoutCall08Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall09Carry136_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall09Carry136 a b = 0 := by
  unfold mulModProductLayoutCall09Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn7 _ _
    (mulModProductLayoutCall08P136_toNat_le_three_forColumn7 a b)
    (mulModProductLayoutCall09Carry128_toNat_le_one_forColumn7 a b)

private theorem mulModProductLayoutCall09Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall09Carry144 a b = 0 := by
  unfold mulModProductLayoutCall09Carry144
  rw [mulModProductLayoutCall08P144_zero_forColumn7, mulModProductLayoutCall09Carry136_zero_forColumn7]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall09P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall09P152 a b = 0 := by
  unfold mulModProductLayoutCall09P152 mulModCarryStepValue
  rw [mulModProductLayoutCall08P152_zero_forColumn7, mulModProductLayoutCall09Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall10Carry136_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall10Carry136 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall10Carry136
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn7 _ _ _ _

private theorem mulModProductLayoutCall11Carry136_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall11Carry136 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall11Carry136
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn7 _ _ _ _

private theorem mulModProductLayoutCall12Carry136_toNat_le_one_forColumn7 (a b : EvmWord) :
    (mulModProductLayoutCall12Carry136 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall12Carry136
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn7 _ _ _ _

private theorem mulModProductLayoutCall10Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall10Carry144 a b = 0 := by
  unfold mulModProductLayoutCall10Carry144
  exact mulModCarryStepCarry_zero_of_small_forColumn7 _ _
    (by rw [mulModProductLayoutCall09P144_toNat_zero]; decide)
    (mulModProductLayoutCall10Carry136_toNat_le_one_forColumn7 a b)

private theorem mulModProductLayoutCall10P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall10P152 a b = 0 := by
  unfold mulModProductLayoutCall10P152
  rw [mulModProductLayoutCall09P152_zero_forColumn7, mulModProductLayoutCall10Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall11Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall11Carry144 a b = 0 := by
  unfold mulModProductLayoutCall11Carry144
  exact mulModCarryStepCarry_zero_of_small_forColumn7 _ _
    (by
      rw [mulModProductLayoutCall10P144]
      rw [mulModCarryStepValue]
      rw [BitVec.toNat_add]
      rw [mulModProductLayoutCall09P144_toNat_zero]
      have h := mulModProductLayoutCall10Carry136_toNat_le_one_forColumn7 a b
      omega)
    (mulModProductLayoutCall11Carry136_toNat_le_one_forColumn7 a b)

private theorem mulModProductLayoutCall11P152_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall11P152 a b = 0 := by
  unfold mulModProductLayoutCall11P152
  rw [mulModProductLayoutCall10P152_zero_forColumn7, mulModProductLayoutCall11Carry144_zero_forColumn7]
  rfl

private theorem mulModProductLayoutCall12Carry144_zero_forColumn7 (a b : EvmWord) :
    mulModProductLayoutCall12Carry144 a b = 0 := by
  unfold mulModProductLayoutCall12Carry144
  exact mulModCarryStepCarry_zero_of_small_forColumn7 _ _
    (by
      unfold mulModProductLayoutCall11P144 mulModCarryStepValue
      rw [BitVec.toNat_add]
      have h_p10 : (mulModProductLayoutCall10P144 a b).toNat ≤ 1 := by
        unfold mulModProductLayoutCall10P144 mulModCarryStepValue
        rw [BitVec.toNat_add]
        rw [mulModProductLayoutCall09P144_toNat_zero]
        have h := mulModProductLayoutCall10Carry136_toNat_le_one_forColumn7 a b
        omega
      have h_c11 := mulModProductLayoutCall11Carry136_toNat_le_one_forColumn7 a b
      omega)
    (mulModProductLayoutCall12Carry136_toNat_le_one_forColumn7 a b)

/-- The offset-152 product-layout cell is still zero before column-five carry propagation. -/
theorem mulModProductLayoutCall12P152_zero (a b : EvmWord) :
    mulModProductLayoutCall12P152 a b = 0 := by
  unfold mulModProductLayoutCall12P152
  rw [mulModProductLayoutCall11P152_zero_forColumn7, mulModProductLayoutCall12Carry144_zero_forColumn7]
  rfl

/-- Nat view of `mulModProductLayoutCall12P152_zero`. -/
theorem mulModProductLayoutCall12P152_toNat_zero (a b : EvmWord) :
    (mulModProductLayoutCall12P152 a b).toNat = 0 := by
  rw [mulModProductLayoutCall12P152_zero]
  rfl

/-- The finalized product-layout column-seven cell at offset 152. -/
def mulModProductLayoutColumn7Value (a b : EvmWord) : Word :=
  mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
    (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3)

/-- The concrete call15 P152 cell is the folded column-seven target. -/
theorem mulModProductLayoutCall15P152Value_eq_column7Value (a b : EvmWord) :
    mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
      mulModProductLayoutColumn7Value a b := by
  rfl

/-- The concrete call15 P152 cell has the same product-limb-7 proof obligation
    as the folded column-seven target. -/
theorem mulModProductLayoutCall15P152Value_eq_productLimb_seven_iff_column7Value
    (a b : EvmWord) :
    (mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
        (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        productLimb a b 7) ↔
      (mulModProductLayoutColumn7Value a b = productLimb a b 7) := by
  rfl

/-- The concrete call15 high-limb target is equivalent to the folded
    column-seven product-limb obligation. -/
theorem mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three_iff_column7Value
    (a b : EvmWord) :
    (mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
        (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3) ↔
      (mulModProductLayoutColumn7Value a b = productLimb a b 7) := by
  rw [← productLimb_seven_eq_mulHigh_getLimbN_three]
  exact mulModProductLayoutCall15P152Value_eq_productLimb_seven_iff_column7Value a b

/-- The folded column-seven product-limb target is the same as the direct
    mulHigh limb3 target. -/
theorem mulModProductLayoutColumn7Value_eq_mulHigh_getLimbN_three_iff_productLimb_seven
    (a b : EvmWord) :
    (mulModProductLayoutColumn7Value a b =
        (EvmWord.mulHigh a b).getLimbN 3) ↔
      (mulModProductLayoutColumn7Value a b = productLimb a b 7) := by
  rw [← productLimb_seven_eq_mulHigh_getLimbN_three]

theorem mulModProductLayoutColumn7Value_eq_mulHigh_getLimbN_three_of_productLimb_seven
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutColumn7Value a b =
      (EvmWord.mulHigh a b).getLimbN 3 := by
  exact (mulModProductLayoutColumn7Value_eq_mulHigh_getLimbN_three_iff_productLimb_seven
    a b).2 h_col

theorem mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three_of_column7Value_mulHigh
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn7Value a b =
      (EvmWord.mulHigh a b).getLimbN 3) :
    mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3 := by
  rw [mulModProductLayoutCall15P152Value_eq_column7Value, h_col]

theorem mulModProductLayoutColumn7Value_eq_productLimb_seven_of_call15P152Value_mulHigh
    {a b : EvmWord}
    (h_col : mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3) :
    mulModProductLayoutColumn7Value a b = productLimb a b 7 := by
  exact (mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three_iff_column7Value
    a b).1 h_col

end EvmAsm.Evm64
