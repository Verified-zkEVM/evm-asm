import EvmAsm.Evm64.MulMod.ProductLayoutColumn5Target

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra


private theorem mulModProductLayoutCarryTelescoping5ForLimb6
    (d0 d1 d2 d3 d4 c1 c2 c3 c4 c5 w : Nat)
    (h0 : w * c1 + d0 % w = d0)
    (h1 : w * c2 + (d1 + c1) % w = d1 + c1)
    (h2 : w * c3 + (d2 + c2) % w = d2 + c2)
    (h3 : w * c4 + (d3 + c3) % w = d3 + c3)
    (h4 : w * c5 + (d4 + c4) % w = d4 + c4) :
    d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 + d4 * w ^ 4 =
      d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
        (d3 + c3) % w * w ^ 3 + (d4 + c4) % w * w ^ 4 + c5 * w ^ 5 := by
  have h_d1 : d1 + c1 = (d1 + c1) % w + w * c2 := by
    linarith [h1]
  have h_d2 : d2 + c2 = (d2 + c2) % w + w * c3 := by
    linarith [h2]
  have h_d3 : d3 + c3 = (d3 + c3) % w + w * c4 := by
    linarith [h3]
  have h_d4 : d4 + c4 = (d4 + c4) % w + w * c5 := by
    linarith [h4]
  calc
    d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 + d4 * w ^ 4
        = (d0 % w + w * c1) + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 +
            d4 * w ^ 4 := by
          linarith [h0]
    _ = d0 % w + (d1 + c1) * w + d2 * w ^ 2 + d3 * w ^ 3 +
          d4 * w ^ 4 := by
          ring
    _ = d0 % w + ((d1 + c1) % w + w * c2) * w + d2 * w ^ 2 +
          d3 * w ^ 3 + d4 * w ^ 4 := by
          rw [← h_d1]
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) * w ^ 2 +
          d3 * w ^ 3 + d4 * w ^ 4 := by
          ring
    _ = d0 % w + (d1 + c1) % w * w + ((d2 + c2) % w + w * c3) * w ^ 2 +
          d3 * w ^ 3 + d4 * w ^ 4 := by
          rw [← h_d2]
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) * w ^ 3 + d4 * w ^ 4 := by
          ring
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          ((d3 + c3) % w + w * c4) * w ^ 3 + d4 * w ^ 4 := by
          rw [← h_d3]
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + (d4 + c4) * w ^ 4 := by
          ring
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + ((d4 + c4) % w + w * c5) * w ^ 4 := by
          rw [← h_d4]
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + (d4 + c4) % w * w ^ 4 + c5 * w ^ 5 := by
          ring

private theorem mulModProductLayoutGeoSeriesIdentity5ForLimb6 (w : Nat) (h_w : 0 < w) :
    (w - 1) + (w - 1) * w + (w - 1) * w ^ 2 + (w - 1) * w ^ 3 +
        (w - 1) * w ^ 4 + 1 = w ^ 5 := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

private theorem mulModProductLayoutLowPartBound5ForLimb6
    (d0 d1c1 d2c2 d3c3 d4c4 w : Nat) (h_w : 0 < w)
    (h0 : d0 % w < w) (h1 : d1c1 % w < w) (h2 : d2c2 % w < w)
    (h3 : d3c3 % w < w) (h4 : d4c4 % w < w) :
    d0 % w + d1c1 % w * w + d2c2 % w * w ^ 2 + d3c3 % w * w ^ 3 +
        d4c4 % w * w ^ 4 < w ^ 5 := by
  have h_bound0 : d0 % w ≤ w - 1 := by
    omega
  have h_bound1 : d1c1 % w * w ≤ (w - 1) * w :=
    Nat.mul_le_mul_right w (by omega)
  have h_bound2 : d2c2 % w * w ^ 2 ≤ (w - 1) * w ^ 2 :=
    Nat.mul_le_mul_right (w ^ 2) (by omega)
  have h_bound3 : d3c3 % w * w ^ 3 ≤ (w - 1) * w ^ 3 :=
    Nat.mul_le_mul_right (w ^ 3) (by omega)
  have h_bound4 : d4c4 % w * w ^ 4 ≤ (w - 1) * w ^ 4 :=
    Nat.mul_le_mul_right (w ^ 4) (by omega)
  have h_geo := mulModProductLayoutGeoSeriesIdentity5ForLimb6 w h_w
  linarith [h_bound0, h_bound1, h_bound2, h_bound3, h_bound4, h_geo]

private theorem mulModProductLayoutProductExpansion5ForLimb6
    (a0 a1 a2 a3 b0 b1 b2 b3 w : Nat) :
    (a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) *
        (b0 + b1 * w + b2 * w ^ 2 + b3 * w ^ 3) =
      a0 * b0 + (a0 * b1 + a1 * b0) * w +
        (a0 * b2 + a1 * b1 + a2 * b0) * w ^ 2 +
        (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * w ^ 3 +
        (a1 * b3 + a2 * b2 + a3 * b1) * w ^ 4 +
        (a2 * b3 + a3 * b2) * w ^ 5 + a3 * b3 * w ^ 6 := by
  ring

/-- Schoolbook multiplication identifies product limb six with the carried
    column-six value. -/
theorem mulModProductLayoutSchoolbookLimb6
    (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    let product :=
      (a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192) *
        (b0 + b1 * 2 ^ 64 + b2 * 2 ^ 128 + b3 * 2 ^ 192)
    let d0 := a0 * b0
    let d1 := a0 * b1 + a1 * b0
    let d2 := a0 * b2 + a1 * b1 + a2 * b0
    let d3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
    let d4 := a1 * b3 + a2 * b2 + a3 * b1
    let d5 := a2 * b3 + a3 * b2
    let d6 := a3 * b3
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    let c5 := (d4 + c4) / 2 ^ 64
    let c6 := (d5 + c5) / 2 ^ 64
    product / 2 ^ 384 % 2 ^ 64 = (d6 + c6) % 2 ^ 64 := by
  dsimp only
  set w := (2 : Nat) ^ 64
  have h128 : (2 : Nat) ^ 128 = w ^ 2 := by
    norm_num [w]
  have h192 : (2 : Nat) ^ 192 = w ^ 3 := by
    norm_num [w]
  have h384 : (2 : Nat) ^ 384 = w ^ 6 := by
    rw [show w = (2 : Nat) ^ 64 by rfl, ← Nat.pow_mul]
  rw [h128, h192, h384]
  set d0 := a0 * b0
  set d1 := a0 * b1 + a1 * b0
  set d2 := a0 * b2 + a1 * b1 + a2 * b0
  set d3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
  set d4 := a1 * b3 + a2 * b2 + a3 * b1
  set d5 := a2 * b3 + a3 * b2
  set d6 := a3 * b3
  set c1 := d0 / w
  set c2 := (d1 + c1) / w
  set c3 := (d2 + c2) / w
  set c4 := (d3 + c3) / w
  set c5 := (d4 + c4) / w
  set c6 := (d5 + c5) / w
  set product :=
    (a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) *
      (b0 + b1 * w + b2 * w ^ 2 + b3 * w ^ 3)
  have h_product :
      product = d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 +
        d4 * w ^ 4 + d5 * w ^ 5 + d6 * w ^ 6 := by
    simp only [product, d0, d1, d2, d3, d4, d5, d6]
    exact mulModProductLayoutProductExpansion5ForLimb6 a0 a1 a2 a3 b0 b1 b2 b3 w
  have h_w : (0 : Nat) < w := by
    positivity
  have h_tel :
      d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 + d4 * w ^ 4 =
        d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + (d4 + c4) % w * w ^ 4 + c5 * w ^ 5 :=
    mulModProductLayoutCarryTelescoping5ForLimb6 d0 d1 d2 d3 d4 c1 c2 c3 c4 c5 w
      (Nat.div_add_mod d0 w)
      (Nat.div_add_mod (d1 + c1) w)
      (Nat.div_add_mod (d2 + c2) w)
      (Nat.div_add_mod (d3 + c3) w)
      (Nat.div_add_mod (d4 + c4) w)
  have h_low :
      d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + (d4 + c4) % w * w ^ 4 <
        w ^ 5 :=
    mulModProductLayoutLowPartBound5ForLimb6 d0 (d1 + c1) (d2 + c2) (d3 + c3)
      (d4 + c4) w h_w
      (Nat.mod_lt d0 h_w)
      (Nat.mod_lt (d1 + c1) h_w)
      (Nat.mod_lt (d2 + c2) h_w)
      (Nat.mod_lt (d3 + c3) h_w)
      (Nat.mod_lt (d4 + c4) h_w)
  set low :=
    d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
      (d3 + c3) % w * w ^ 3 + (d4 + c4) % w * w ^ 4
  have h_product_folded :
      product = low + ((d5 + c5) + d6 * w) * w ^ 5 := by
    rw [h_product, h_tel]
    ring
  set high := (d5 + c5) + d6 * w
  have h_div5 : product / w ^ 5 = high := by
    rw [h_product_folded,
      Nat.add_mul_div_right _ _ (by positivity : (0 : Nat) < w ^ 5),
      Nat.div_eq_of_lt h_low, Nat.zero_add]
  have h_pow6 : w ^ 6 = w ^ 5 * w := by ring
  rw [h_pow6, ← Nat.div_div_eq_div_mul, h_div5]
  subst high
  subst c6
  rw [show ((d5 + c5) + d6 * w) / w = d6 + (d5 + c5) / w by
    rw [Nat.add_mul_div_right _ _ h_w]
    ring]


private theorem mulModCarryStepCarry_twoBits_zero_forColumn6 (p q : Bool) :
    mulModCarryStepCarry (if p then (1 : Word) else 0) (if q then (1 : Word) else 0) =
      0 := by
  cases p <;> cases q <;> decide

private theorem mulModCarryStepCarry_twoPlusOneBits_zero_forColumn6 (p q r : Bool) :
    mulModCarryStepCarry ((if p then (1 : Word) else 0) + (if q then (1 : Word) else 0))
      (if r then (1 : Word) else 0) = 0 := by
  cases p <;> cases q <;> cases r <;> decide

private theorem mulModProductLayoutCall00Carry128_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall00Carry128 a b = 0 := by
  unfold mulModProductLayoutCall00Carry128
  rw [mulModProductLayoutCall00Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall00P136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall00P136 a b = 0 := by
  unfold mulModProductLayoutCall00P136 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry128_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall00Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall00Carry136 a b = 0 := by
  unfold mulModProductLayoutCall00Carry136
  rw [mulModProductLayoutCall00Carry128_zero_forColumn6]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall00P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall00P144 a b = 0 := by
  unfold mulModProductLayoutCall00P144 mulModCarryStepValue
  rw [mulModProductLayoutCall00Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall01Carry128_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall01Carry128 a b = 0 := by
  unfold mulModProductLayoutCall01Carry128
  rw [mulModProductLayoutCall00P128_zero, mulModProductLayoutCall01Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall01P136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall01P136 a b = 0 := by
  unfold mulModProductLayoutCall01P136 mulModCarryStepValue
  rw [mulModProductLayoutCall00P136_zero_forColumn6, mulModProductLayoutCall01Carry128_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall01Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall01Carry136 a b = 0 := by
  unfold mulModProductLayoutCall01Carry136
  rw [mulModProductLayoutCall00P136_zero_forColumn6, mulModProductLayoutCall01Carry128_zero_forColumn6]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall01P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall01P144 a b = 0 := by
  unfold mulModProductLayoutCall01P144 mulModCarryStepValue
  rw [mulModProductLayoutCall00P144_zero_forColumn6, mulModProductLayoutCall01Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall02Carry128_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall02Carry128 a b = 0 := by
  unfold mulModProductLayoutCall02Carry128
  rw [mulModProductLayoutCall01P128_zero, mulModProductLayoutCall02Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall02P136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall02P136 a b = 0 := by
  unfold mulModProductLayoutCall02P136 mulModCarryStepValue
  rw [mulModProductLayoutCall01P136_zero_forColumn6, mulModProductLayoutCall02Carry128_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall02Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall02Carry136 a b = 0 := by
  unfold mulModProductLayoutCall02Carry136
  rw [mulModProductLayoutCall01P136_zero_forColumn6, mulModProductLayoutCall02Carry128_zero_forColumn6]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall02P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall02P144 a b = 0 := by
  unfold mulModProductLayoutCall02P144 mulModCarryStepValue
  rw [mulModProductLayoutCall01P144_zero_forColumn6, mulModProductLayoutCall02Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall03Carry128_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall03Carry128 a b = 0 := by
  unfold mulModProductLayoutCall03Carry128
  rw [mulModProductLayoutCall02P128_zero]
  unfold mulModCarryStepCarry
  simp [BitVec.ult]

private theorem mulModProductLayoutCall03P136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall03P136 a b = 0 := by
  unfold mulModProductLayoutCall03P136 mulModCarryStepValue
  rw [mulModProductLayoutCall02P136_zero_forColumn6, mulModProductLayoutCall03Carry128_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall03Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall03Carry136 a b = 0 := by
  unfold mulModProductLayoutCall03Carry136
  rw [mulModProductLayoutCall02P136_zero_forColumn6, mulModProductLayoutCall03Carry128_zero_forColumn6]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall03P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall03P144 a b = 0 := by
  unfold mulModProductLayoutCall03P144 mulModCarryStepValue
  rw [mulModProductLayoutCall02P144_zero_forColumn6, mulModProductLayoutCall03Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall04Carry128_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall04Carry128 a b = 0 := by
  unfold mulModProductLayoutCall04Carry128
  rw [mulModProductLayoutCall03P128_eq_highCarry]
  unfold mulModProductLayoutCall04Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  exact mulModCarryStepCarry_twoBits_zero_forColumn6 _ _

private theorem mulModProductLayoutCall04P136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall04P136 a b = 0 := by
  unfold mulModProductLayoutCall04P136 mulModCarryStepValue
  rw [mulModProductLayoutCall03P136_zero_forColumn6, mulModProductLayoutCall04Carry128_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall04Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall04Carry136 a b = 0 := by
  unfold mulModProductLayoutCall04Carry136
  rw [mulModProductLayoutCall03P136_zero_forColumn6, mulModProductLayoutCall04Carry128_zero_forColumn6]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall04P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall04P144 a b = 0 := by
  unfold mulModProductLayoutCall04P144 mulModCarryStepValue
  rw [mulModProductLayoutCall03P144_zero_forColumn6, mulModProductLayoutCall04Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall05Carry128_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall05Carry128 a b = 0 := by
  unfold mulModProductLayoutCall05Carry128
  rw [mulModProductLayoutCall04P128_eq_highCarry]
  unfold mulModProductLayoutCall05Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  exact mulModCarryStepCarry_twoPlusOneBits_zero_forColumn6 _ _ _

private theorem mulModProductLayoutCall05P136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall05P136 a b = 0 := by
  unfold mulModProductLayoutCall05P136 mulModCarryStepValue
  rw [mulModProductLayoutCall04P136_zero_forColumn6, mulModProductLayoutCall05Carry128_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall05Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall05Carry136 a b = 0 := by
  unfold mulModProductLayoutCall05Carry136
  rw [mulModProductLayoutCall04P136_zero_forColumn6, mulModProductLayoutCall05Carry128_zero_forColumn6]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall05P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall05P144 a b = 0 := by
  unfold mulModProductLayoutCall05P144 mulModCarryStepValue
  rw [mulModProductLayoutCall04P144_zero_forColumn6, mulModProductLayoutCall05Carry136_zero_forColumn6]
  rfl

private theorem mulModCarryStepValue_toNat_forColumn6 (limb carry : Word) :
    (mulModCarryStepValue limb carry).toNat = (limb.toNat + carry.toNat) % 2 ^ 64 := by
  unfold mulModCarryStepValue
  rw [BitVec.toNat_add]

private theorem mulModCarryStepCarry_toNat_forColumn6 (limb carry : Word) :
    (mulModCarryStepCarry limb carry).toNat = (limb.toNat + carry.toNat) / 2 ^ 64 := by
  unfold mulModCarryStepCarry
  exact mulModProductLayoutCarryRight_toNat limb carry

private theorem mulModAddPartialLoValue_toNat_forColumn6 (lo x y : Word) :
    (mulModAddPartialLoValue lo x y).toNat = (lo.toNat + (x * y).toNat) % 2 ^ 64 := by
  unfold mulModAddPartialLoValue mulModAddPartialLoProduct
  rw [BitVec.toNat_add]

private theorem mulModAddPartialHiValue_toNat_forColumn6 (hi lo x y : Word) :
    (mulModAddPartialHiValue hi lo x y).toNat =
      (hi.toNat + ((rv64_mulhu x y).toNat + (lo.toNat + (x * y).toNat) / 2 ^ 64) %
        2 ^ 64) % 2 ^ 64 := by
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseValue mulModAddPartialHiProduct
  rw [BitVec.toNat_add]
  rw [BitVec.toNat_add]
  unfold mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  rw [mulModProductLayoutCarryRightEqTrue_toNat]
  omega

private theorem mulModAddPartialHiCarry_toNat_forColumn6 (hi lo x y : Word) :
    (mulModAddPartialHiCarry hi lo x y).toNat =
      (hi.toNat + ((rv64_mulhu x y).toNat + (lo.toNat + (x * y).toNat) / 2 ^ 64) %
        2 ^ 64) / 2 ^ 64 := by
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  rw [mulModProductLayoutCarryRightEqTrue_toNat]
  rw [BitVec.toNat_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue
    mulModAddPartialLoProduct
  rw [mulModProductLayoutCarryRightEqTrue_toNat]


private theorem mulModProductLayoutCall10P128_toNat_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall10P128 a b).toNat =
      ((mulModProductLayoutCall09P128 a b).toNat +
        (a.getLimbN 3 * b.getLimbN 1).toNat) % 2 ^ 64 := by
  unfold mulModProductLayoutCall10P128
  exact mulModAddPartialLoValue_toNat_forColumn6 _ _ _

private theorem mulModProductLayoutCall10P136_toNat_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall10P136 a b).toNat =
      ((mulModProductLayoutCall09P136 a b).toNat +
        ((rv64_mulhu (a.getLimbN 3) (b.getLimbN 1)).toNat +
          ((mulModProductLayoutCall09P128 a b).toNat +
            (a.getLimbN 3 * b.getLimbN 1).toNat) / 2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
  unfold mulModProductLayoutCall10P136
  exact mulModAddPartialHiValue_toNat_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall11P128_toNat_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall11P128 a b).toNat =
      ((mulModProductLayoutCall10P128 a b).toNat +
        (a.getLimbN 2 * b.getLimbN 2).toNat) % 2 ^ 64 := by
  unfold mulModProductLayoutCall11P128
  exact mulModAddPartialLoValue_toNat_forColumn6 _ _ _

private theorem mulModProductLayoutCall11P136_toNat_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall11P136 a b).toNat =
      ((mulModProductLayoutCall10P136 a b).toNat +
        ((rv64_mulhu (a.getLimbN 2) (b.getLimbN 2)).toNat +
          ((mulModProductLayoutCall10P128 a b).toNat +
            (a.getLimbN 2 * b.getLimbN 2).toNat) / 2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
  unfold mulModProductLayoutCall11P136
  exact mulModAddPartialHiValue_toNat_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall10Carry136_toNat_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall10Carry136 a b).toNat =
      ((mulModProductLayoutCall09P136 a b).toNat +
        ((rv64_mulhu (a.getLimbN 3) (b.getLimbN 1)).toNat +
          ((mulModProductLayoutCall09P128 a b).toNat +
            (a.getLimbN 3 * b.getLimbN 1).toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 := by
  unfold mulModProductLayoutCall10Carry136
  exact mulModAddPartialHiCarry_toNat_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall11Carry136_toNat_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall11Carry136 a b).toNat =
      ((mulModProductLayoutCall10P136 a b).toNat +
        ((rv64_mulhu (a.getLimbN 2) (b.getLimbN 2)).toNat +
          ((mulModProductLayoutCall10P128 a b).toNat +
            (a.getLimbN 2 * b.getLimbN 2).toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 := by
  unfold mulModProductLayoutCall11Carry136
  exact mulModAddPartialHiCarry_toNat_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall12Carry136_toNat_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall12Carry136 a b).toNat =
      ((mulModProductLayoutCall11P136 a b).toNat +
        ((rv64_mulhu (a.getLimbN 1) (b.getLimbN 3)).toNat +
          ((mulModProductLayoutCall11P128 a b).toNat +
            (a.getLimbN 1 * b.getLimbN 3).toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 := by
  unfold mulModProductLayoutCall12Carry136
  exact mulModAddPartialHiCarry_toNat_forColumn6 _ _ _ _

private theorem mulModAddPartialHiCarry_toNat_le_one_forColumn6 (hi lo x y : Word) :
    (mulModAddPartialHiCarry hi lo x y).toNat ≤ 1 := by
  rw [mulModAddPartialHiCarry_toNat_forColumn6]
  have h_hi := hi.isLt
  have h_term : ((rv64_mulhu x y).toNat + (lo.toNat + (x * y).toNat) / 2 ^ 64) %
      2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  omega

private theorem mulModCarryStepCarry_zero_of_small_forColumn6
    (limb carry : Word) (h_limb : limb.toNat ≤ 3) (h_carry : carry.toNat ≤ 1) :
    mulModCarryStepCarry limb carry = 0 := by
  apply BitVec.eq_of_toNat_eq
  change (mulModCarryStepCarry limb carry).toNat = 0
  unfold mulModCarryStepCarry
  rw [mulModProductLayoutCarryRight_toNat]
  omega

private theorem mulModProductLayoutCall06Carry128_toNat_le_one_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall06Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall06Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall07Carry128_toNat_le_one_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall07Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall07Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall08Carry128_toNat_le_one_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall08Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall08Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall09Carry128_toNat_le_one_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall09Carry128 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall09Carry128
  exact mulModAddPartialHiCarry_toNat_le_one_forColumn6 _ _ _ _

private theorem mulModProductLayoutCall06P136_toNat_le_one_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall06P136 a b).toNat ≤ 1 := by
  unfold mulModProductLayoutCall06P136 mulModCarryStepValue
  rw [mulModProductLayoutCall05P136_zero_forColumn6]
  simpa using mulModProductLayoutCall06Carry128_toNat_le_one_forColumn6 a b

private theorem mulModProductLayoutCall06Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall06Carry136 a b = 0 := by
  unfold mulModProductLayoutCall06Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn6 _ _
    (by rw [mulModProductLayoutCall05P136_zero_forColumn6]; decide)
    (mulModProductLayoutCall06Carry128_toNat_le_one_forColumn6 a b)

private theorem mulModProductLayoutCall06P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall06P144 a b = 0 := by
  unfold mulModProductLayoutCall06P144 mulModCarryStepValue
  rw [mulModProductLayoutCall05P144_zero_forColumn6, mulModProductLayoutCall06Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall07P136_toNat_le_two_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall07P136 a b).toNat ≤ 2 := by
  unfold mulModProductLayoutCall07P136 mulModCarryStepValue
  rw [BitVec.toNat_add]
  have h6 := mulModProductLayoutCall06P136_toNat_le_one_forColumn6 a b
  have h7 := mulModProductLayoutCall07Carry128_toNat_le_one_forColumn6 a b
  omega

private theorem mulModProductLayoutCall07Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall07Carry136 a b = 0 := by
  unfold mulModProductLayoutCall07Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn6 _ _
    (by exact Nat.le_trans (mulModProductLayoutCall06P136_toNat_le_one_forColumn6 a b) (by decide))
    (mulModProductLayoutCall07Carry128_toNat_le_one_forColumn6 a b)

private theorem mulModProductLayoutCall07P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall07P144 a b = 0 := by
  unfold mulModProductLayoutCall07P144 mulModCarryStepValue
  rw [mulModProductLayoutCall06P144_zero_forColumn6, mulModProductLayoutCall07Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall08P136_toNat_le_three_forColumn6 (a b : EvmWord) :
    (mulModProductLayoutCall08P136 a b).toNat ≤ 3 := by
  unfold mulModProductLayoutCall08P136 mulModCarryStepValue
  rw [BitVec.toNat_add]
  have h7 := mulModProductLayoutCall07P136_toNat_le_two_forColumn6 a b
  have h8 := mulModProductLayoutCall08Carry128_toNat_le_one_forColumn6 a b
  omega

private theorem mulModProductLayoutCall08Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall08Carry136 a b = 0 := by
  unfold mulModProductLayoutCall08Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn6 _ _
    (by exact Nat.le_trans (mulModProductLayoutCall07P136_toNat_le_two_forColumn6 a b) (by decide))
    (mulModProductLayoutCall08Carry128_toNat_le_one_forColumn6 a b)

private theorem mulModProductLayoutCall08P144_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall08P144 a b = 0 := by
  unfold mulModProductLayoutCall08P144 mulModCarryStepValue
  rw [mulModProductLayoutCall07P144_zero_forColumn6, mulModProductLayoutCall08Carry136_zero_forColumn6]
  rfl

private theorem mulModProductLayoutCall09Carry136_zero_forColumn6 (a b : EvmWord) :
    mulModProductLayoutCall09Carry136 a b = 0 := by
  unfold mulModProductLayoutCall09Carry136
  exact mulModCarryStepCarry_zero_of_small_forColumn6 _ _
    (mulModProductLayoutCall08P136_toNat_le_three_forColumn6 a b)
    (mulModProductLayoutCall09Carry128_toNat_le_one_forColumn6 a b)

/-- The offset-144 product-layout cell is still zero before the column-4
    add-partial calls propagate into it. -/
theorem mulModProductLayoutCall09P144_zero (a b : EvmWord) :
    mulModProductLayoutCall09P144 a b = 0 := by
  unfold mulModProductLayoutCall09P144 mulModCarryStepValue
  rw [mulModProductLayoutCall08P144_zero_forColumn6, mulModProductLayoutCall09Carry136_zero_forColumn6]
  rfl

/-- Nat view of `mulModProductLayoutCall09P144_zero`. -/
theorem mulModProductLayoutCall09P144_toNat_zero (a b : EvmWord) :
    (mulModProductLayoutCall09P144 a b).toNat = 0 := by
  rw [mulModProductLayoutCall09P144_zero]
  rfl



private theorem mulModProductLayoutCarryHighFromTwoWordAccumulatorProductsModCarries
    (lo hi mu20 lo20 mu11 lo11 mu02 lo02 : Nat)
    (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64)
    (hp20 : mu20 * 2 ^ 64 + lo20 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp11 : mu11 * 2 ^ 64 + lo11 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hp02 : mu02 * 2 ^ 64 + lo02 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    let w := 2 ^ 64
    let lo1 := (lo + lo20) % w
    let hi1 := (hi + (mu20 + (lo + lo20) / w) % w) % w
    let c1 := (hi + (mu20 + (lo + lo20) / w) % w) / w
    let lo2 := (lo1 + lo11) % w
    let hi2 := (hi1 + (mu11 + (lo1 + lo11) / w) % w) % w
    let c2 := (hi1 + (mu11 + (lo1 + lo11) / w) % w) / w
    let c3 := (hi2 + (mu02 + (lo2 + lo02) / w) % w) / w
    (((c1 % w + c2) % w + c3) % w) =
      ((mu02 * w + lo02 + (mu11 * w + lo11) + (mu20 * w + lo20) + (hi * w + lo)) /
        w / w) % w := by
  intro w lo1 hi1 c1 lo2 hi2 c2 c3
  have h_core := mulModProductLayoutCarryHighFromTwoWordAccumulatorProducts
    lo hi mu20 lo20 mu11 lo11 mu02 lo02 hlo hhi hp20 hp11 hp02
  dsimp only at h_core
  have h_c1 : c1 < w := by
    subst c1
    subst w
    have h20 : mu20 + (lo + lo20) / 2 ^ 64 < 2 ^ 64 := by
      norm_num at hlo hp20 ⊢
      omega
    have h_term : (mu20 + (lo + lo20) / 2 ^ 64) % 2 ^ 64 < 2 ^ 64 :=
      Nat.mod_lt _ (by norm_num)
    norm_num at hhi h_term ⊢
    omega
  rw [Nat.mod_eq_of_lt h_c1]
  exact h_core

/-- The twelfth call's offset-144 cell is the high word of the column-4 carry. -/
theorem mulModProductLayoutCall12P144_toNat_eq_c5_high (a b : EvmWord) :
    let a0 := a.getLimbN 0
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let a3 := a.getLimbN 3
    let b0 := b.getLimbN 0
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let b3 := b.getLimbN 3
    let d0 := a0.toNat * b0.toNat
    let d1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let d2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let d3 := a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat +
      a3.toNat * b0.toNat
    let d4 := a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    let c5 := (d4 + c4) / 2 ^ 64
    (mulModProductLayoutCall12P144 a b).toNat = (c5 / 2 ^ 64) % 2 ^ 64 := by
  dsimp only
  unfold mulModProductLayoutCall12P144 mulModProductLayoutCall11P144
    mulModProductLayoutCall10P144
  simp only [mulModCarryStepValue_toNat_forColumn6, mulModProductLayoutCall09P144_toNat_zero,
    mulModProductLayoutCall10Carry136_toNat_forColumn6,
    mulModProductLayoutCall11Carry136_toNat_forColumn6,
    mulModProductLayoutCall12Carry136_toNat_forColumn6,
    mulModProductLayoutCall09P136_toNat_eq_limb3CarryHigh,
    mulModProductLayoutCall09P128_toNat_eq_limb3Carry,
    mulModProductLayoutCall10P128_toNat_forColumn6,
    mulModProductLayoutCall10P136_toNat_forColumn6,
    mulModProductLayoutCall11P128_toNat_forColumn6,
    mulModProductLayoutCall11P136_toNat_forColumn6]
  simp only [Nat.zero_add]
  rw [mulModProductLayoutCarryHighFromTwoWordAccumulatorProductsModCarries]
  · have h31 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 1)
    have h22 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 2)
    have h13 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 3)
    have h00 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 0)
    have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
    have h20 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 0)
    have h30 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 0)
    have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
    have h11 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 1)
    have h21 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 1)
    have h02 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 2)
    have h12 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 2)
    have h03 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 3)
    have ha0 := (a.getLimbN 0).isLt
    have ha1 := (a.getLimbN 1).isLt
    have ha2 := (a.getLimbN 2).isLt
    have ha3 := (a.getLimbN 3).isLt
    have hb0 := (b.getLimbN 0).isLt
    have hb1 := (b.getLimbN 1).isLt
    have hb2 := (b.getLimbN 2).isLt
    have hb3 := (b.getLimbN 3).isLt
    norm_num at h31 h22 h13 h00 h10 h20 h30 h01 h11 h21 h02 h12 h03 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 ⊢
    omega
  · exact Nat.mod_lt _ (by norm_num)
  · have h00 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 0)
    have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
    have h20 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 0)
    have h30 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 0)
    have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
    have h11 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 1)
    have h21 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 1)
    have h02 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 2)
    have h12 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 2)
    have h03 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 3)
    have ha0 := (a.getLimbN 0).isLt
    have ha1 := (a.getLimbN 1).isLt
    have ha2 := (a.getLimbN 2).isLt
    have ha3 := (a.getLimbN 3).isLt
    have hb0 := (b.getLimbN 0).isLt
    have hb1 := (b.getLimbN 1).isLt
    have hb2 := (b.getLimbN 2).isLt
    have hb3 := (b.getLimbN 3).isLt
    norm_num at h00 h10 h20 h30 h01 h11 h21 h02 h12 h03 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 ⊢
    omega
  · have h31 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 1)
    rw [h31]
    exact Nat.mul_le_mul (by omega) (by omega)
  · have h22 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 2)
    rw [h22]
    exact Nat.mul_le_mul (by omega) (by omega)
  · have h13 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 3)
    rw [h13]
    exact Nat.mul_le_mul (by omega) (by omega)


/-- The fourteenth call's offset-144 cell is the carry into column six. -/
theorem mulModProductLayoutCall14P144_toNat_eq_c6_carry (a b : EvmWord) :
    let a0 := a.getLimbN 0
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let a3 := a.getLimbN 3
    let b0 := b.getLimbN 0
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let b3 := b.getLimbN 3
    let d0 := a0.toNat * b0.toNat
    let d1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let d2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let d3 := a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat +
      a3.toNat * b0.toNat
    let d4 := a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat
    let d5 := a2.toNat * b3.toNat + a3.toNat * b2.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    let c5 := (d4 + c4) / 2 ^ 64
    let c6 := (d5 + c5) / 2 ^ 64
    (mulModProductLayoutCall14P144 a b).toNat = c6 % 2 ^ 64 := by
  dsimp only
  unfold mulModProductLayoutCall14P144 mulModProductLayoutCall13P144
    mulModProductLayoutCall13P136
  simp only [mulModAddPartialHiValue_toNat_forColumn6, mulModAddPartialLoValue_toNat_forColumn6,
    mulModProductLayoutCall12P144_toNat_eq_c5_high, mulModProductLayoutCall12P136_toNat_eq_c5]
  have h32 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 2)
  have h23 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 3)
  have h00 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 0)
  have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
  have h20 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 0)
  have h30 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 0)
  have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
  have h11 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 1)
  have h21 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 1)
  have h02 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 2)
  have h12 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 2)
  have h03 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 3)
  have h31 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 1)
  have h22 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 2)
  have h13 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 3)
  have ha0 := (a.getLimbN 0).isLt
  have ha1 := (a.getLimbN 1).isLt
  have ha2 := (a.getLimbN 2).isLt
  have ha3 := (a.getLimbN 3).isLt
  have hb0 := (b.getLimbN 0).isLt
  have hb1 := (b.getLimbN 1).isLt
  have hb2 := (b.getLimbN 2).isLt
  have hb3 := (b.getLimbN 3).isLt
  norm_num at h32 h23 h00 h10 h20 h30 h01 h11 h21 h02 h12 h03 h31 h22 h13 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 ⊢
  omega

/-- The finalized product-layout column-six cell at offset 144. -/
def mulModProductLayoutColumn6Value (a b : EvmWord) : Word :=
  mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
    (a.getLimbN 3) (b.getLimbN 3)


/-- The folded column-six target is the schoolbook limb-six value. -/
theorem mulModProductLayoutColumn6Value_toNat_eq_schoolbook_limb6 (a b : EvmWord) :
    let a0 := a.getLimbN 0
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let a3 := a.getLimbN 3
    let b0 := b.getLimbN 0
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let b3 := b.getLimbN 3
    let d0 := a0.toNat * b0.toNat
    let d1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let d2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let d3 := a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat +
      a3.toNat * b0.toNat
    let d4 := a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat
    let d5 := a2.toNat * b3.toNat + a3.toNat * b2.toNat
    let d6 := a3.toNat * b3.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    let c5 := (d4 + c4) / 2 ^ 64
    let c6 := (d5 + c5) / 2 ^ 64
    (mulModProductLayoutColumn6Value a b).toNat = (d6 + c6) % 2 ^ 64 := by
  dsimp only
  unfold mulModProductLayoutColumn6Value
  simp only [mulModAddPartialLoValue_toNat_forColumn6,
    mulModProductLayoutCall14P144_toNat_eq_c6_carry]
  have h33 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 3)
  norm_num at h33 ⊢
  omega

/-- The folded column-six target is the sixth schoolbook product limb. -/
theorem mulModProductLayoutColumn6Value_eq_productLimb_six (a b : EvmWord) :
    mulModProductLayoutColumn6Value a b = productLimb a b 6 := by
  apply BitVec.eq_of_toNat_eq
  rw [mulModProductLayoutColumn6Value_toNat_eq_schoolbook_limb6]
  simp only [productLimb, productNat, BitVec.toNat_ofNat, Nat.reduceMul]
  rw [EvmWord.toNat_eq_limb_sum a, EvmWord.toNat_eq_limb_sum b]
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  rw [mulModProductLayoutSchoolbookLimb6]

/-- The folded column-six target is the third high product limb. -/
theorem mulModProductLayoutColumn6Value_eq_mulHigh_getLimbN_two (a b : EvmWord) :
    mulModProductLayoutColumn6Value a b = (EvmWord.mulHigh a b).getLimbN 2 := by
  rw [← productLimb_six_eq_mulHigh_getLimbN_two]
  exact mulModProductLayoutColumn6Value_eq_productLimb_six a b

/-- The concrete call15 P144 cell is the folded column-six target. -/
theorem mulModProductLayoutCall15P144Value_eq_column6Value (a b : EvmWord) :
    mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
      (a.getLimbN 3) (b.getLimbN 3) =
      mulModProductLayoutColumn6Value a b := by
  rfl

/-- The concrete call15 P144 cell has the same product-limb-6 proof obligation
    as the folded column-six target. -/
theorem mulModProductLayoutCall15P144Value_eq_productLimb_six_iff_column6Value
    (a b : EvmWord) :
    (mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
        (a.getLimbN 3) (b.getLimbN 3) = productLimb a b 6) ↔
      (mulModProductLayoutColumn6Value a b = productLimb a b 6) := by
  rfl

/-- The concrete call15 P144 cell is the sixth schoolbook product limb. -/
theorem mulModProductLayoutCall15P144Value_eq_productLimb_six (a b : EvmWord) :
    mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
      (a.getLimbN 3) (b.getLimbN 3) = productLimb a b 6 := by
  rw [mulModProductLayoutCall15P144Value_eq_column6Value]
  exact mulModProductLayoutColumn6Value_eq_productLimb_six a b

/-- The concrete call15 high-limb target is equivalent to the folded
    column-six product-limb obligation. -/
theorem mulModProductLayoutCall15P144Value_eq_mulHigh_getLimbN_two_iff_column6Value
    (a b : EvmWord) :
    (mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
        (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 2) ↔
      (mulModProductLayoutColumn6Value a b = productLimb a b 6) := by
  rw [← productLimb_six_eq_mulHigh_getLimbN_two]
  exact mulModProductLayoutCall15P144Value_eq_productLimb_six_iff_column6Value a b

/-- The concrete call15 P144 cell is the third high product limb. -/
theorem mulModProductLayoutCall15P144Value_eq_mulHigh_getLimbN_two (a b : EvmWord) :
    mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
      (a.getLimbN 3) (b.getLimbN 3) = (EvmWord.mulHigh a b).getLimbN 2 := by
  rw [mulModProductLayoutCall15P144Value_eq_column6Value]
  exact mulModProductLayoutColumn6Value_eq_mulHigh_getLimbN_two a b

/-- The folded column-six product-limb target is the same as the direct
    mulHigh limb2 target. -/
theorem mulModProductLayoutColumn6Value_eq_mulHigh_getLimbN_two_iff_productLimb_six
    (a b : EvmWord) :
    (mulModProductLayoutColumn6Value a b =
        (EvmWord.mulHigh a b).getLimbN 2) ↔
      (mulModProductLayoutColumn6Value a b = productLimb a b 6) := by
  rw [← productLimb_six_eq_mulHigh_getLimbN_two]

theorem mulModProductLayoutColumn6Value_eq_mulHigh_getLimbN_two_of_productLimb_six
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn6Value a b = productLimb a b 6) :
    mulModProductLayoutColumn6Value a b =
      (EvmWord.mulHigh a b).getLimbN 2 := by
  exact (mulModProductLayoutColumn6Value_eq_mulHigh_getLimbN_two_iff_productLimb_six
    a b).2 h_col

theorem mulModProductLayoutCall15P144Value_eq_mulHigh_getLimbN_two_of_column6Value_mulHigh
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn6Value a b =
      (EvmWord.mulHigh a b).getLimbN 2) :
    mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
      (a.getLimbN 3) (b.getLimbN 3) = (EvmWord.mulHigh a b).getLimbN 2 := by
  rw [mulModProductLayoutCall15P144Value_eq_column6Value, h_col]

theorem mulModProductLayoutColumn6Value_eq_productLimb_six_of_call15P144Value_mulHigh
    {a b : EvmWord}
    (h_col : mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
      (a.getLimbN 3) (b.getLimbN 3) = (EvmWord.mulHigh a b).getLimbN 2) :
    mulModProductLayoutColumn6Value a b = productLimb a b 6 := by
  exact (mulModProductLayoutCall15P144Value_eq_mulHigh_getLimbN_two_iff_column6Value
    a b).1 h_col

end EvmAsm.Evm64
