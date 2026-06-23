import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Target
import EvmAsm.Evm64.MulMod.ProductLayoutCall15

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

private theorem mulModCarryStepCarry_twoBits_zero (p q : Bool) :
    mulModCarryStepCarry (if p then (1 : Word) else 0) (if q then (1 : Word) else 0) =
      0 := by
  cases p <;> cases q <;> decide

private theorem mulModCarryStepCarry_twoPlusOneBits_zero (p q r : Bool) :
    mulModCarryStepCarry ((if p then (1 : Word) else 0) + (if q then (1 : Word) else 0))
      (if r then (1 : Word) else 0) = 0 := by
  cases p <;> cases q <;> cases r <;> decide

private theorem mulModProductLayoutCall00P136_zero (a b : EvmWord) :
    mulModProductLayoutCall00P136 a b = 0 := by
  unfold mulModProductLayoutCall00P136 mulModCarryStepValue
  unfold mulModProductLayoutCall00Carry128 mulModCarryStepCarry
  simp [mulModProductLayoutCall00Carry120_zero, BitVec.ult]

private theorem mulModProductLayoutCall01Carry128_zero (a b : EvmWord) :
    mulModProductLayoutCall01Carry128 a b = 0 := by
  unfold mulModProductLayoutCall01Carry128
  rw [mulModProductLayoutCall00P128_zero, mulModProductLayoutCall01Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall01P136_zero (a b : EvmWord) :
    mulModProductLayoutCall01P136 a b = 0 := by
  unfold mulModProductLayoutCall01P136 mulModCarryStepValue
  rw [mulModProductLayoutCall00P136_zero, mulModProductLayoutCall01Carry128_zero]
  rfl

private theorem mulModProductLayoutCall02Carry128_zero (a b : EvmWord) :
    mulModProductLayoutCall02Carry128 a b = 0 := by
  unfold mulModProductLayoutCall02Carry128
  rw [mulModProductLayoutCall01P128_zero, mulModProductLayoutCall02Carry120_zero]
  exact mulModCarryStepCarry_zero_zero

private theorem mulModProductLayoutCall02P136_zero (a b : EvmWord) :
    mulModProductLayoutCall02P136 a b = 0 := by
  unfold mulModProductLayoutCall02P136 mulModCarryStepValue
  rw [mulModProductLayoutCall01P136_zero, mulModProductLayoutCall02Carry128_zero]
  rfl

private theorem mulModProductLayoutCall03Carry128_zero (a b : EvmWord) :
    mulModProductLayoutCall03Carry128 a b = 0 := by
  unfold mulModProductLayoutCall03Carry128
  rw [mulModProductLayoutCall02P128_zero]
  unfold mulModCarryStepCarry
  simp [BitVec.ult]

private theorem mulModProductLayoutCall03P136_zero (a b : EvmWord) :
    mulModProductLayoutCall03P136 a b = 0 := by
  unfold mulModProductLayoutCall03P136 mulModCarryStepValue
  rw [mulModProductLayoutCall02P136_zero, mulModProductLayoutCall03Carry128_zero]
  rfl

private theorem mulModProductLayoutCall04Carry128_zero (a b : EvmWord) :
    mulModProductLayoutCall04Carry128 a b = 0 := by
  unfold mulModProductLayoutCall04Carry128
  rw [mulModProductLayoutCall03P128_eq_highCarry]
  unfold mulModProductLayoutCall04Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  exact mulModCarryStepCarry_twoBits_zero _ _

private theorem mulModProductLayoutCall04P136_zero (a b : EvmWord) :
    mulModProductLayoutCall04P136 a b = 0 := by
  unfold mulModProductLayoutCall04P136 mulModCarryStepValue
  rw [mulModProductLayoutCall03P136_zero, mulModProductLayoutCall04Carry128_zero]
  rfl

private theorem mulModProductLayoutCall05Carry128_zero (a b : EvmWord) :
    mulModProductLayoutCall05Carry128 a b = 0 := by
  unfold mulModProductLayoutCall05Carry128
  rw [mulModProductLayoutCall04P128_eq_highCarry]
  unfold mulModProductLayoutCall05Carry120
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoValue, mulModAddPartialLoProduct]
  exact mulModCarryStepCarry_twoPlusOneBits_zero _ _ _

private theorem mulModProductLayoutCall05P136_zero (a b : EvmWord) :
    mulModProductLayoutCall05P136 a b = 0 := by
  unfold mulModProductLayoutCall05P136 mulModCarryStepValue
  rw [mulModProductLayoutCall04P136_zero, mulModProductLayoutCall05Carry128_zero]
  rfl

private theorem mulModProductLayoutCarryTelescoping5
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

private theorem mulModProductLayoutGeoSeriesIdentity5 (w : Nat) (h_w : 0 < w) :
    (w - 1) + (w - 1) * w + (w - 1) * w ^ 2 + (w - 1) * w ^ 3 +
        (w - 1) * w ^ 4 + 1 = w ^ 5 := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

private theorem mulModProductLayoutLowPartBound5
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
  have h_geo := mulModProductLayoutGeoSeriesIdentity5 w h_w
  linarith [h_bound0, h_bound1, h_bound2, h_bound3, h_bound4, h_geo]

private theorem mulModProductLayoutProductExpansion5
    (a0 a1 a2 a3 b0 b1 b2 b3 w : Nat) :
    (a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) *
        (b0 + b1 * w + b2 * w ^ 2 + b3 * w ^ 3) =
      a0 * b0 + (a0 * b1 + a1 * b0) * w +
        (a0 * b2 + a1 * b1 + a2 * b0) * w ^ 2 +
        (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * w ^ 3 +
        (a1 * b3 + a2 * b2 + a3 * b1) * w ^ 4 +
        (a2 * b3 + a3 * b2) * w ^ 5 + a3 * b3 * w ^ 6 := by
  ring

private theorem mulModProductLayoutCarryChainHigh4CarryEq
    (hi feed lo30 mu30 lo21 mu21 lo12 mu12 lo03 mu03 : Nat)
    (h30 : mu30 + (feed + lo30) / 2 ^ 64 < 2 ^ 64)
    (h21 : mu21 + ((feed + lo30) % 2 ^ 64 + lo21) / 2 ^ 64 < 2 ^ 64)
    (h12 : mu12 + (((feed + lo30) % 2 ^ 64 + lo21) % 2 ^ 64 + lo12) /
        2 ^ 64 < 2 ^ 64)
    (h03 : mu03 + ((((feed + lo30) % 2 ^ 64 + lo21) % 2 ^ 64 + lo12) %
        2 ^ 64 + lo03) / 2 ^ 64 < 2 ^ 64) :
    let w := 2 ^ 64
    let feed06 := (feed + lo30) % w
    let feed07 := (feed06 + lo21) % w
    let feed08 := (feed07 + lo12) % w
    let high05 := hi
    let high06 := (high05 + (mu30 + (feed + lo30) / w) % w) % w
    let carry06 := (high05 + (mu30 + (feed + lo30) / w) % w) / w
    let high07 := (high06 + (mu21 + (feed06 + lo21) / w) % w) % w
    let carry07 := (high06 + (mu21 + (feed06 + lo21) / w) % w) / w
    let high08 := (high07 + (mu12 + (feed07 + lo12) / w) % w) % w
    let carry08 := (high07 + (mu12 + (feed07 + lo12) / w) % w) / w
    let carry09 := (high08 + (mu03 + (feed08 + lo03) / w) % w) / w
    ((carry06 + carry07) % w + carry08 + carry09) % w =
      ((hi + mu30 + mu21 + mu12 + mu03 +
        (feed + lo30 + lo21 + lo12 + lo03) / w) / w) % w := by
  intro w feed06 feed07 feed08 high05 high06 carry06 high07 carry07 high08 carry08
    carry09
  have hq := mulModProductLayoutCarryChainQuot4 feed lo30 lo21 lo12 lo03
  dsimp only at hq
  rw [hq]
  subst carry09
  subst carry08
  subst high08
  subst carry07
  subst high07
  subst carry06
  subst high06
  subst high05
  subst feed08
  subst feed07
  subst feed06
  subst w
  norm_num at h30 h21 h12 h03 ⊢
  omega


theorem mulModProductLayoutSchoolbookLimb5
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
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    let c5 := (d4 + c4) / 2 ^ 64
    product / 2 ^ 320 % 2 ^ 64 = (d5 + c5) % 2 ^ 64 := by
  dsimp only
  set w := (2 : Nat) ^ 64
  have h128 : (2 : Nat) ^ 128 = w ^ 2 := by
    norm_num [w]
  have h192 : (2 : Nat) ^ 192 = w ^ 3 := by
    norm_num [w]
  have h320 : (2 : Nat) ^ 320 = w ^ 5 := by
    rw [show w = (2 : Nat) ^ 64 by rfl, ← Nat.pow_mul]
  rw [h128, h192, h320]
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
  set product :=
    (a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) *
      (b0 + b1 * w + b2 * w ^ 2 + b3 * w ^ 3)
  have h_product :
      product = d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 +
        d4 * w ^ 4 + d5 * w ^ 5 + d6 * w ^ 6 := by
    simp only [product, d0, d1, d2, d3, d4, d5, d6]
    exact mulModProductLayoutProductExpansion5 a0 a1 a2 a3 b0 b1 b2 b3 w
  have h_w : (0 : Nat) < w := by
    positivity
  have h_tel :
      d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 + d4 * w ^ 4 =
        d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + (d4 + c4) % w * w ^ 4 + c5 * w ^ 5 :=
    mulModProductLayoutCarryTelescoping5 d0 d1 d2 d3 d4 c1 c2 c3 c4 c5 w
      (Nat.div_add_mod d0 w)
      (Nat.div_add_mod (d1 + c1) w)
      (Nat.div_add_mod (d2 + c2) w)
      (Nat.div_add_mod (d3 + c3) w)
      (Nat.div_add_mod (d4 + c4) w)
  have h_low :
      d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + (d4 + c4) % w * w ^ 4 <
        w ^ 5 :=
    mulModProductLayoutLowPartBound5 d0 (d1 + c1) (d2 + c2) (d3 + c3) (d4 + c4)
      w h_w
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
  have h_div : product / w ^ 5 = high := by
    rw [h_product_folded,
      Nat.add_mul_div_right _ _ (by positivity : (0 : Nat) < w ^ 5),
      Nat.div_eq_of_lt h_low, Nat.zero_add]
  rw [h_div, Nat.add_mul_mod_self_right]

/-- The finalized product-layout column-five cell. -/
def mulModProductLayoutColumn5Value (a b : EvmWord) : Word :=
  mulModProductLayoutCall14P136 a b

/-- The concrete call14 P136 cell is the folded column-five target. -/
theorem mulModProductLayoutCall14P136_eq_column5Value (a b : EvmWord) :
    mulModProductLayoutCall14P136 a b = mulModProductLayoutColumn5Value a b := by
  rfl

/-- The concrete call14 P136 cell has the same product-limb-5 proof obligation
    as the folded column-five target. -/
theorem mulModProductLayoutCall14P136_eq_productLimb_five_iff_column5Value
    (a b : EvmWord) :
    (mulModProductLayoutCall14P136 a b = productLimb a b 5) ↔
      (mulModProductLayoutColumn5Value a b = productLimb a b 5) := by
  rfl

/-- The concrete call14 high-limb target is equivalent to the folded
    column-five product-limb obligation. -/
theorem mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one_iff_column5Value
    (a b : EvmWord) :
    (mulModProductLayoutCall14P136 a b = (EvmWord.mulHigh a b).getLimbN 1) ↔
      (mulModProductLayoutColumn5Value a b = productLimb a b 5) := by
  rw [← productLimb_five_eq_mulHigh_getLimbN_one]
  exact mulModProductLayoutCall14P136_eq_productLimb_five_iff_column5Value a b

/-- The folded column-five product-limb target is the same as the direct
    mulHigh limb1 target. -/
theorem mulModProductLayoutColumn5Value_eq_mulHigh_getLimbN_one_iff_productLimb_five
    (a b : EvmWord) :
    (mulModProductLayoutColumn5Value a b =
        (EvmWord.mulHigh a b).getLimbN 1) ↔
      (mulModProductLayoutColumn5Value a b = productLimb a b 5) := by
  rw [← productLimb_five_eq_mulHigh_getLimbN_one]

theorem mulModProductLayoutColumn5Value_eq_mulHigh_getLimbN_one_of_productLimb_five
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn5Value a b = productLimb a b 5) :
    mulModProductLayoutColumn5Value a b =
      (EvmWord.mulHigh a b).getLimbN 1 := by
  exact (mulModProductLayoutColumn5Value_eq_mulHigh_getLimbN_one_iff_productLimb_five
    a b).2 h_col

theorem mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one_of_column5Value_mulHigh
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn5Value a b =
      (EvmWord.mulHigh a b).getLimbN 1) :
    mulModProductLayoutCall14P136 a b = (EvmWord.mulHigh a b).getLimbN 1 := by
  rw [mulModProductLayoutCall14P136_eq_column5Value, h_col]

theorem mulModProductLayoutColumn5Value_eq_productLimb_five_of_call14P136_mulHigh
    {a b : EvmWord}
    (h_col : mulModProductLayoutCall14P136 a b = (EvmWord.mulHigh a b).getLimbN 1) :
    mulModProductLayoutColumn5Value a b = productLimb a b 5 := by
  exact (mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one_iff_column5Value
    a b).1 h_col

end EvmAsm.Evm64
