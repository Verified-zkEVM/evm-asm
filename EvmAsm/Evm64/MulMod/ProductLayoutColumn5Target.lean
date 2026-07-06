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

private theorem mulModAddPartialLoValue_toNat (lo x y : Word) :
    (mulModAddPartialLoValue lo x y).toNat = (lo.toNat + (x * y).toNat) % 2 ^ 64 := by
  unfold mulModAddPartialLoValue mulModAddPartialLoProduct
  rw [BitVec.toNat_add]

private theorem mulModAddPartialHiValue_toNat (hi lo x y : Word) :
    (mulModAddPartialHiValue hi lo x y).toNat =
      (hi.toNat + ((rv64_mulhu x y).toNat + (lo.toNat + (x * y).toNat) / 2 ^ 64) %
        2 ^ 64) % 2 ^ 64 := by
  unfold mulModAddPartialHiValue mulModAddPartialHiBaseValue mulModAddPartialHiProduct
  rw [BitVec.toNat_add]
  rw [BitVec.toNat_add]
  unfold mulModAddPartialLoCarry mulModAddPartialLoValue mulModAddPartialLoProduct
  rw [mulModProductLayoutCarryRightEqTrue_toNat]
  omega

private theorem mulModAddPartialHiCarry_toNat (hi lo x y : Word) :
    (mulModAddPartialHiCarry hi lo x y).toNat =
      (hi.toNat + ((rv64_mulhu x y).toNat + (lo.toNat + (x * y).toNat) / 2 ^ 64) %
        2 ^ 64) / 2 ^ 64 := by
  rw [mulModAddPartialHiCarry_eq_singleCarry]
  rw [mulModProductLayoutCarryRightEqTrue_toNat]
  rw [BitVec.toNat_add]
  unfold mulModAddPartialHiProduct mulModAddPartialLoCarry mulModAddPartialLoValue
    mulModAddPartialLoProduct
  rw [mulModProductLayoutCarryRightEqTrue_toNat]

private theorem mulModProductLayoutCall06P120_toNat (a b : EvmWord) :
    (mulModProductLayoutCall06P120 a b).toNat =
      ((mulModProductLayoutCall05P120 a b).toNat +
        (a.getLimbN 3 * b.getLimbN 0).toNat) % 2 ^ 64 := by
  unfold mulModProductLayoutCall06P120
  exact mulModAddPartialLoValue_toNat _ _ _

private theorem mulModProductLayoutCall07P120_toNat (a b : EvmWord) :
    (mulModProductLayoutCall07P120 a b).toNat =
      ((mulModProductLayoutCall06P120 a b).toNat +
        (a.getLimbN 2 * b.getLimbN 1).toNat) % 2 ^ 64 := by
  unfold mulModProductLayoutCall07P120
  exact mulModAddPartialLoValue_toNat _ _ _

private theorem mulModProductLayoutCall08P120_toNat (a b : EvmWord) :
    (mulModProductLayoutCall08P120 a b).toNat =
      ((mulModProductLayoutCall07P120 a b).toNat +
        (a.getLimbN 1 * b.getLimbN 2).toNat) % 2 ^ 64 := by
  unfold mulModProductLayoutCall08P120
  exact mulModAddPartialLoValue_toNat _ _ _

private theorem mulModProductLayoutCall06P128_toNat (a b : EvmWord) :
    (mulModProductLayoutCall06P128 a b).toNat =
      ((mulModProductLayoutCall05P128 a b).toNat +
        ((rv64_mulhu (a.getLimbN 3) (b.getLimbN 0)).toNat +
          ((mulModProductLayoutCall05P120 a b).toNat +
            (a.getLimbN 3 * b.getLimbN 0).toNat) / 2 ^ 64) % 2 ^ 64) %
        2 ^ 64 := by
  unfold mulModProductLayoutCall06P128
  exact mulModAddPartialHiValue_toNat _ _ _ _

private theorem mulModProductLayoutCall07P128_toNat (a b : EvmWord) :
    (mulModProductLayoutCall07P128 a b).toNat =
      ((mulModProductLayoutCall06P128 a b).toNat +
        ((rv64_mulhu (a.getLimbN 2) (b.getLimbN 1)).toNat +
          ((mulModProductLayoutCall06P120 a b).toNat +
            (a.getLimbN 2 * b.getLimbN 1).toNat) / 2 ^ 64) % 2 ^ 64) %
        2 ^ 64 := by
  unfold mulModProductLayoutCall07P128
  exact mulModAddPartialHiValue_toNat _ _ _ _

private theorem mulModProductLayoutCall08P128_toNat (a b : EvmWord) :
    (mulModProductLayoutCall08P128 a b).toNat =
      ((mulModProductLayoutCall07P128 a b).toNat +
        ((rv64_mulhu (a.getLimbN 1) (b.getLimbN 2)).toNat +
          ((mulModProductLayoutCall07P120 a b).toNat +
            (a.getLimbN 1 * b.getLimbN 2).toNat) / 2 ^ 64) % 2 ^ 64) %
        2 ^ 64 := by
  unfold mulModProductLayoutCall08P128
  exact mulModAddPartialHiValue_toNat _ _ _ _

private theorem mulModProductLayoutCall06Carry128_toNat (a b : EvmWord) :
    (mulModProductLayoutCall06Carry128 a b).toNat =
      ((mulModProductLayoutCall05P128 a b).toNat +
        ((rv64_mulhu (a.getLimbN 3) (b.getLimbN 0)).toNat +
          ((mulModProductLayoutCall05P120 a b).toNat +
            (a.getLimbN 3 * b.getLimbN 0).toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 := by
  unfold mulModProductLayoutCall06Carry128
  exact mulModAddPartialHiCarry_toNat _ _ _ _

private theorem mulModProductLayoutCall07Carry128_toNat (a b : EvmWord) :
    (mulModProductLayoutCall07Carry128 a b).toNat =
      ((mulModProductLayoutCall06P128 a b).toNat +
        ((rv64_mulhu (a.getLimbN 2) (b.getLimbN 1)).toNat +
          ((mulModProductLayoutCall06P120 a b).toNat +
            (a.getLimbN 2 * b.getLimbN 1).toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 := by
  unfold mulModProductLayoutCall07Carry128
  exact mulModAddPartialHiCarry_toNat _ _ _ _

private theorem mulModProductLayoutCall08Carry128_toNat (a b : EvmWord) :
    (mulModProductLayoutCall08Carry128 a b).toNat =
      ((mulModProductLayoutCall07P128 a b).toNat +
        ((rv64_mulhu (a.getLimbN 1) (b.getLimbN 2)).toNat +
          ((mulModProductLayoutCall07P120 a b).toNat +
            (a.getLimbN 1 * b.getLimbN 2).toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 := by
  unfold mulModProductLayoutCall08Carry128
  exact mulModAddPartialHiCarry_toNat _ _ _ _

private theorem mulModProductLayoutCall09Carry128_toNat (a b : EvmWord) :
    (mulModProductLayoutCall09Carry128 a b).toNat =
      ((mulModProductLayoutCall08P128 a b).toNat +
        ((rv64_mulhu (a.getLimbN 0) (b.getLimbN 3)).toNat +
          ((mulModProductLayoutCall08P120 a b).toNat +
            (a.getLimbN 0 * b.getLimbN 3).toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64 := by
  unfold mulModProductLayoutCall09Carry128
  exact mulModAddPartialHiCarry_toNat _ _ _ _

private theorem mulModProductLayoutCall05P120_toNat_eq_limb2CarryLowCompact (a b : EvmWord) :
    let a0 := a.getLimbN 0
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let b0 := b.getLimbN 0
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let d0 := a0.toNat * b0.toNat
    let d1 := a0.toNat * b1.toNat + a1.toNat * b0.toNat
    let d2 := a0.toNat * b2.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    (mulModProductLayoutCall05P120 a b).toNat = c3 % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutCall05P120_toNat_eq_limb2CarryLow]
  have h00 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 0)
  have h10 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 0)
  have h20 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 0)
  have h01 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 1)
  have h11 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 1)
  have h02 := EvmWord.mul_full_product (a.getLimbN 0) (b.getLimbN 2)
  norm_num at h00 h10 h20 h01 h11 h02 ⊢
  omega

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

private theorem mulModProductLayoutCarryChainHigh4CarryExpanded
    (hi feed lo30 mu30 lo21 mu21 lo12 mu12 lo03 mu03 : Nat)
    (h30 : mu30 + (feed + lo30) / 2 ^ 64 < 2 ^ 64)
    (h21 : mu21 + ((feed + lo30) % 2 ^ 64 + lo21) / 2 ^ 64 < 2 ^ 64)
    (h12 : mu12 + (((feed + lo30) % 2 ^ 64 + lo21) % 2 ^ 64 + lo12) /
        2 ^ 64 < 2 ^ 64)
    (h03 : mu03 + ((((feed + lo30) % 2 ^ 64 + lo21) % 2 ^ 64 + lo12) %
        2 ^ 64 + lo03) / 2 ^ 64 < 2 ^ 64) :
    let w := 2 ^ 64
    let feed06 := (feed + lo30) % w
    let high06 := (hi + (mu30 + (feed + lo30) / w) % w) % w
    let carry06 := (hi + (mu30 + (feed + lo30) / w) % w) / w
    let feed07 := (feed06 + lo21) % w
    let high07 := (high06 + (mu21 + (feed06 + lo21) / w) % w) % w
    let carry07 := (high06 + (mu21 + (feed06 + lo21) / w) % w) / w
    let feed08 := (feed07 + lo12) % w
    let high08 := (high07 + (mu12 + (feed07 + lo12) / w) % w) % w
    let carry08 := (high07 + (mu12 + (feed07 + lo12) / w) % w) / w
    let carry09 := (high08 + (mu03 + (feed08 + lo03) / w) % w) / w
    ((((0 + carry06) % w + carry07) % w + carry08) % w + carry09) % w =
      ((hi + mu30 + mu21 + mu12 + mu03 +
        (feed + lo30 + lo21 + lo12 + lo03) / w) / w) % w := by
  intro w feed06 high06 carry06 feed07 high07 carry07 feed08 high08 carry08 carry09
  have h_eq :=
    mulModProductLayoutCarryChainHigh4CarryEq hi feed lo30 mu30 lo21 mu21 lo12 mu12
      lo03 mu03 h30 h21 h12 h03
  dsimp only at h_eq
  subst carry09
  subst carry08
  subst high08
  subst feed08
  subst carry07
  subst high07
  subst feed07
  subst carry06
  subst high06
  subst feed06
  subst w
  simpa [Nat.zero_add, Nat.add_assoc] using h_eq

/-- The ninth call's offset-136 cell is the high word of the column-3 carry. -/
theorem mulModProductLayoutCall09P136_toNat_eq_limb3CarryHigh (a b : EvmWord) :
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
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    (mulModProductLayoutCall09P136 a b).toNat = (c4 / 2 ^ 64) % 2 ^ 64 := by
  dsimp only
  unfold mulModProductLayoutCall09P136 mulModProductLayoutCall08P136
    mulModProductLayoutCall07P136 mulModProductLayoutCall06P136 mulModCarryStepValue
  rw [mulModProductLayoutCall05P136_zero]
  simp only [BitVec.toNat_add, mulModProductLayoutCall06Carry128_toNat,
    mulModProductLayoutCall07Carry128_toNat, mulModProductLayoutCall08Carry128_toNat,
    mulModProductLayoutCall09Carry128_toNat, mulModProductLayoutCall06P120_toNat,
    mulModProductLayoutCall07P120_toNat, mulModProductLayoutCall08P120_toNat,
    mulModProductLayoutCall06P128_toNat, mulModProductLayoutCall07P128_toNat,
    mulModProductLayoutCall08P128_toNat, mulModProductLayoutCall05P120_toNat_eq_limb2CarryLowCompact,
    mulModProductLayoutCall05P128_toNat_eq_limb2CarryHigh]
  rw [show (BitVec.toNat (0 : Word)) = 0 by rfl]
  rw [mulModProductLayoutCarryChainHigh4CarryExpanded]
  all_goals
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
    have hp30 : (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0)).toNat * 2 ^ 64 +
        (a.getLimbN 3 * b.getLimbN 0).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
      rw [h30]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hp21 : (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1)).toNat * 2 ^ 64 +
        (a.getLimbN 2 * b.getLimbN 1).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
      rw [h21]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hp12 : (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2)).toNat * 2 ^ 64 +
        (a.getLimbN 1 * b.getLimbN 2).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
      rw [h12]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hp03 : (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3)).toNat * 2 ^ 64 +
        (a.getLimbN 0 * b.getLimbN 3).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
      rw [h03]
      exact Nat.mul_le_mul (by omega) (by omega)
    norm_num at h00 h10 h20 h30 h01 h11 h21 h02 h12 h03 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hp30 hp21 hp12 hp03 ⊢
    omega


/-- The twelfth call's offset-136 cell is the low word of the column-4 carry. -/
theorem mulModProductLayoutCall12P136_toNat_eq_c5 (a b : EvmWord) :
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
    (mulModProductLayoutCall12P136 a b).toNat = c5 % 2 ^ 64 := by
  dsimp only
  unfold mulModProductLayoutCall12P136 mulModProductLayoutCall11P136
    mulModProductLayoutCall10P136 mulModProductLayoutCall11P128
    mulModProductLayoutCall10P128
  simp only [mulModAddPartialHiValue_toNat, mulModAddPartialLoValue_toNat,
    mulModProductLayoutCall09P136_toNat_eq_limb3CarryHigh,
    mulModProductLayoutCall09P128_toNat_eq_limb3Carry]
  rw [mulModProductLayoutCarryLowAfterThreeAdditions]
  have h31 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 1)
  have h22 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 2)
  have h13 := EvmWord.mul_full_product (a.getLimbN 1) (b.getLimbN 3)
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

/-- The folded column-five target is the schoolbook limb-five value. -/
theorem mulModProductLayoutColumn5Value_toNat_eq_schoolbook_limb5 (a b : EvmWord) :
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
    (mulModProductLayoutColumn5Value a b).toNat = (d5 + c5) % 2 ^ 64 := by
  dsimp only
  unfold mulModProductLayoutColumn5Value mulModProductLayoutCall14P136
    mulModProductLayoutCall13P136
  simp only [mulModAddPartialLoValue_toNat, mulModProductLayoutCall12P136_toNat_eq_c5]
  have h32 := EvmWord.mul_full_product (a.getLimbN 3) (b.getLimbN 2)
  have h23 := EvmWord.mul_full_product (a.getLimbN 2) (b.getLimbN 3)
  norm_num at h32 h23 ⊢
  omega


/-- The folded column-five target is the fifth schoolbook product limb. -/
theorem mulModProductLayoutColumn5Value_eq_productLimb_five (a b : EvmWord) :
    mulModProductLayoutColumn5Value a b = productLimb a b 5 := by
  apply BitVec.eq_of_toNat_eq
  rw [mulModProductLayoutColumn5Value_toNat_eq_schoolbook_limb5]
  simp only [productLimb, productNat, BitVec.toNat_ofNat, Nat.reduceMul]
  rw [EvmWord.toNat_eq_limb_sum a, EvmWord.toNat_eq_limb_sum b]
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  rw [mulModProductLayoutSchoolbookLimb5]

/-- The folded column-five target is the second high product limb. -/
theorem mulModProductLayoutColumn5Value_eq_mulHigh_getLimbN_one (a b : EvmWord) :
    mulModProductLayoutColumn5Value a b = (EvmWord.mulHigh a b).getLimbN 1 := by
  rw [← productLimb_five_eq_mulHigh_getLimbN_one]
  exact mulModProductLayoutColumn5Value_eq_productLimb_five a b

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

/-- The concrete call14 P136 cell is the fifth schoolbook product limb. -/
theorem mulModProductLayoutCall14P136_eq_productLimb_five (a b : EvmWord) :
    mulModProductLayoutCall14P136 a b = productLimb a b 5 := by
  exact (mulModProductLayoutCall14P136_eq_productLimb_five_iff_column5Value a b).2
    (mulModProductLayoutColumn5Value_eq_productLimb_five a b)

/-- The concrete call14 P136 cell is the second high product limb. -/
theorem mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one (a b : EvmWord) :
    mulModProductLayoutCall14P136 a b = (EvmWord.mulHigh a b).getLimbN 1 := by
  exact (mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one_iff_column5Value a b).2
    (mulModProductLayoutColumn5Value_eq_productLimb_five a b)

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
