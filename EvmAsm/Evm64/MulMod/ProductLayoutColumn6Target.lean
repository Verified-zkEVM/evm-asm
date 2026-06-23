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

/-- The finalized product-layout column-six cell at offset 144. -/
def mulModProductLayoutColumn6Value (a b : EvmWord) : Word :=
  mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
    (a.getLimbN 3) (b.getLimbN 3)

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
