import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Call02Feed
import EvmAsm.Evm64.MulMod.ProductLayoutCall09Carry

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

private theorem mulModProductLayoutCarryTelescoping4
    (d0 d1 d2 d3 c1 c2 c3 c4 w : Nat)
    (h0 : w * c1 + d0 % w = d0)
    (h1 : w * c2 + (d1 + c1) % w = d1 + c1)
    (h2 : w * c3 + (d2 + c2) % w = d2 + c2)
    (h3 : w * c4 + (d3 + c3) % w = d3 + c3) :
    d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 =
      d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
        (d3 + c3) % w * w ^ 3 + c4 * w ^ 4 := by
  have h_d1 : d1 + c1 = (d1 + c1) % w + w * c2 := by
    linarith [h1]
  have h_d2 : d2 + c2 = (d2 + c2) % w + w * c3 := by
    linarith [h2]
  have h_d3 : d3 + c3 = (d3 + c3) % w + w * c4 := by
    linarith [h3]
  calc
    d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3
        = (d0 % w + w * c1) + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 := by
          linarith [h0]
    _ = d0 % w + (d1 + c1) * w + d2 * w ^ 2 + d3 * w ^ 3 := by
          ring
    _ = d0 % w + ((d1 + c1) % w + w * c2) * w + d2 * w ^ 2 +
          d3 * w ^ 3 := by
          rw [← h_d1]
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) * w ^ 2 +
          d3 * w ^ 3 := by
          ring
    _ = d0 % w + (d1 + c1) % w * w + ((d2 + c2) % w + w * c3) * w ^ 2 +
          d3 * w ^ 3 := by
          rw [← h_d2]
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) * w ^ 3 := by
          ring
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          ((d3 + c3) % w + w * c4) * w ^ 3 := by
          rw [← h_d3]
    _ = d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + c4 * w ^ 4 := by
          ring

private theorem mulModProductLayoutGeoSeriesIdentity4 (w : Nat) (h_w : 0 < w) :
    (w - 1) + (w - 1) * w + (w - 1) * w ^ 2 + (w - 1) * w ^ 3 + 1 =
      w ^ 4 := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

private theorem mulModProductLayoutLowPartBound4
    (d0 d1c1 d2c2 d3c3 w : Nat) (h_w : 0 < w)
    (h0 : d0 % w < w) (h1 : d1c1 % w < w) (h2 : d2c2 % w < w)
    (h3 : d3c3 % w < w) :
    d0 % w + d1c1 % w * w + d2c2 % w * w ^ 2 + d3c3 % w * w ^ 3 <
      w ^ 4 := by
  have h_bound0 : d0 % w ≤ w - 1 := by
    omega
  have h_bound1 : d1c1 % w * w ≤ (w - 1) * w :=
    Nat.mul_le_mul_right w (by omega)
  have h_bound2 : d2c2 % w * w ^ 2 ≤ (w - 1) * w ^ 2 :=
    Nat.mul_le_mul_right (w ^ 2) (by omega)
  have h_bound3 : d3c3 % w * w ^ 3 ≤ (w - 1) * w ^ 3 :=
    Nat.mul_le_mul_right (w ^ 3) (by omega)
  have h_geo := mulModProductLayoutGeoSeriesIdentity4 w h_w
  linarith [h_bound0, h_bound1, h_bound2, h_bound3, h_geo]

private theorem mulModProductLayoutProductExpansion4
    (a0 a1 a2 a3 b0 b1 b2 b3 w : Nat) :
    (a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) *
        (b0 + b1 * w + b2 * w ^ 2 + b3 * w ^ 3) =
      a0 * b0 + (a0 * b1 + a1 * b0) * w +
        (a0 * b2 + a1 * b1 + a2 * b0) * w ^ 2 +
        (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * w ^ 3 +
        (a1 * b3 + a2 * b2 + a3 * b1) * w ^ 4 +
        (a2 * b3 + a3 * b2) * w ^ 5 + a3 * b3 * w ^ 6 := by
  ring

theorem mulModProductLayoutSchoolbookLimb4
    (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    let product :=
      (a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192) *
        (b0 + b1 * 2 ^ 64 + b2 * 2 ^ 128 + b3 * 2 ^ 192)
    let d0 := a0 * b0
    let d1 := a0 * b1 + a1 * b0
    let d2 := a0 * b2 + a1 * b1 + a2 * b0
    let d3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
    let d4 := a1 * b3 + a2 * b2 + a3 * b1
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    product / 2 ^ 256 % 2 ^ 64 = (d4 + c4) % 2 ^ 64 := by
  dsimp only
  set w := (2 : Nat) ^ 64
  have h128 : (2 : Nat) ^ 128 = w ^ 2 := by
    norm_num [w]
  have h192 : (2 : Nat) ^ 192 = w ^ 3 := by
    norm_num [w]
  have h256 : (2 : Nat) ^ 256 = w ^ 4 := by
    norm_num [w]
  rw [h128, h192, h256]
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
  set product :=
    (a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) *
      (b0 + b1 * w + b2 * w ^ 2 + b3 * w ^ 3)
  have h_product :
      product = d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 +
        d4 * w ^ 4 + d5 * w ^ 5 + d6 * w ^ 6 := by
    simp only [product, d0, d1, d2, d3, d4, d5, d6]
    exact mulModProductLayoutProductExpansion4 a0 a1 a2 a3 b0 b1 b2 b3 w
  have h_w : (0 : Nat) < w := by
    positivity
  have h_tel :
      d0 + d1 * w + d2 * w ^ 2 + d3 * w ^ 3 =
        d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 + c4 * w ^ 4 :=
    mulModProductLayoutCarryTelescoping4 d0 d1 d2 d3 c1 c2 c3 c4 w
      (Nat.div_add_mod d0 w)
      (Nat.div_add_mod (d1 + c1) w)
      (Nat.div_add_mod (d2 + c2) w)
      (Nat.div_add_mod (d3 + c3) w)
  have h_low :
      d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
          (d3 + c3) % w * w ^ 3 <
        w ^ 4 :=
    mulModProductLayoutLowPartBound4 d0 (d1 + c1) (d2 + c2) (d3 + c3) w h_w
      (Nat.mod_lt d0 h_w)
      (Nat.mod_lt (d1 + c1) h_w)
      (Nat.mod_lt (d2 + c2) h_w)
      (Nat.mod_lt (d3 + c3) h_w)
  set low :=
    d0 % w + (d1 + c1) % w * w + (d2 + c2) % w * w ^ 2 +
      (d3 + c3) % w * w ^ 3
  have h_product_folded :
      product = low + ((d4 + c4) + d5 * w + d6 * w ^ 2) * w ^ 4 := by
    rw [h_product, h_tel]
    ring
  set high := (d4 + c4) + d5 * w + d6 * w ^ 2
  have h_div : product / w ^ 4 = high := by
    rw [h_product_folded,
      Nat.add_mul_div_right _ _ (by positivity : (0 : Nat) < w ^ 4),
      Nat.div_eq_of_lt h_low, Nat.zero_add]
  rw [h_div, show high = (d4 + c4) + (d5 + d6 * w) * w from by ring,
    Nat.add_mul_mod_self_right]

theorem mulModProductLayoutColumn4Call08P120FeedValue_toNat_eq_call09P128_plus_d4
    (a b : EvmWord) :
    let a1 := a.getLimbN 1
    let a2 := a.getLimbN 2
    let a3 := a.getLimbN 3
    let b1 := b.getLimbN 1
    let b2 := b.getLimbN 2
    let b3 := b.getLimbN 3
    let d4 := a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat
    (mulModProductLayoutColumn4Call08P120FeedValue a b).toNat =
      ((mulModProductLayoutCall09P128 a b).toNat + d4) % 2 ^ 64 := by
  dsimp only
  have h_feed :
      mulModProductLayoutColumn4Call08P120FeedValue a b =
        mulModProductLayoutCall12P128 a b := by
    rw [mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue,
      ← mulModProductLayoutColumn4Value_eq_expandedValue,
      ← mulModProductLayoutCall12P128_eq_column4Value]
  rw [h_feed, mulModProductLayoutCall12P128_eq_expanded]
  simp only [BitVec.toNat_add, EvmWord.mul_toNat]
  omega

/-- The call08 feed cell is the schoolbook fourth-limb value. -/
theorem mulModProductLayoutColumn4Call08P120FeedValue_toNat_eq_schoolbook_limb4
    (a b : EvmWord) :
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
    let d3 := a0.toNat * b3.toNat + a1.toNat * b2.toNat + a2.toNat * b1.toNat + a3.toNat * b0.toNat
    let d4 := a1.toNat * b3.toNat + a2.toNat * b2.toNat + a3.toNat * b1.toNat
    let c1 := d0 / 2 ^ 64
    let c2 := (d1 + c1) / 2 ^ 64
    let c3 := (d2 + c2) / 2 ^ 64
    let c4 := (d3 + c3) / 2 ^ 64
    (mulModProductLayoutColumn4Call08P120FeedValue a b).toNat = (d4 + c4) % 2 ^ 64 := by
  dsimp only
  rw [mulModProductLayoutColumn4Call08P120FeedValue_toNat_eq_call09P128_plus_d4]
  rw [mulModProductLayoutCall09P128_toNat_eq_limb3Carry]
  omega

/-- The call08 feed cell is the fourth schoolbook product limb. -/
theorem mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4 := by
  apply BitVec.eq_of_toNat_eq
  rw [mulModProductLayoutColumn4Call08P120FeedValue_toNat_eq_schoolbook_limb4]
  simp only [productLimb, productNat, BitVec.toNat_ofNat, Nat.reduceMul]
  rw [EvmWord.toNat_eq_limb_sum a, EvmWord.toNat_eq_limb_sum b]
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
  rw [mulModProductLayoutSchoolbookLimb4]

/-- The folded call08-feed target is exactly the existing expanded column-four target. -/
theorem mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four_iff_expandedValue
    (a b : EvmWord) :
    (mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) ↔
      (mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4) := by
  rw [mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue]

/-- The public folded column-four value and call08-feed target are interchangeable
    as the remaining product-limb-4 proof obligation. -/
theorem mulModProductLayoutColumn4Value_eq_productLimb_four_iff_call08P120FeedValue
    (a b : EvmWord) :
    (mulModProductLayoutColumn4Value a b = productLimb a b 4) ↔
      (mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) := by
  rw [mulModProductLayoutColumn4Value_eq_expandedValue,
    mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue]

/-- The concrete call12 P128 cell has the same product-limb-4 proof obligation
    as the folded call08-feed target. -/
theorem mulModProductLayoutCall12P128_eq_productLimb_four_iff_call08P120FeedValue
    (a b : EvmWord) :
    (mulModProductLayoutCall12P128 a b = productLimb a b 4) ↔
      (mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) := by
  rw [mulModProductLayoutCall12P128_eq_column4Value,
    mulModProductLayoutColumn4Value_eq_expandedValue,
    mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue]

/-- The concrete call12 P128 cell is the fourth schoolbook product limb. -/
theorem mulModProductLayoutCall12P128_eq_productLimb_four (a b : EvmWord) :
    mulModProductLayoutCall12P128 a b = productLimb a b 4 := by
  exact (mulModProductLayoutCall12P128_eq_productLimb_four_iff_call08P120FeedValue
    a b).2 (mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four a b)

/-- The concrete call12 high-limb target is equivalent to the folded
    call08-feed product-limb-4 obligation. -/
theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_iff_call08P120FeedValue
    (a b : EvmWord) :
    (mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0) ↔
      (mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) := by
  rw [← productLimb_four_eq_mulHigh_getLimbN_zero]
  exact mulModProductLayoutCall12P128_eq_productLimb_four_iff_call08P120FeedValue a b

/-- The concrete call12 P128 cell is the low limb of the high 256-bit product. -/
theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero (a b : EvmWord) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact (mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_iff_call08P120FeedValue
    a b).2 (mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four a b)

/-- The folded call08-feed product-limb-4 target is the same as the direct
    mulHigh limb0 target. -/
theorem mulModProductLayoutColumn4Call08P120FeedValue_eq_mulHigh_getLimbN_zero_iff_productLimb_four
    (a b : EvmWord) :
    (mulModProductLayoutColumn4Call08P120FeedValue a b =
        (EvmWord.mulHigh a b).getLimbN 0) ↔
      (mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) := by
  rw [← productLimb_four_eq_mulHigh_getLimbN_zero]

theorem mulModProductLayoutColumn4Call08P120FeedValue_eq_mulHigh_getLimbN_zero_of_productLimb_four
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call08P120FeedValue a b =
      (EvmWord.mulHigh a b).getLimbN 0 := by
  exact (mulModProductLayoutColumn4Call08P120FeedValue_eq_mulHigh_getLimbN_zero_iff_productLimb_four
    a b).2 h_col

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call08P120FeedValue_mulHigh
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b =
      (EvmWord.mulHigh a b).getLimbN 0) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  rw [mulModProductLayoutCall12P128_eq_column4Value,
    mulModProductLayoutColumn4Value_eq_expandedValue,
    ← mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue,
    h_col]

theorem mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four_of_call12P128_mulHigh
    {a b : EvmWord}
    (h_col : mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0) :
    mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4 := by
  exact (mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_iff_call08P120FeedValue
    a b).1 h_col

end EvmAsm.Evm64
