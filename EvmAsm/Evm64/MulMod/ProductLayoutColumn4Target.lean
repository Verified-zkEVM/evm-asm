import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Call02Feed

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

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

/-- The concrete call12 high-limb target is equivalent to the folded
    call08-feed product-limb-4 obligation. -/
theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_iff_call08P120FeedValue
    (a b : EvmWord) :
    (mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0) ↔
      (mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) := by
  rw [← productLimb_four_eq_mulHigh_getLimbN_zero]
  exact mulModProductLayoutCall12P128_eq_productLimb_four_iff_call08P120FeedValue a b

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
