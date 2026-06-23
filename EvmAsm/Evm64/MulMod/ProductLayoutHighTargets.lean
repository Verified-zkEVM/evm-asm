import EvmAsm.Evm64.MulMod.ProductLayoutColumn7Target

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- The four finalized high product-layout cells, in product-limb order. -/
def mulModProductLayoutHighTargetValues (a b : EvmWord) : List Word :=
  [mulModProductLayoutCall12P128 a b,
   mulModProductLayoutColumn5Value a b,
   mulModProductLayoutColumn6Value a b,
   mulModProductLayoutColumn7Value a b]

/-- The finalized high product-layout cells paired with their runtime offsets. -/
def mulModProductLayoutHighOffsetValues (a b : EvmWord) : List (BitVec 12 × Word) :=
  [((128 : BitVec 12), mulModProductLayoutCall12P128 a b),
   ((136 : BitVec 12), mulModProductLayoutColumn5Value a b),
   ((144 : BitVec 12), mulModProductLayoutColumn6Value a b),
   ((152 : BitVec 12), mulModProductLayoutColumn7Value a b)]

/-- Column-target obligations are exactly enough to identify the high product
    cells with `productHighLimbs`. -/
theorem mulModProductLayoutHighTargetValues_eq_productHighLimbs_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutHighTargetValues a b = productHighLimbs a b := by
  rw [mulModProductLayoutHighTargetValues, productHighLimbs_eq,
    (mulModProductLayoutCall12P128_eq_productLimb_four_iff_call08P120FeedValue
      a b).2 h4, h5, h6, h7]

/-- Column-target obligations identify the high product cells with `mulHigh` limbs. -/
theorem mulModProductLayoutHighTargetValues_eq_mulHigh_getLimbNs_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutHighTargetValues a b =
      [(EvmWord.mulHigh a b).getLimbN 0, (EvmWord.mulHigh a b).getLimbN 1,
       (EvmWord.mulHigh a b).getLimbN 2, (EvmWord.mulHigh a b).getLimbN 3] := by
  rw [mulModProductLayoutHighTargetValues_eq_productHighLimbs_of_columnTargets
    h4 h5 h6 h7, productHighLimbs_eq_mulHigh_getLimbNs]

/-- Column-target obligations identify the high runtime product-window offsets
    with the algebraic `productOffsetValues` high half. -/
theorem mulModProductLayoutHighOffsetValues_eq_productOffsetValues_drop_four_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutHighOffsetValues a b = (productOffsetValues a b).drop 4 := by
  rw [mulModProductLayoutHighOffsetValues, productOffsetValues, productOffsetIndices,
    (mulModProductLayoutCall12P128_eq_productLimb_four_iff_call08P120FeedValue
      a b).2 h4, h5, h6, h7]
  rfl

/-- Column-target obligations identify the high runtime product-window offsets
    with the direct `mulHigh.getLimbN` view. -/
theorem mulModProductLayoutHighOffsetValues_eq_mulHigh_getLimbNs_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutHighOffsetValues a b =
      [((128 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 0),
       ((136 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 1),
       ((144 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 2),
       ((152 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 3)] := by
  rw [mulModProductLayoutHighOffsetValues_eq_productOffsetValues_drop_four_of_columnTargets
    h4 h5 h6 h7]
  simp [productOffsetValues, productOffsetIndices, EvmWord.getLimb_as_getLimbN_0,
    EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
    EvmWord.getLimb_as_getLimbN_3]

end EvmAsm.Evm64
