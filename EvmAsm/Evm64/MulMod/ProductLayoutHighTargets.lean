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

/-- The concrete final high product-layout cells as they appear in the call15 postcondition. -/
def mulModProductLayoutConcreteHighTargetValues (a b : EvmWord) : List Word :=
  [mulModProductLayoutCall12P128 a b,
   mulModProductLayoutCall14P136 a b,
   mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
    (a.getLimbN 3) (b.getLimbN 3),
   mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
    (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3)]

/-- The concrete final high product-layout cells paired with their runtime offsets. -/
def mulModProductLayoutConcreteHighOffsetValues (a b : EvmWord) : List (BitVec 12 × Word) :=
  [((128 : BitVec 12), mulModProductLayoutCall12P128 a b),
   ((136 : BitVec 12), mulModProductLayoutCall14P136 a b),
   ((144 : BitVec 12), mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
    (a.getLimbN 3) (b.getLimbN 3)),
   ((152 : BitVec 12), mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
    (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3))]

/-- The concrete call15 high cells are exactly the folded target values. -/
theorem mulModProductLayoutConcreteHighTargetValues_eq_highTargetValues
    (a b : EvmWord) :
    mulModProductLayoutConcreteHighTargetValues a b =
      mulModProductLayoutHighTargetValues a b := by
  rfl

/-- The concrete call15 high offset cells are exactly the folded target offsets. -/
theorem mulModProductLayoutConcreteHighOffsetValues_eq_highOffsetValues
    (a b : EvmWord) :
    mulModProductLayoutConcreteHighOffsetValues a b =
      mulModProductLayoutHighOffsetValues a b := by
  rfl

/-- Direct concrete high-cell aliases identify the final high cells with `mulHigh` limbs. -/
theorem mulModProductLayoutConcreteHighTargetValues_eq_mulHigh_getLimbNs
    {a b : EvmWord}
    (h128 : mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0)
    (h136 : mulModProductLayoutCall14P136 a b = (EvmWord.mulHigh a b).getLimbN 1)
    (h144 : mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
      (a.getLimbN 3) (b.getLimbN 3) = (EvmWord.mulHigh a b).getLimbN 2)
    (h152 : mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3) :
    mulModProductLayoutConcreteHighTargetValues a b =
      [(EvmWord.mulHigh a b).getLimbN 0, (EvmWord.mulHigh a b).getLimbN 1,
       (EvmWord.mulHigh a b).getLimbN 2, (EvmWord.mulHigh a b).getLimbN 3] := by
  rw [mulModProductLayoutConcreteHighTargetValues, h128, h136, h144, h152]

/-- Direct concrete high-cell aliases identify the final high offset cells with
    the high half of `productOffsetValues`. -/
theorem mulModProductLayoutConcreteHighOffsetValues_eq_productOffsetValues_drop_four
    {a b : EvmWord}
    (h128 : mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0)
    (h136 : mulModProductLayoutCall14P136 a b = (EvmWord.mulHigh a b).getLimbN 1)
    (h144 : mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
      (a.getLimbN 3) (b.getLimbN 3) = (EvmWord.mulHigh a b).getLimbN 2)
    (h152 : mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3) :
    mulModProductLayoutConcreteHighOffsetValues a b = (productOffsetValues a b).drop 4 := by
  rw [mulModProductLayoutConcreteHighOffsetValues, h128, h136, h144, h152]
  simp [productOffsetValues, productOffsetIndices, EvmWord.getLimb_as_getLimbN_0,
    EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
    EvmWord.getLimb_as_getLimbN_3]


end EvmAsm.Evm64
