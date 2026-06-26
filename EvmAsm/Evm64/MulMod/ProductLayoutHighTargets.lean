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
  [((3968 : BitVec 12), mulModProductLayoutCall12P128 a b),
   ((3976 : BitVec 12), mulModProductLayoutColumn5Value a b),
   ((3984 : BitVec 12), mulModProductLayoutColumn6Value a b),
   ((3992 : BitVec 12), mulModProductLayoutColumn7Value a b)]

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
      [((3968 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 0),
       ((3976 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 1),
       ((3984 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 2),
       ((3992 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 3)] := by
  rw [mulModProductLayoutHighOffsetValues_eq_productOffsetValues_drop_four_of_columnTargets
    h4 h5 h6 h7]
  simp [productOffsetValues, productOffsetIndices, EvmWord.getLimb_as_getLimbN_0,
    EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
    EvmWord.getLimb_as_getLimbN_3]


/-- The finalized high product-layout cells are exactly `productHighLimbs`. -/
theorem mulModProductLayoutHighTargetValues_eq_productHighLimbs (a b : EvmWord) :
    mulModProductLayoutHighTargetValues a b = productHighLimbs a b := by
  exact mulModProductLayoutHighTargetValues_eq_productHighLimbs_of_columnTargets
    (mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four a b)
    (mulModProductLayoutColumn5Value_eq_productLimb_five a b)
    (mulModProductLayoutColumn6Value_eq_productLimb_six a b)
    (mulModProductLayoutColumn7Value_eq_productLimb_seven a b)

/-- The finalized high product-layout cells are the limbs of `mulHigh`. -/
theorem mulModProductLayoutHighTargetValues_eq_mulHigh_getLimbNs (a b : EvmWord) :
    mulModProductLayoutHighTargetValues a b =
      [(EvmWord.mulHigh a b).getLimbN 0, (EvmWord.mulHigh a b).getLimbN 1,
       (EvmWord.mulHigh a b).getLimbN 2, (EvmWord.mulHigh a b).getLimbN 3] := by
  exact mulModProductLayoutHighTargetValues_eq_mulHigh_getLimbNs_of_columnTargets
    (mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four a b)
    (mulModProductLayoutColumn5Value_eq_productLimb_five a b)
    (mulModProductLayoutColumn6Value_eq_productLimb_six a b)
    (mulModProductLayoutColumn7Value_eq_productLimb_seven a b)

/-- The finalized high product-layout offset cells are the high half of `productOffsetValues`. -/
theorem mulModProductLayoutHighOffsetValues_eq_productOffsetValues_drop_four (a b : EvmWord) :
    mulModProductLayoutHighOffsetValues a b = (productOffsetValues a b).drop 4 := by
  exact mulModProductLayoutHighOffsetValues_eq_productOffsetValues_drop_four_of_columnTargets
    (mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four a b)
    (mulModProductLayoutColumn5Value_eq_productLimb_five a b)
    (mulModProductLayoutColumn6Value_eq_productLimb_six a b)
    (mulModProductLayoutColumn7Value_eq_productLimb_seven a b)

/-- The finalized high product-layout offset cells are the direct `mulHigh` limbs. -/
theorem mulModProductLayoutHighOffsetValues_eq_mulHigh_getLimbNs (a b : EvmWord) :
    mulModProductLayoutHighOffsetValues a b =
      [((3968 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 0),
       ((3976 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 1),
       ((3984 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 2),
       ((3992 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 3)] := by
  exact mulModProductLayoutHighOffsetValues_eq_mulHigh_getLimbNs_of_columnTargets
    (mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four a b)
    (mulModProductLayoutColumn5Value_eq_productLimb_five a b)
    (mulModProductLayoutColumn6Value_eq_productLimb_six a b)
    (mulModProductLayoutColumn7Value_eq_productLimb_seven a b)

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
  [((3968 : BitVec 12), mulModProductLayoutCall12P128 a b),
   ((3976 : BitVec 12), mulModProductLayoutCall14P136 a b),
   ((3984 : BitVec 12), mulModAddPartialLoValue (mulModProductLayoutCall14P144 a b)
    (a.getLimbN 3) (b.getLimbN 3)),
   ((3992 : BitVec 12), mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
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



/-- The concrete final high cells identify with `productHighLimbs`. -/
theorem mulModProductLayoutConcreteHighTargetValues_eq_productHighLimbs (a b : EvmWord) :
    mulModProductLayoutConcreteHighTargetValues a b = productHighLimbs a b := by
  rw [mulModProductLayoutConcreteHighTargetValues_eq_highTargetValues]
  exact mulModProductLayoutHighTargetValues_eq_productHighLimbs a b

/-- The concrete final high cells are the direct `mulHigh.getLimbN` limbs. -/
theorem mulModProductLayoutConcreteHighTargetValues_eq_mulHigh_getLimbNs_noHyp (a b : EvmWord) :
    mulModProductLayoutConcreteHighTargetValues a b =
      [(EvmWord.mulHigh a b).getLimbN 0, (EvmWord.mulHigh a b).getLimbN 1,
       (EvmWord.mulHigh a b).getLimbN 2, (EvmWord.mulHigh a b).getLimbN 3] := by
  exact mulModProductLayoutConcreteHighTargetValues_eq_mulHigh_getLimbNs
    (mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero a b)
    (mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one a b)
    (mulModProductLayoutCall15P144Value_eq_mulHigh_getLimbN_two a b)
    (mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three a b)

/-- The concrete final high offset cells are the high half of `productOffsetValues`. -/
theorem mulModProductLayoutConcreteHighOffsetValues_eq_productOffsetValues_drop_four_noHyp
    (a b : EvmWord) :
    mulModProductLayoutConcreteHighOffsetValues a b = (productOffsetValues a b).drop 4 := by
  exact mulModProductLayoutConcreteHighOffsetValues_eq_productOffsetValues_drop_four
    (mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero a b)
    (mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one a b)
    (mulModProductLayoutCall15P144Value_eq_mulHigh_getLimbN_two a b)
    (mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three a b)

/-- The concrete final high offset cells are the direct `mulHigh.getLimbN` limbs. -/
theorem mulModProductLayoutConcreteHighOffsetValues_eq_mulHigh_getLimbNs_noHyp
    (a b : EvmWord) :
    mulModProductLayoutConcreteHighOffsetValues a b =
      [((3968 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 0),
       ((3976 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 1),
       ((3984 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 2),
       ((3992 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 3)] := by
  rw [mulModProductLayoutConcreteHighOffsetValues_eq_highOffsetValues]
  exact mulModProductLayoutHighOffsetValues_eq_mulHigh_getLimbNs a b

/-- Column-target obligations identify the concrete final high cells with
    `productHighLimbs`. -/
theorem mulModProductLayoutConcreteHighTargetValues_eq_productHighLimbs_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutConcreteHighTargetValues a b = productHighLimbs a b := by
  rw [mulModProductLayoutConcreteHighTargetValues_eq_highTargetValues]
  exact mulModProductLayoutHighTargetValues_eq_productHighLimbs_of_columnTargets
    h4 h5 h6 h7

/-- Column-target obligations identify the concrete final high cells with
    `mulHigh.getLimbN` limbs. -/
theorem mulModProductLayoutConcreteHighTargetValues_eq_mulHigh_getLimbNs_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutConcreteHighTargetValues a b =
      [(EvmWord.mulHigh a b).getLimbN 0, (EvmWord.mulHigh a b).getLimbN 1,
       (EvmWord.mulHigh a b).getLimbN 2, (EvmWord.mulHigh a b).getLimbN 3] := by
  rw [mulModProductLayoutConcreteHighTargetValues_eq_highTargetValues]
  exact mulModProductLayoutHighTargetValues_eq_mulHigh_getLimbNs_of_columnTargets
    h4 h5 h6 h7

/-- Column-target obligations identify the concrete final high offset cells with
    the high half of `productOffsetValues`. -/
theorem mulModProductLayoutConcreteHighOffsetValues_eq_productOffsetValues_drop_four_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutConcreteHighOffsetValues a b = (productOffsetValues a b).drop 4 := by
  rw [mulModProductLayoutConcreteHighOffsetValues_eq_highOffsetValues]
  exact mulModProductLayoutHighOffsetValues_eq_productOffsetValues_drop_four_of_columnTargets
    h4 h5 h6 h7

/-- Column-target obligations identify the concrete final high offset cells with
    the direct `mulHigh.getLimbN` view. -/
theorem mulModProductLayoutConcreteHighOffsetValues_eq_mulHigh_getLimbNs_of_columnTargets
    {a b : EvmWord}
    (h4 : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4)
    (h5 : mulModProductLayoutColumn5Value a b = productLimb a b 5)
    (h6 : mulModProductLayoutColumn6Value a b = productLimb a b 6)
    (h7 : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutConcreteHighOffsetValues a b =
      [((3968 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 0),
       ((3976 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 1),
       ((3984 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 2),
       ((3992 : BitVec 12), (EvmWord.mulHigh a b).getLimbN 3)] := by
  rw [mulModProductLayoutConcreteHighOffsetValues_eq_highOffsetValues]
  exact mulModProductLayoutHighOffsetValues_eq_mulHigh_getLimbNs_of_columnTargets
    h4 h5 h6 h7


end EvmAsm.Evm64
