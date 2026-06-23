import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Target
import EvmAsm.Evm64.MulMod.ProductLayoutCall15

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

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
