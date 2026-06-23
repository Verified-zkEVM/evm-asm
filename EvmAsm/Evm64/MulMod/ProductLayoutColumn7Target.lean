import EvmAsm.Evm64.MulMod.ProductLayoutColumn6Target

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- The finalized product-layout column-seven cell at offset 152. -/
def mulModProductLayoutColumn7Value (a b : EvmWord) : Word :=
  mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
    (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3)

/-- The concrete call15 P152 cell is the folded column-seven target. -/
theorem mulModProductLayoutCall15P152Value_eq_column7Value (a b : EvmWord) :
    mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
      mulModProductLayoutColumn7Value a b := by
  rfl

/-- The concrete call15 P152 cell has the same product-limb-7 proof obligation
    as the folded column-seven target. -/
theorem mulModProductLayoutCall15P152Value_eq_productLimb_seven_iff_column7Value
    (a b : EvmWord) :
    (mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
        (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        productLimb a b 7) ↔
      (mulModProductLayoutColumn7Value a b = productLimb a b 7) := by
  rfl

/-- The concrete call15 high-limb target is equivalent to the folded
    column-seven product-limb obligation. -/
theorem mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three_iff_column7Value
    (a b : EvmWord) :
    (mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
        (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3) ↔
      (mulModProductLayoutColumn7Value a b = productLimb a b 7) := by
  rw [← productLimb_seven_eq_mulHigh_getLimbN_three]
  exact mulModProductLayoutCall15P152Value_eq_productLimb_seven_iff_column7Value a b

/-- The folded column-seven product-limb target is the same as the direct
    mulHigh limb3 target. -/
theorem mulModProductLayoutColumn7Value_eq_mulHigh_getLimbN_three_iff_productLimb_seven
    (a b : EvmWord) :
    (mulModProductLayoutColumn7Value a b =
        (EvmWord.mulHigh a b).getLimbN 3) ↔
      (mulModProductLayoutColumn7Value a b = productLimb a b 7) := by
  rw [← productLimb_seven_eq_mulHigh_getLimbN_three]

theorem mulModProductLayoutColumn7Value_eq_mulHigh_getLimbN_three_of_productLimb_seven
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn7Value a b = productLimb a b 7) :
    mulModProductLayoutColumn7Value a b =
      (EvmWord.mulHigh a b).getLimbN 3 := by
  exact (mulModProductLayoutColumn7Value_eq_mulHigh_getLimbN_three_iff_productLimb_seven
    a b).2 h_col

theorem mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three_of_column7Value_mulHigh
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn7Value a b =
      (EvmWord.mulHigh a b).getLimbN 3) :
    mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3 := by
  rw [mulModProductLayoutCall15P152Value_eq_column7Value, h_col]

theorem mulModProductLayoutColumn7Value_eq_productLimb_seven_of_call15P152Value_mulHigh
    {a b : EvmWord}
    (h_col : mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
      (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3) =
        (EvmWord.mulHigh a b).getLimbN 3) :
    mulModProductLayoutColumn7Value a b = productLimb a b 7 := by
  exact (mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three_iff_column7Value
    a b).1 h_col

end EvmAsm.Evm64
