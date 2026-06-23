import EvmAsm.Evm64.MulMod.ProductLayoutColumn5Target

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

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
