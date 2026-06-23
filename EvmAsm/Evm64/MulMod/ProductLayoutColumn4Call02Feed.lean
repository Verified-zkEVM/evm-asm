import EvmAsm.Evm64.MulMod.ProductLayoutPublicAlgebra

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.MulMod.ProductAlgebra

/-- Column-4 call03-feed value with the call02 high carry expanded into
    the explicit carry out of the two column-1 high/carry contributions. -/
@[irreducible] def mulModProductLayoutColumn4Call02FeedValue (a b : EvmWord) : Word :=
  let hi01 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)
  let carry01 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
      (a.getLimbN 0 * b.getLimbN 1) then (1 : Word) else 0
  let hi10 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)
  let carry10 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
      (1 : Word) else 0
  let carry02Prefix := if BitVec.ult ((hi01 + carry01) + (hi10 + carry10))
      (hi01 + carry01) then (1 : Word) else 0
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
      (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (mulModProductLayoutCall04P112 a b + a.getLimbN 0 * b.getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed03 := carry02Prefix + (hi20 + carry20)
  let feed04 := feed03 + (hi11 + carry11)
  let feed05 := feed04 + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult feed03 (hi20 + carry20) then (1 : Word) else 0) +
      (if BitVec.ult feed04 (hi11 + carry11) then (1 : Word) else 0)) +
      (if BitVec.ult feed05 (hi02 + carry02) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (feed05 + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (feed06 + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (feed07 + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult ((a * b).getLimbN 3) (a.getLimbN 0 * b.getLimbN 3) then
        (1 : Word)
      else
        0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

theorem mulModProductLayoutColumn4Call03FeedValue_eq_call02FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Call03FeedValue a b =
      mulModProductLayoutColumn4Call02FeedValue a b := by
  unfold mulModProductLayoutColumn4Call03FeedValue mulModProductLayoutColumn4Call02FeedValue
  rw [mulModProductLayoutCall02P120_eq_expanded]

theorem mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_call02FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call03FeedValue_eq_call02FeedValue, h_col]

theorem mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_call02FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call04FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_call03FeedValue
    (mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_call02FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call02FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call03FeedValue
    (mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_call02FeedValue h_col)

end EvmAsm.Evm64
