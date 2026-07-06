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

/-- Column-4 call02-feed value with the call02 low-column-2 cell expanded
    into the explicit column-1 high/carry sum used by the next low carry. -/
@[irreducible] def mulModProductLayoutColumn4Call02P112FeedValue (a b : EvmWord) : Word :=
  let hi01 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)
  let carry01 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
      (a.getLimbN 0 * b.getLimbN 1) then (1 : Word) else 0
  let hi10 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)
  let carry10 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
      (1 : Word) else 0
  let p112 := hi01 + hi10 + carry01 + carry10
  let carry02Prefix := if BitVec.ult ((hi01 + carry01) + (hi10 + carry10))
      (hi01 + carry01) then (1 : Word) else 0
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (p112 + a.getLimbN 2 * b.getLimbN 0)
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

/-- Column-4 call02-P112-feed value with the call03 low-column-2 cell
    expanded into the explicit column-1 high/carry sum plus `a2*b0`. -/
@[irreducible] def mulModProductLayoutColumn4Call03P112FeedValue (a b : EvmWord) : Word :=
  let hi01 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)
  let carry01 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
      (a.getLimbN 0 * b.getLimbN 1) then (1 : Word) else 0
  let hi10 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)
  let carry10 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
      (1 : Word) else 0
  let p112 := hi01 + hi10 + carry01 + carry10
  let p112a := p112 + a.getLimbN 2 * b.getLimbN 0
  let carry02Prefix := if BitVec.ult ((hi01 + carry01) + (hi10 + carry10))
      (hi01 + carry01) then (1 : Word) else 0
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (p112 + a.getLimbN 2 * b.getLimbN 0)
      (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (p112a + a.getLimbN 1 * b.getLimbN 1)
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

/-- Column-4 call03-P112-feed value with the call04 low-column-2 cell
    expanded into the explicit column-1 high/carry sum plus `a2*b0 + a1*b1`. -/
@[irreducible] def mulModProductLayoutColumn4Call04P112FeedValue (a b : EvmWord) : Word :=
  let hi01 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)
  let carry01 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
      (a.getLimbN 0 * b.getLimbN 1) then (1 : Word) else 0
  let hi10 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)
  let carry10 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
      (1 : Word) else 0
  let p112 := hi01 + hi10 + carry01 + carry10
  let p112a := p112 + a.getLimbN 2 * b.getLimbN 0
  let p112b := p112a + a.getLimbN 1 * b.getLimbN 1
  let carry02Prefix := if BitVec.ult ((hi01 + carry01) + (hi10 + carry10))
      (hi01 + carry01) then (1 : Word) else 0
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (p112 + a.getLimbN 2 * b.getLimbN 0)
      (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (p112a + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (p112b + a.getLimbN 0 * b.getLimbN 2)
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

/-- Column-4 call04-P112-feed value with the final low-column-2 cell folded
    back to the layout's call05 P112 value. -/
@[irreducible] def mulModProductLayoutColumn4Call05P112FeedValue (a b : EvmWord) : Word :=
  let hi01 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)
  let carry01 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
      (a.getLimbN 0 * b.getLimbN 1) then (1 : Word) else 0
  let hi10 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)
  let carry10 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
      (1 : Word) else 0
  let p112 := hi01 + hi10 + carry01 + carry10
  let p112a := p112 + a.getLimbN 2 * b.getLimbN 0
  let carry02Prefix := if BitVec.ult ((hi01 + carry01) + (hi10 + carry10))
      (hi01 + carry01) then (1 : Word) else 0
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (p112 + a.getLimbN 2 * b.getLimbN 0)
      (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (p112a + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult (mulModProductLayoutCall05P112 a b)
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

/-- Column-4 call05-P112-feed value with the final low-column-2 cell exposed
    as the concrete second limb of the full product. -/
@[irreducible] def mulModProductLayoutColumn4Limb2FeedValue (a b : EvmWord) : Word :=
  let hi01 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 1)
  let carry01 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0 + a.getLimbN 0 * b.getLimbN 1)
      (a.getLimbN 0 * b.getLimbN 1) then (1 : Word) else 0
  let hi10 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 0)
  let carry10 := if BitVec.ult (rv64_mulhu (a.getLimbN 0) (b.getLimbN 0) +
      a.getLimbN 1 * b.getLimbN 0) (a.getLimbN 1 * b.getLimbN 0) then
      (1 : Word) else 0
  let p112 := hi01 + hi10 + carry01 + carry10
  let p112a := p112 + a.getLimbN 2 * b.getLimbN 0
  let carry02Prefix := if BitVec.ult ((hi01 + carry01) + (hi10 + carry10))
      (hi01 + carry01) then (1 : Word) else 0
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (p112 + a.getLimbN 2 * b.getLimbN 0)
      (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (p112a + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult ((a * b).getLimbN 2)
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

/-- Column-4 limb2-feed value with the first high carry folded back to
    the layout's call02 P120 value. -/
@[irreducible] def mulModProductLayoutColumn4Call02P120Limb2FeedValue (a b : EvmWord) : Word :=
  let hi20 := rv64_mulhu (a.getLimbN 2) (b.getLimbN 0)
  let carry20 := if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
      (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult ((a * b).getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed03 := mulModProductLayoutCall02P120 a b + (hi20 + carry20)
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

/-- Column-4 call02-P120 limb2-feed value with the next high carry folded
    back to the layout's call03 P120 value. -/
@[irreducible] def mulModProductLayoutColumn4Call03P120Limb2FeedValue (a b : EvmWord) : Word :=
  let hi11 := rv64_mulhu (a.getLimbN 1) (b.getLimbN 1)
  let carry11 := if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
      (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult ((a * b).getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed04 := mulModProductLayoutCall03P120 a b + (hi11 + carry11)
  let feed05 := feed04 + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
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

/-- Column-4 call03-P120 limb2-feed value with the next high carry folded
    back to the layout's call04 P120 value. -/
@[irreducible] def mulModProductLayoutColumn4Call04P120Limb2FeedValue (a b : EvmWord) : Word :=
  let hi02 := rv64_mulhu (a.getLimbN 0) (b.getLimbN 2)
  let carry02 := if BitVec.ult ((a * b).getLimbN 2)
      (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0
  let feed05 := mulModProductLayoutCall04P120 a b + (hi02 + carry02)
  let feed06 := feed05 + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
      (if BitVec.ult (mulModProductLayoutCall03P120 a b +
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
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

/-- Column-4 call04-P120 limb2-feed value with the column-2 high feed folded
    back to the layout's call05 P120 value. -/
@[irreducible] def mulModProductLayoutColumn4Call05P120FeedValue (a b : EvmWord) : Word :=
  let feed06 := mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0
  let feed07 := feed06 + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
      (if BitVec.ult (mulModProductLayoutCall03P120 a b +
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
      (if BitVec.ult (mulModProductLayoutCall04P120 a b +
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
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

/-- Column-4 call05-P120 feed value with the next running high-feed cell
    folded back to the layout's call06 P120 value. -/
@[irreducible] def mulModProductLayoutColumn4Call06P120FeedValue (a b : EvmWord) : Word :=
  let feed07 := mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
      (if BitVec.ult (mulModProductLayoutCall03P120 a b +
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
      (if BitVec.ult (mulModProductLayoutCall04P120 a b +
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
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

/-- Column-4 call06-P120 feed value with the next running high-feed cell
    folded back to the layout's call07 P120 value. -/
@[irreducible] def mulModProductLayoutColumn4Call07P120FeedValue (a b : EvmWord) : Word :=
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
      (if BitVec.ult (mulModProductLayoutCall03P120 a b +
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
      (if BitVec.ult (mulModProductLayoutCall04P120 a b +
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult ((a * b).getLimbN 3) (a.getLimbN 0 * b.getLimbN 3) then
        (1 : Word)
      else
        0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

/-- Column-4 call07-P120 feed value with the final running high-feed cell
    folded back to the layout's call08 P120 value. -/
@[irreducible] def mulModProductLayoutColumn4Call08P120FeedValue (a b : EvmWord) : Word :=
  (((if BitVec.ult (mulModProductLayoutCall02P120 a b +
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 2) (b.getLimbN 0) +
            (if BitVec.ult (mulModProductLayoutCall02P112 a b + a.getLimbN 2 * b.getLimbN 0)
                (a.getLimbN 2 * b.getLimbN 0) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0) +
      (if BitVec.ult (mulModProductLayoutCall03P120 a b +
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 1) (b.getLimbN 1) +
            (if BitVec.ult (mulModProductLayoutCall03P112 a b + a.getLimbN 1 * b.getLimbN 1)
                (a.getLimbN 1 * b.getLimbN 1) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
      (if BitVec.ult (mulModProductLayoutCall04P120 a b +
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)))
          (rv64_mulhu (a.getLimbN 0) (b.getLimbN 2) +
            (if BitVec.ult (mulModProductLayoutCall05P112 a b)
                (a.getLimbN 0 * b.getLimbN 2) then (1 : Word) else 0)) then
        (1 : Word)
      else
        0)) +
    (rv64_mulhu (a.getLimbN 3) (b.getLimbN 0) +
      (if BitVec.ult (mulModProductLayoutCall05P120 a b + a.getLimbN 3 * b.getLimbN 0)
          (a.getLimbN 3 * b.getLimbN 0) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 2) (b.getLimbN 1) +
      (if BitVec.ult (mulModProductLayoutCall06P120 a b + a.getLimbN 2 * b.getLimbN 1)
          (a.getLimbN 2 * b.getLimbN 1) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 1) (b.getLimbN 2) +
      (if BitVec.ult (mulModProductLayoutCall07P120 a b + a.getLimbN 1 * b.getLimbN 2)
          (a.getLimbN 1 * b.getLimbN 2) then (1 : Word) else 0)) +
    (rv64_mulhu (a.getLimbN 0) (b.getLimbN 3) +
      (if BitVec.ult (mulModProductLayoutCall08P120 a b + a.getLimbN 0 * b.getLimbN 3)
          (a.getLimbN 0 * b.getLimbN 3) then (1 : Word) else 0)) +
    a.getLimbN 3 * b.getLimbN 1 +
    a.getLimbN 2 * b.getLimbN 2 +
    a.getLimbN 1 * b.getLimbN 3

theorem mulModProductLayoutColumn4Call02FeedValue_eq_call02P112FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Call02FeedValue a b =
      mulModProductLayoutColumn4Call02P112FeedValue a b := by
  unfold mulModProductLayoutColumn4Call02FeedValue mulModProductLayoutColumn4Call02P112FeedValue
  rw [mulModProductLayoutCall02P112_eq_expanded]

theorem mulModProductLayoutColumn4Call02P112FeedValue_eq_call03P112FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Call02P112FeedValue a b =
      mulModProductLayoutColumn4Call03P112FeedValue a b := by
  unfold mulModProductLayoutColumn4Call02P112FeedValue mulModProductLayoutColumn4Call03P112FeedValue
  rw [mulModProductLayoutCall03P112_eq_expanded]

theorem mulModProductLayoutColumn4Call03P112FeedValue_eq_call04P112FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Call03P112FeedValue a b =
      mulModProductLayoutColumn4Call04P112FeedValue a b := by
  unfold mulModProductLayoutColumn4Call03P112FeedValue mulModProductLayoutColumn4Call04P112FeedValue
  rw [mulModProductLayoutCall04P112_eq_expanded]

theorem mulModProductLayoutColumn4Call04P112FeedValue_eq_call05P112FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Call04P112FeedValue a b =
      mulModProductLayoutColumn4Call05P112FeedValue a b := by
  unfold mulModProductLayoutColumn4Call04P112FeedValue mulModProductLayoutColumn4Call05P112FeedValue
  rw [mulModProductLayoutCall05P112_eq_add, mulModProductLayoutCall04P112_eq_expanded]
  simp only [mulModAddPartialLoProduct]
  ac_rfl

theorem mulModProductLayoutColumn4Call05P112FeedValue_eq_limb2FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Call05P112FeedValue a b =
      mulModProductLayoutColumn4Limb2FeedValue a b := by
  unfold mulModProductLayoutColumn4Call05P112FeedValue mulModProductLayoutColumn4Limb2FeedValue
  rw [mulModProductLayoutCall05P112_eq_mul_limb2]

theorem mulModProductLayoutColumn4Limb2FeedValue_eq_call02P120Limb2FeedValue (a b : EvmWord) :
    mulModProductLayoutColumn4Limb2FeedValue a b =
      mulModProductLayoutColumn4Call02P120Limb2FeedValue a b := by
  unfold mulModProductLayoutColumn4Limb2FeedValue
    mulModProductLayoutColumn4Call02P120Limb2FeedValue
  rw [← mulModProductLayoutCall05P112_eq_mul_limb2]
  rw [mulModProductLayoutCall05P112_eq_add]
  rw [mulModProductLayoutCall04P112_eq_add]
  rw [mulModProductLayoutCall03P112_eq_add]
  rw [mulModProductLayoutCall02P112_eq_expanded]
  rw [mulModProductLayoutCall02P120_eq_expanded]
  simp only [mulModAddPartialLoProduct]
  ac_rfl

theorem mulModProductLayoutColumn4Call02P120Limb2FeedValue_eq_call03P120Limb2FeedValue
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call02P120Limb2FeedValue a b =
      mulModProductLayoutColumn4Call03P120Limb2FeedValue a b := by
  unfold mulModProductLayoutColumn4Call02P120Limb2FeedValue
    mulModProductLayoutColumn4Call03P120Limb2FeedValue
  rw [mulModProductLayoutCall03P120_eq_add]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutColumn4Call03P120Limb2FeedValue_eq_call04P120Limb2FeedValue
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call03P120Limb2FeedValue a b =
      mulModProductLayoutColumn4Call04P120Limb2FeedValue a b := by
  unfold mulModProductLayoutColumn4Call03P120Limb2FeedValue
    mulModProductLayoutColumn4Call04P120Limb2FeedValue
  rw [mulModProductLayoutCall04P120_eq_add]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutColumn4Call04P120Limb2FeedValue_eq_call05P120FeedValue
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call04P120Limb2FeedValue a b =
      mulModProductLayoutColumn4Call05P120FeedValue a b := by
  unfold mulModProductLayoutColumn4Call04P120Limb2FeedValue
    mulModProductLayoutColumn4Call05P120FeedValue
  rw [← mulModProductLayoutCall05P112_eq_mul_limb2]
  rw [mulModProductLayoutCall05P120_eq_add]
  simp only [mulModAddPartialHiProduct, mulModAddPartialLoCarry,
    mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutColumn4Call05P120FeedValue_eq_call06P120FeedValue
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call05P120FeedValue a b =
      mulModProductLayoutColumn4Call06P120FeedValue a b := by
  unfold mulModProductLayoutColumn4Call05P120FeedValue
    mulModProductLayoutColumn4Call06P120FeedValue
  rw [mulModProductLayoutCall06P120_eq_add]
  simp only [mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutColumn4Call06P120FeedValue_eq_call07P120FeedValue
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call06P120FeedValue a b =
      mulModProductLayoutColumn4Call07P120FeedValue a b := by
  unfold mulModProductLayoutColumn4Call06P120FeedValue
    mulModProductLayoutColumn4Call07P120FeedValue
  rw [mulModProductLayoutCall07P120_eq_add]
  simp only [mulModAddPartialLoProduct]
  rfl

theorem mulModProductLayoutColumn4Call07P120FeedValue_eq_call08P120FeedValue
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call07P120FeedValue a b =
      mulModProductLayoutColumn4Call08P120FeedValue a b := by
  unfold mulModProductLayoutColumn4Call07P120FeedValue
    mulModProductLayoutColumn4Call08P120FeedValue
  rw [← mulModProductLayoutCall09P120_eq_mul_limb3]
  rw [mulModProductLayoutCall09P120_eq_add]
  simp only [mulModAddPartialLoProduct]
  rfl

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

theorem mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_call02P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call02FeedValue_eq_call02P112FeedValue, h_col]

theorem mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_call02P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_call02FeedValue
    (mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_call02P112FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call02P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call02FeedValue
    (mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_call02P112FeedValue h_col)

theorem mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_call03P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02P112FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call02P112FeedValue_eq_call03P112FeedValue, h_col]

theorem mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_call03P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_call02P112FeedValue
    (mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_call03P112FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call03P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call02P112FeedValue
    (mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_call03P112FeedValue h_col)

theorem mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_call04P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03P112FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call03P112FeedValue_eq_call04P112FeedValue, h_col]

theorem mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_call04P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02P112FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_call03P112FeedValue
    (mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_call04P112FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call04P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call03P112FeedValue
    (mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_call04P112FeedValue h_col)

theorem mulModProductLayoutColumn4Call04P112FeedValue_eq_productLimb_four_of_call05P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call05P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call04P112FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call04P112FeedValue_eq_call05P112FeedValue, h_col]

theorem mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_call05P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call05P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03P112FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_call04P112FeedValue
    (mulModProductLayoutColumn4Call04P112FeedValue_eq_productLimb_four_of_call05P112FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call05P112FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call05P112FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call04P112FeedValue
    (mulModProductLayoutColumn4Call04P112FeedValue_eq_productLimb_four_of_call05P112FeedValue h_col)

theorem mulModProductLayoutColumn4Call05P112FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call05P112FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call05P112FeedValue_eq_limb2FeedValue, h_col]

theorem mulModProductLayoutColumn4Call04P112FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call04P112FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call04P112FeedValue_eq_productLimb_four_of_call05P112FeedValue
    (mulModProductLayoutColumn4Call05P112FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call05P112FeedValue
    (mulModProductLayoutColumn4Call05P112FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03P112FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_call05P112FeedValue
    (mulModProductLayoutColumn4Call05P112FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02P112FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_call03P112FeedValue
    (mulModProductLayoutColumn4Call03P112FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_call02P112FeedValue
    (mulModProductLayoutColumn4Call02P112FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_call02FeedValue
    (mulModProductLayoutColumn4Call02FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call04FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_call03FeedValue
    (mulModProductLayoutColumn4Call03FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4PrefixFeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_call04FeedValue
    (mulModProductLayoutColumn4Call04FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Limb3FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_prefixFeedValue
    (mulModProductLayoutColumn4PrefixFeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4LowFeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_limb3FeedValue
    (mulModProductLayoutColumn4Limb3FeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_lowFeedValue
    (mulModProductLayoutColumn4LowFeedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Value_eq_productLimb_four_of_limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Value a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Value_eq_productLimb_four_of_expandedValue
    (mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Limb2FeedValue_eq_productLimb_four_of_call02P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Limb2FeedValue_eq_call02P120Limb2FeedValue, h_col]

theorem mulModProductLayoutColumn4Value_eq_productLimb_four_of_call02P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Value a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Value_eq_productLimb_four_of_limb2FeedValue
    (mulModProductLayoutColumn4Limb2FeedValue_eq_productLimb_four_of_call02P120Limb2FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call02P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call02P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_limb2FeedValue
    (mulModProductLayoutColumn4Limb2FeedValue_eq_productLimb_four_of_call02P120Limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call02P120Limb2FeedValue_eq_productLimb_four_of_call03P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02P120Limb2FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call02P120Limb2FeedValue_eq_call03P120Limb2FeedValue, h_col]

theorem mulModProductLayoutColumn4Limb2FeedValue_eq_productLimb_four_of_call03P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Limb2FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Limb2FeedValue_eq_productLimb_four_of_call02P120Limb2FeedValue
    (mulModProductLayoutColumn4Call02P120Limb2FeedValue_eq_productLimb_four_of_call03P120Limb2FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call03P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call03P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call02P120Limb2FeedValue
    (mulModProductLayoutColumn4Call02P120Limb2FeedValue_eq_productLimb_four_of_call03P120Limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call03P120Limb2FeedValue_eq_productLimb_four_of_call04P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03P120Limb2FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call03P120Limb2FeedValue_eq_call04P120Limb2FeedValue, h_col]

theorem mulModProductLayoutColumn4Call02P120Limb2FeedValue_eq_productLimb_four_of_call04P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call02P120Limb2FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call02P120Limb2FeedValue_eq_productLimb_four_of_call03P120Limb2FeedValue
    (mulModProductLayoutColumn4Call03P120Limb2FeedValue_eq_productLimb_four_of_call04P120Limb2FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call04P120Limb2FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call04P120Limb2FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call03P120Limb2FeedValue
    (mulModProductLayoutColumn4Call03P120Limb2FeedValue_eq_productLimb_four_of_call04P120Limb2FeedValue h_col)

theorem mulModProductLayoutColumn4Call04P120Limb2FeedValue_eq_productLimb_four_of_call05P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call05P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call04P120Limb2FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call04P120Limb2FeedValue_eq_call05P120FeedValue, h_col]

theorem mulModProductLayoutColumn4Call03P120Limb2FeedValue_eq_productLimb_four_of_call05P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call05P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call03P120Limb2FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call03P120Limb2FeedValue_eq_productLimb_four_of_call04P120Limb2FeedValue
    (mulModProductLayoutColumn4Call04P120Limb2FeedValue_eq_productLimb_four_of_call05P120FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call05P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call05P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call04P120Limb2FeedValue
    (mulModProductLayoutColumn4Call04P120Limb2FeedValue_eq_productLimb_four_of_call05P120FeedValue h_col)

theorem mulModProductLayoutColumn4Call05P120FeedValue_eq_productLimb_four_of_call06P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call06P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call05P120FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call05P120FeedValue_eq_call06P120FeedValue, h_col]

theorem mulModProductLayoutColumn4Call04P120Limb2FeedValue_eq_productLimb_four_of_call06P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call06P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call04P120Limb2FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call04P120Limb2FeedValue_eq_productLimb_four_of_call05P120FeedValue
    (mulModProductLayoutColumn4Call05P120FeedValue_eq_productLimb_four_of_call06P120FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call06P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call06P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call05P120FeedValue
    (mulModProductLayoutColumn4Call05P120FeedValue_eq_productLimb_four_of_call06P120FeedValue h_col)

theorem mulModProductLayoutColumn4Call06P120FeedValue_eq_productLimb_four_of_call07P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call07P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call06P120FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call06P120FeedValue_eq_call07P120FeedValue, h_col]

theorem mulModProductLayoutColumn4Call05P120FeedValue_eq_productLimb_four_of_call07P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call07P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call05P120FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call05P120FeedValue_eq_productLimb_four_of_call06P120FeedValue
    (mulModProductLayoutColumn4Call06P120FeedValue_eq_productLimb_four_of_call07P120FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call07P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call07P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call06P120FeedValue
    (mulModProductLayoutColumn4Call06P120FeedValue_eq_productLimb_four_of_call07P120FeedValue h_col)

theorem mulModProductLayoutColumn4Call07P120FeedValue_eq_productLimb_four_of_call08P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call07P120FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call07P120FeedValue_eq_call08P120FeedValue, h_col]

theorem mulModProductLayoutColumn4Call06P120FeedValue_eq_productLimb_four_of_call08P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call06P120FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call06P120FeedValue_eq_productLimb_four_of_call07P120FeedValue
    (mulModProductLayoutColumn4Call07P120FeedValue_eq_productLimb_four_of_call08P120FeedValue h_col)

theorem mulModProductLayoutColumn4Call05P120FeedValue_eq_productLimb_four_of_call08P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call05P120FeedValue a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Call05P120FeedValue_eq_productLimb_four_of_call07P120FeedValue
    (mulModProductLayoutColumn4Call07P120FeedValue_eq_productLimb_four_of_call08P120FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call08P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call07P120FeedValue
    (mulModProductLayoutColumn4Call07P120FeedValue_eq_productLimb_four_of_call08P120FeedValue h_col)

theorem mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue
    (a b : EvmWord) :
    mulModProductLayoutColumn4Call08P120FeedValue a b =
      mulModProductLayoutColumn4ExpandedValue a b := by
  unfold mulModProductLayoutColumn4Call08P120FeedValue
    mulModProductLayoutColumn4ExpandedValue mulModProductLayoutColumn4PrefixCarry
  rfl

theorem mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_call08P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4 := by
  rw [← mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue, h_col]

theorem mulModProductLayoutColumn4Value_eq_productLimb_four_of_call08P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Value a b = productLimb a b 4 := by
  exact mulModProductLayoutColumn4Value_eq_productLimb_four_of_expandedValue
    (mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_call08P120FeedValue h_col)

theorem mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call08P120FeedValue_via_expanded
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = (EvmWord.mulHigh a b).getLimbN 0 := by
  exact mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_expandedValue
    (mulModProductLayoutColumn4ExpandedValue_eq_productLimb_four_of_call08P120FeedValue h_col)

theorem mulModProductLayoutColumn4Call08P120FeedValue_eq_productLimb_four_of_expandedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4ExpandedValue a b = productLimb a b 4) :
    mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4 := by
  rw [mulModProductLayoutColumn4Call08P120FeedValue_eq_expandedValue, h_col]

theorem mulModProductLayoutCall12P128_eq_productLimb_four_of_call08P120FeedValue
    {a b : EvmWord}
    (h_col : mulModProductLayoutColumn4Call08P120FeedValue a b = productLimb a b 4) :
    mulModProductLayoutCall12P128 a b = productLimb a b 4 := by
  rw [mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero_of_call08P120FeedValue h_col]
  rw [← productLimb_four_eq_mulHigh_getLimbN_zero]

end EvmAsm.Evm64
