/-
  EvmAsm.Evm64.DivMod.Spec.N1V5QuotientWordLane

  EvmWord-level v5 n=1 quotient correctness for an arbitrary dividend/divisor
  given their limbs: `fullDivN1QuotientWordV5 a0..b3 = EvmWord.div a b` when
  `a`/`b` decompose to those limbs.  Bridges the limb-indexed quotient theorem
  `fullDivN1QuotientWordV5_eq_div_of_shape` to the lane's `a b : EvmWord` (via the
  `fromLimbs ∘ getLimb = id` reconstruction), discharging the `hdivWord` hypothesis
  the v4 lane left open.  Per-limb corollaries feed the stack-level post bridge.
  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1V5Quotient
public import EvmAsm.Evm64.DivMod.Spec.N1V5QuotientLimbs

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

theorem fullDivN1QuotientWordV5_eq_div_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    fullDivN1QuotientWordV5 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  rw [fullDivN1QuotientWordV5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hshift_nz]
  congr 1
  · conv_rhs => rw [← fromLimbs_getLimb a]
    congr 1
    funext i
    fin_cases i <;> simp only [getLimb_eq_getLimbN] <;>
      first
        | (rw [ha0]) | (rw [ha1]) | (rw [ha2]) | (rw [ha3])
  · conv_rhs => rw [← fromLimbs_getLimb b]
    congr 1
    funext i
    fin_cases i <;> simp only [getLimb_eq_getLimbN] <;>
      first
        | (rw [hb0]) | (rw [hb1]) | (rw [hb2]) | (rw [hb3])

/-- Per-limb form: each limb of `EvmWord.div a b` equals the corresponding v5
    schoolbook digit, for the lane's `a b`. -/
theorem div_getLimbN0_eq_digit_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  have hw := fullDivN1QuotientWordV5_eq_div_lane a b a0 a1 a2 a3 b0 b1 b2 b3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb1z hb2z hb3z hshift_nz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hw]
  · exact fullDivN1QuotientWordV5_getLimbN0 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN1QuotientWordV5_getLimbN1 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN1QuotientWordV5_getLimbN2 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN1QuotientWordV5_getLimbN3 a0 a1 a2 a3 b0 b1 b2 b3

end EvmAsm.Evm64
