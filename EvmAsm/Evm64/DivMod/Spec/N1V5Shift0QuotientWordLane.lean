/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0QuotientWordLane

  Lane-level shift=0 quotient facts: for the lane's `a b : EvmWord`, each limb of
  `EvmWord.div a b` equals the corresponding shift=0 schoolbook digit.  Shift=0
  counterpart of `N1V5QuotientWordLane` (`fullDivN1QuotientWordV5_eq_div_lane` /
  `div_getLimbN0_eq_digit_lane`); feeds the shift=0 n=1 lane post bridge.
  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0QuotientCorrect

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- The shift=0 quotient word equals `EvmWord.div a b` for the lane's `a b`. -/
theorem fullDivN1QuotientWordShift0V5_eq_div_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    fullDivN1QuotientWordShift0V5 a0 a1 a2 a3 b0 = EvmWord.div a b := by
  rw [fullDivN1QuotientWordShift0V5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
        hbnz hb1z hb2z hb3z hclz]
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

/-- Per-limb form: each limb of `EvmWord.div a b` equals the corresponding
    shift=0 schoolbook digit, for the lane's `a b`. -/
theorem div_getLimbN_eq_digit_shift0 (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    (EvmWord.div a b).getLimbN 0 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1 ∧
    (EvmWord.div a b).getLimbN 3 = (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1 := by
  have hw := fullDivN1QuotientWordShift0V5_eq_div_lane a b a0 a1 a2 a3 b0 b1 b2 b3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb1z hb2z hb3z hclz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hw]
  · exact fullDivN1QuotientWordShift0V5_getLimbN0 a0 a1 a2 a3 b0
  · exact fullDivN1QuotientWordShift0V5_getLimbN1 a0 a1 a2 a3 b0
  · exact fullDivN1QuotientWordShift0V5_getLimbN2 a0 a1 a2 a3 b0
  · exact fullDivN1QuotientWordShift0V5_getLimbN3 a0 a1 a2 a3 b0

end EvmAsm.Evm64
