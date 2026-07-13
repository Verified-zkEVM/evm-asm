/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Quotient

  The v5 n=1 **shift=0** quotient word and its per-limb extraction.  On the
  shift=0 branch the loop runs at `v = (b0, 0, 0, 0)`, `u0 = a3`,
  `u1 = u2 = u3 = uTop = 0`, `u0_orig_{2,1,0} = a2, a1, a0` (the copy-AU layout),
  producing the four quotient digits
    `(iterN1Call_v5 …).1` (j=3), `(fullN1S2 …).1` (j=2),
    `(fullN1S1 …).1` (j=1), `(fullN1S0 …).1` (j=0).
  The DIV epilogue writes these to the output slots in little-endian order, so
  the quotient word is `fromLimbs` of `(S0.1, S1.1, S2.1, R3.1)`.

  Shift=0 counterpart of `fullDivN1QuotientWordV5` + `N1V5QuotientLimbs`; the
  per-limb facts feed the (forthcoming) shift=0 quotient-correctness proof.
  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5Quotient
import EvmAsm.Evm64.DivMod.LoopIterN1.N1V5IterChainShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- The v5 n=1 shift=0 quotient word: `fromLimbs` of the four shift=0 loop
    digits (little-endian), matching the DIV-epilogue output order. -/
def fullDivN1QuotientWordShift0V5 (a0 a1 a2 a3 b0 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1
    | 1 => (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1
    | 2 => (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1
    | 3 => (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1)

theorem fullDivN1QuotientWordShift0V5_getLimbN0 (a0 a1 a2 a3 b0 : Word) :
    (fullDivN1QuotientWordShift0V5 a0 a1 a2 a3 b0).getLimbN 0
    = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1 := by
  unfold fullDivN1QuotientWordShift0V5
  rw [← getLimb_as_getLimbN_0, getLimb_fromLimbs_0]

theorem fullDivN1QuotientWordShift0V5_getLimbN1 (a0 a1 a2 a3 b0 : Word) :
    (fullDivN1QuotientWordShift0V5 a0 a1 a2 a3 b0).getLimbN 1
    = (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1 := by
  unfold fullDivN1QuotientWordShift0V5
  rw [← getLimb_as_getLimbN_1, getLimb_fromLimbs_1]

theorem fullDivN1QuotientWordShift0V5_getLimbN2 (a0 a1 a2 a3 b0 : Word) :
    (fullDivN1QuotientWordShift0V5 a0 a1 a2 a3 b0).getLimbN 2
    = (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1 := by
  unfold fullDivN1QuotientWordShift0V5
  rw [← getLimb_as_getLimbN_2, getLimb_fromLimbs_2]

theorem fullDivN1QuotientWordShift0V5_getLimbN3 (a0 a1 a2 a3 b0 : Word) :
    (fullDivN1QuotientWordShift0V5 a0 a1 a2 a3 b0).getLimbN 3
    = (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1 := by
  unfold fullDivN1QuotientWordShift0V5
  rw [← getLimb_as_getLimbN_3, getLimb_fromLimbs_3]

end EvmAsm.Evm64
