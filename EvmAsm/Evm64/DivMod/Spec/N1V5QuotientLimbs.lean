/-
  EvmAsm.Evm64.DivMod.Spec.N1V5QuotientLimbs

  Per-limb extraction of the v5 n=1 quotient word: each limb of
  `fullDivN1QuotientWordV5` is the corresponding schoolbook digit
  `(fullDivN1R{0,1,2,3}V5 …).1`.  Combined with the merged quotient theorem
  `fullDivN1QuotientWordV5_eq_div_of_shape` (which equates the word to
  `EvmWord.div`), these give the `getLimbN` facts the n=1 stack-level post
  bridge needs.  Pure `getLimb_fromLimbs` extraction — no shape hypotheses.
  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1V5Quotient

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

theorem fullDivN1QuotientWordV5_getLimbN0 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN1QuotientWordV5 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 0
    = (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold fullDivN1QuotientWordV5
  rw [← getLimb_as_getLimbN_0, getLimb_fromLimbs_0]

theorem fullDivN1QuotientWordV5_getLimbN1 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN1QuotientWordV5 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 1
    = (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold fullDivN1QuotientWordV5
  rw [← getLimb_as_getLimbN_1, getLimb_fromLimbs_1]

theorem fullDivN1QuotientWordV5_getLimbN2 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN1QuotientWordV5 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 2
    = (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold fullDivN1QuotientWordV5
  rw [← getLimb_as_getLimbN_2, getLimb_fromLimbs_2]

theorem fullDivN1QuotientWordV5_getLimbN3 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN1QuotientWordV5 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 3
    = (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  unfold fullDivN1QuotientWordV5
  rw [← getLimb_as_getLimbN_3, getLimb_fromLimbs_3]

end EvmAsm.Evm64
