/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5DigitLoopForm

  Goal-side rewrite lemmas connecting the irreducible n=1 digit/remainder aliases
  (`n1QuotDigit*V5`, `n1RemLimb*V5`) to the `fullN1S{0,1,2}` / `iterN1Call_v5`
  iteration-chain projections that appear (after peeling the post structure) in
  `loopN1UnifiedPostV5`.  The loop-post → denorm-epilogue bridge cannot run any
  whole-assertion tactic over the deep cell values; instead it rewrites the
  (shallow, aliased) denorm-pre goal cell-by-cell into the chain form via these
  lemmas, then matches the peeled post cells.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Digits
import EvmAsm.Evm64.DivMod.LoopIterN1.N1V5IterChainShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- q3 alias = the j=3 chain head `(iterN1Call_v5 …).1`. -/
theorem n1QuotDigit3V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1QuotDigit3V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).1 := by
  rw [n1QuotDigit3V5_eq, fullDivN1R3V5_eq_iterN1Call_v5]

/-- q2 alias = `(fullN1S2 …).1`. -/
theorem n1QuotDigit2V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1QuotDigit2V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (fullN1S2 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).1 := by
  rw [n1QuotDigit2V5_eq, ← fullN1S2_eq_fullDivN1R2V5]

/-- q1 alias = `(fullN1S1 …).1`. -/
theorem n1QuotDigit1V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1QuotDigit1V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (fullN1S1 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1).1 := by
  rw [n1QuotDigit1V5_eq, ← fullN1S1_eq_fullDivN1R1V5]

/-- q0 alias = `(fullN1S0 …).1`. -/
theorem n1QuotDigit0V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1QuotDigit0V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (fullN1S0 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1).1 := by
  rw [n1QuotDigit0V5_eq, ← fullN1S0_eq_fullDivN1R0V5]

/-- The four normalized remainder limbs as `fullN1S0` projections. -/
theorem n1RemLimb0V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1RemLimb0V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (fullN1S0 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1).2.1 := by
  rw [n1RemLimb0V5_eq, ← fullN1S0_eq_fullDivN1R0V5]

theorem n1RemLimb1V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1RemLimb1V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (fullN1S0 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1).2.2.1 := by
  rw [n1RemLimb1V5_eq, ← fullN1S0_eq_fullDivN1R0V5]

theorem n1RemLimb2V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1RemLimb2V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (fullN1S0 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1).2.2.2.1 := by
  rw [n1RemLimb2V5_eq, ← fullN1S0_eq_fullDivN1R0V5]

theorem n1RemLimb3V5_loopform (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    n1RemLimb3V5 a0 a1 a2 a3 b0 b1 b2 b3
    = (fullN1S0 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1).2.2.2.2.1 := by
  rw [n1RemLimb3V5_eq, ← fullN1S0_eq_fullDivN1R0V5]

end EvmAsm.Evm64
