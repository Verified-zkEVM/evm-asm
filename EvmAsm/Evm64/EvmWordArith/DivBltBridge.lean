/-
  EvmAsm.Evm64.EvmWordArith.DivBltBridge

  BLT-path analog of the N{2,3}Max bridges in `DivN{2,3}MaxOverestimate`.

  The BLT carry-2-nz predicates
  (`loopBodyN{2,3}CallAddbackCarry2NzV4`) expand to
  `isAddbackCarry2Nz (divKTrialCallV4QHat uHi uLo vTop) …` — i.e., the same
  shape as the generic double-addback progress predicate, but with the v4
  call-trial quotient `divKTrialCallV4QHat` in place of the saturated
  `signExtend12 4095`.

  This file provides the BLT analog `isAddbackCarry2Nz_blt_of_overestimate`
  that bridges the predicate to the generic
  `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero`.

  Hypotheses:
    1. `hbnz`: divisor has a nonzero limb.
    2. `hq_over`: a +2 overestimate on the v4 call-trial vs the true
       val256-level local quotient.  The discharge of this is the
       Knuth-A v4 bound (bead `7.1.4.1` and its descendants) composed
       with the val256-level normalisation.
    3. `MulsubBltC3OneOfCarryZero`: the c3 = 1 when first-addback carry = 0
       reachability invariant for the v4 call-trial.

  Symmetric to the MAX side: with both invariants discharged, all twelve
  carry-branch bead leaves (six MAX + six BLT) close at once.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
public import EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Generic BLT-path bridge: instantiates
    `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` at the v4
    call-trial `divKTrialCallV4QHat uHi uLo vTop`.

    The hypotheses `hbnz`, `hq_over`, and `hc3` mirror the structure of the
    MAX-path bridge but specialised to the v4 trial.  The result has the
    same shape as the MAX bridge so the same downstream consumers compose. -/
theorem isAddbackCarry2Nz_blt_of_overestimate_c3_one_of_carry_zero
    (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop_w : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hc3 : MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3) :
    isAddbackCarry2Nz (divKTrialCallV4QHat uHi uLo vTop)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop_w := by
  apply isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
  · exact hbnz
  · exact hq_over
  · -- MulsubBltC3OneOfCarryZero unfolds to exactly the third hypothesis form.
    exact hc3

end EvmAsm.Evm64
