/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostStateBridge

  State-invariant wrappers around fixed iteration case-post peels.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCountBridge
public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterState

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- State-invariant non-final arbitrary-iteration peel.  This is the form the
    Nat induction uses for `k < 255`: the bundled state invariant supplies the
    loop-count fact required by the count-aware peel. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_nonfinal_of_state_spec_within
    (iterations k : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    {baseWord exponentWord : EvmWord}
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hk : k < 255)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e c6 ptr nextLimb evmSp r0 r1 r2 r3) :
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_iterations_body_peel_case_nonfinal_of_count_spec_within
    iterations k
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase hk hState.2.2.2

/-- State-invariant final arbitrary-iteration peel. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_final_of_state_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    {baseWord exponentWord : EvmWord}
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 255
        iterCount e c6 ptr nextLimb evmSp r0 r1 r2 r3)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_iterations_body_peel_case_final_of_count_spec_within
    iterations
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase hState.2.2.2 hExit

/-- Closed-form state-invariant non-final arbitrary-iteration peel. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_nonfinal_of_state_closed_bound_spec_within
    (iterations k : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    {baseWord exponentWord : EvmWord}
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hk : k < 255)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e c6 ptr nextLimb evmSp r0 r1 r2 r3) :
    (cpsTripleWithin (iterations * 193)
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin ((iterations + 1) * 193)
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_iterations_body_peel_case_nonfinal_of_count_closed_bound_spec_within
    iterations k
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase hk hState.2.2.2

/-- Closed-form state-invariant final arbitrary-iteration peel. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_final_of_state_closed_bound_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    {baseWord exponentWord : EvmWord}
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 255
        iterCount e c6 ptr nextLimb evmSp r0 r1 r2 r3)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin ((iterations + 1) * 193)
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_iterations_body_peel_case_final_of_count_closed_bound_spec_within
    iterations
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase hState.2.2.2 hExit

end EvmAsm.Evm64.Exp.Compose
