/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCountBridge

  Count-invariant wrappers around fixed iteration case-post peels.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge
public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCount

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Count-invariant non-final arbitrary-iteration peel.  This is the form the
    Nat induction uses for `k < 255`: the loop counter invariant supplies the
    nonzero decremented-count fact. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_nonfinal_of_count_spec_within
    (iterations k : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount) :
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
  exp_two_mul_fixed_iterations_body_peel_case_nonfinal_spec_within
    iterations
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)

/-- Count-invariant final arbitrary-iteration peel.  This is the form the Nat
    induction uses at `k = 255`: the loop counter invariant supplies the zero
    decremented-count fact. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_final_of_count_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hCount : expTwoMulFixedIterCountInvariant 255 iterCount)
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
  exp_two_mul_fixed_iterations_body_peel_case_final_spec_within
    iterations
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (expTwoMulFixedIterCountInvariant_succ_eq_zero hCount)
    hExit

/-- Closed-form count-invariant non-final arbitrary-iteration peel. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_nonfinal_of_count_closed_bound_spec_within
    (iterations k : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount) :
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
  exp_two_mul_fixed_iterations_body_peel_case_nonfinal_closed_bound_spec_within
    iterations
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)

/-- Closed-form count-invariant final arbitrary-iteration peel. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_final_of_count_closed_bound_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hCount : expTwoMulFixedIterCountInvariant 255 iterCount)
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
  exp_two_mul_fixed_iterations_body_peel_case_final_closed_bound_spec_within
    iterations
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (expTwoMulFixedIterCountInvariant_succ_eq_zero hCount)
    hExit

end EvmAsm.Evm64.Exp.Compose
