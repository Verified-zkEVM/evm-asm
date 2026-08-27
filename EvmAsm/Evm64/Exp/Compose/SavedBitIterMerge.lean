/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge

  Branch-elimination helper for the named two-MUL saved-bit EXP iteration.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts
public import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit
public import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Merge one named canonical appended-MUL EXP iteration with externally
    supplied continuations for the loop-back and loop-exit edges. This is the
    structural induction step needed by the full 256-iteration loop proof. -/
theorem exp_two_mul_named_iter_with_continuations_spec_within
    {nCont : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nCont (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nCont (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin
      (expTwoMulNamedIterStepBound + nCont)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    cpsBranchWithin_merge_same_cr
      (by
        simpa [expTwoMulIterBit, expTwoMulIterW, expTwoMulIterAw,
          expTwoMulIterRw, expTwoMulIterCountNew] using
          (exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_appended_mul_spec_within
            e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 base hbase))
      hLoop hExit

/-- Variant of `exp_two_mul_named_iter_with_continuations_spec_within` that
    permits different bounds for the loop-back and loop-exit continuations. -/
theorem exp_two_mul_named_iter_with_continuations_max_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin
      (expTwoMulNamedIterStepBound + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    exp_two_mul_named_iter_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (cpsTripleWithin_mono_nSteps (Nat.le_max_left nLoop nExit) hLoop)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right nLoop nExit) hExit)

/-- Bounded variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. This lets the
    future 256-step induction use a closed-form loop bound while each branch
    continuation keeps its natural local bound. -/
theorem exp_two_mul_named_iter_with_continuations_bounded_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hBound :
      expTwoMulNamedIterStepBound + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin nBound
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_named_iter_with_continuations_max_spec_within
        e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 base hbase hLoop hExit)

/-- Exact named-bound variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. -/
theorem exp_two_mul_named_iter_with_continuations_exact_named_bound_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin (expTwoMulNamedIterStepBound + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  exact
    exp_two_mul_named_iter_with_continuations_max_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase

/-- Peel one named iteration from the 256-iteration body and continue with
    caller-supplied loop-back and loop-exit continuations. -/
theorem exp_two_mul_full_loop_body_peel_with_continuations_spec_within
    {nLoop nExit : Nat}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hBound : expTwoMulNamedIterStepBound + max nLoop nExit ≤
      expTwoMulFullLoopBodyBound) :
    (cpsTripleWithin nLoop (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin nExit (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase hBound

/-- Closed-form variant of
    `exp_two_mul_full_loop_body_peel_with_continuations_spec_within`,
    exposing the full 256-iteration body bound as `48384` and one iteration
    as `189` steps. -/
theorem exp_two_mul_full_loop_body_peel_with_continuations_closed_bound_spec_within
    {nLoop nExit : Nat}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hBound : 189 + max nLoop nExit ≤ 48384) :
    (cpsTripleWithin nLoop (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin nExit (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin 48384 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop hExit
  have hBoundNamed :
      expTwoMulNamedIterStepBound + max nLoop nExit ≤
        expTwoMulFullLoopBodyBound := by
    rw [expTwoMulNamedIterStepBound_eq, expTwoMulFullLoopBodyBound_eq]
    exact hBound
  rw [← expTwoMulFullLoopBodyBound_eq]
  exact
    exp_two_mul_full_loop_body_peel_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hBoundNamed hLoop hExit

/-- Peel one named iteration from an `(iterations + 1)`-iteration body when
    both branch continuations are packaged under the `iterations`-iteration
    tail bound. -/
theorem exp_two_mul_iterations_body_peel_with_continuations_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin (expTwoMulIterationsBodyBound (iterations + 1))
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (expTwoMulNamedIterStepBound_add_max_iterationsBodyBound_le_succ
        iterations)

/-- Closed-form variant of
    `exp_two_mul_iterations_body_peel_with_continuations_spec_within`,
    exposing each saved-bit two-MUL iteration as `189` steps. -/
theorem exp_two_mul_iterations_body_peel_with_continuations_closed_bound_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin (iterations * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin (iterations * 189)
      (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin ((iterations + 1) * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop hExit
  rw [← expTwoMulIterationsBodyBound_eq iterations] at hLoop hExit
  rw [← expTwoMulIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_iterations_body_peel_with_continuations_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hLoop hExit

/-- Peel one named iteration from an `(iterations + 1)`-iteration body when
    the loop-back edge is packaged under the `iterations`-iteration tail
    bound and the exit edge is discharged by a zero-step assertion bridge. -/
theorem exp_two_mul_iterations_body_peel_with_exit_imp_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hExit :
      ∀ hp,
        expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin (expTwoMulIterationsBodyBound (iterations + 1))
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (expTwoMulNamedIterStepBound_add_max_iterationsBodyBound_zero_le_succ
        iterations)
      hLoop
      (cpsTripleWithin_extend_code
        (hmono := by
          intro a i h
          cases h)
        (cpsTripleWithin_refl hExit))

/-- Closed-form variant of
    `exp_two_mul_iterations_body_peel_with_exit_imp_spec_within`. -/
theorem exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hExit :
      ∀ hp,
        expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (iterations * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin ((iterations + 1) * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  rw [← expTwoMulIterationsBodyBound_eq iterations] at hLoop
  rw [← expTwoMulIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_iterations_body_peel_with_exit_imp_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hExit hLoop

/-- Convert the two concrete exit-branch postconditions into the unified
    iteration-exit postcondition expected by the bounded peel helper. -/
theorem exp_two_mul_iter_exit_post_cases_to_loop_exit_pre
    (e iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
      iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    ∀ hp,
      expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) hp →
      expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond hp := by
  intro hp hExit
  rw [expTwoMulIterExitPost_unfold] at hExit
  rcases hExit with hCond | hSkip
  · exact hCondExit hp hCond
  · exact hSkipExit hp hSkip

/-- Peel one named iteration from an `(iterations + 1)`-iteration body, reducing
    the zero-step exit bridge to the two concrete branch-postcondition cases. -/
theorem exp_two_mul_iterations_body_peel_with_exit_cases_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin (expTwoMulIterationsBodyBound (iterations + 1))
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_iterations_body_peel_with_exit_imp_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase
      (exp_two_mul_iter_exit_post_cases_to_loop_exit_pre
        e iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        iterCountFinal tOld out0 out1 out2 out3 base baseWord rest exitCond
        hCondExit hSkipExit)

/-- Closed-form variant of
    `exp_two_mul_iterations_body_peel_with_exit_cases_spec_within`. -/
theorem exp_two_mul_iterations_body_peel_with_exit_cases_closed_bound_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (iterations * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin ((iterations + 1) * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  rw [← expTwoMulIterationsBodyBound_eq iterations] at hLoop
  rw [← expTwoMulIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_iterations_body_peel_with_exit_cases_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hCondExit hSkipExit hLoop

/-- Peel one named iteration from the 256-iteration body when both branch
    continuations are already packaged under the named 255-iteration tail
    bound. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_continuations_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_full_loop_body_peel_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase
      expTwoMulNamedIterStepBound_add_max_fullTail_le_full

/-- Closed-form variant of
    `exp_two_mul_full_loop_body_peel_tail_with_continuations_spec_within`,
    using the normalized 255-iteration tail bound `48195` and full-body bound
    `48384`. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_continuations_closed_bound_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin 48195 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin 48195 (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin 48384 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop hExit
  have hLoopNamed :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyTailBound_eq]
    exact hLoop
  have hExitNamed :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 264) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyTailBound_eq]
    exact hExit
  rw [← expTwoMulFullLoopBodyBound_eq]
  exact
    exp_two_mul_full_loop_body_peel_tail_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hLoopNamed hExitNamed

/-- Peel one named iteration from the 256-iteration body with the loop-back
    continuation packaged under the named 255-iteration tail bound, reducing
    the zero-step exit bridge to the two concrete branch-postcondition cases. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_exit_cases_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  rw [expTwoMulFullLoopBodyBound_eq_tail_succ]
  exact
    exp_two_mul_iterations_body_peel_with_exit_cases_spec_within
      255
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hCondExit hSkipExit hLoop

/-- Closed-form variant of
    `exp_two_mul_full_loop_body_peel_tail_with_exit_cases_spec_within`. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_exit_cases_closed_bound_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin 48195 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin 48384 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  have hLoopNamed :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyTailBound_eq]
    exact hLoop
  rw [← expTwoMulFullLoopBodyBound_eq]
  exact
    exp_two_mul_full_loop_body_peel_tail_with_exit_cases_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hCondExit hSkipExit hLoopNamed

/-- Closed-form bound variant of
    `exp_two_mul_named_iter_with_continuations_bounded_spec_within`, using the
    normalized one-iteration cost `189`. -/
theorem exp_two_mul_named_iter_with_continuations_closed_bound_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hBound : 189 + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin nBound
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (by simpa [expTwoMulNamedIterStepBound_eq] using hBound)
      hLoop hExit

/-- Exact closed-form bound variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. -/
theorem exp_two_mul_named_iter_with_continuations_exact_closed_bound_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin (189 + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  exact
    exp_two_mul_named_iter_with_continuations_closed_bound_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase (by rfl)

/-- `expTwoMulIterLoopPost 0 ...` is unsatisfiable: it embeds `⌜0 ≠ 0⌝`
    (loop-back guard), so no PartialState can satisfy it. -/
theorem expTwoMulIterLoopPost_zero_count_false
    {bit sp evmSp base a0 a1 a2 a3 : Word}
    {squareW rw : EvmWord} {ps : PartialState} :
    ¬ expTwoMulIterLoopPost 0 bit sp evmSp base a0 a1 a2 a3 squareW rw ps := by
  rw [expTwoMulIterLoopPost_unfold]
  rintro (hCond | hSkip)
  · rw [expTwoMulIterCondPost_unfold] at hCond
    obtain ⟨_, _, _, _, h_tcr, _⟩ := hCond
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tcr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 (by decide)
  · rw [expTwoMulIterSkipPost_unfold] at hSkip
    obtain ⟨_, _, _, _, h_tsr, _⟩ := hSkip
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tsr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 (by decide)

/-- 0-step body spec from `expTwoMulIterLoopPost 0 ...` to anything is
    vacuously true: the precondition is unsatisfiable. -/
theorem exp_loop_body_zero_step_vacuous
    {bit sp evmSp base a0 a1 a2 a3 : Word}
    {squareW rw : EvmWord}
    {Q : Assertion} {base_ : Word}
    {code : CodeReq} :
    cpsTripleWithin 0 (base_ + 28) (base_ + 264) code
      (expTwoMulIterLoopPost 0 bit sp evmSp base a0 a1 a2 a3 squareW rw)
      Q := by
  intro R _ s _ hPR _
  exfalso
  have hP := holdsFor_sepConj_elim_left hPR
  obtain ⟨_, _, h_looppost⟩ := hP
  exact expTwoMulIterLoopPost_zero_count_false h_looppost

/-- `expTwoMulIterExitPost k ...` is unsatisfiable when `k ≠ 0`: it embeds
    `⌜k = 0⌝` (loop-exit guard), so no PartialState can satisfy it when `k ≠ 0`. -/
theorem expTwoMulIterExitPost_nonzero_count_false
    {iterCountNew : Word} (h : iterCountNew ≠ 0)
    {bit sp evmSp base a0 a1 a2 a3 : Word}
    {squareW rw : EvmWord} {ps : PartialState} :
    ¬ expTwoMulIterExitPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw ps := by
  rw [expTwoMulIterExitPost_unfold]
  rintro (hCond | hSkip)
  · rw [expTwoMulIterCondPost_unfold] at hCond
    obtain ⟨_, _, _, _, h_tcr, _⟩ := hCond
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tcr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 h
  · rw [expTwoMulIterSkipPost_unfold] at hSkip
    obtain ⟨_, _, _, _, h_tsr, _⟩ := hSkip
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tsr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 h

/-- When `iterCountNew ≠ 0`, the exit post is unsatisfiable, so any implication
    `exitPost → Q` holds vacuously. This is the exit bridge for all non-final
    loop iterations in the 256-step induction. -/
theorem exp_loop_exit_vacuous_bridge
    {iterCountNew : Word} (h : iterCountNew ≠ 0)
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squareW rw : EvmWord}
    {Q : PartialState → Prop} :
    ∀ ps, expTwoMulIterExitPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw ps → Q ps :=
  fun _ hExit => absurd hExit (expTwoMulIterExitPost_nonzero_count_false h)

/-- Abstract n-iteration loop body spec: given any exit bridge for the current
    step's exit condition and any n-step loop-back continuation, the (n+1)-step
    body spec holds from `expTwoMulIterPre`.

    This is a thin wrapper around
    `exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within`
    that makes the "inductive step" shape explicit. -/
theorem exp_loop_body_succ_step
    (n : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word) (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hExit : ∀ ps,
        expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) ps →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond ps)
    (hLoop : cpsTripleWithin (n * 189) (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond)) :
    cpsTripleWithin ((n + 1) * 189) (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) :=
  exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within
    n e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
    e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
    base baseWord rest exitCond hbase hExit hLoop


end EvmAsm.Evm64.Exp.Compose
