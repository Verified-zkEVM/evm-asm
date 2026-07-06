/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedMergedFramedStep

  Framed variant of the merged fixed-x19 EXP per-iteration step.  The exponent
  is read-only across the loop body, so an arbitrary pcFree frame `F` (used by
  the residual induction to carry the not-yet-loaded exponent limb cells) can be
  threaded through one iteration: it rides untouched from the iteration pre to
  both the loop-back and loop-exit posts.  This is the enabler that makes the
  reload-boundary cell available to the loop-back continuation (where the
  proven reshuffle lemmas can re-partition it), discharging the old pure
  `MergedReloadReshuffle` hypothesis.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Merge one fixed x19 canonical appended-MUL EXP iteration with externally
    supplied continuations, with a pcFree frame `F` threaded through the body
    (read-only exponent), so the continuations see `… ** F`. -/
theorem exp_two_mul_fixed_iter_merged_with_continuations_framed_spec_within
    {nCont : Nat} {exit_ : Word} {R F : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree) :
    (cpsTripleWithin nCont (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin nCont (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin
      (expTwoMulFixedReloadIterStepBound + nCont)
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  have hbr :=
    exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
  have hbrF := cpsNBranchWithin_frameR hF hbr
  refine cpsNBranchWithin_merge hbrF ?_
  intro ex hmem
  simp only [List.map] at hmem
  cases hmem with
  | head => exact hLoop
  | tail _ htail =>
      cases htail with
      | head => exact hExit
      | tail _ hnil => cases hnil

/-- Bounded framed merge (max of loop/exit bounds). -/
theorem exp_two_mul_fixed_iter_merged_with_continuations_bounded_framed_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R F : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hBound :
      expTwoMulFixedReloadIterStepBound + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin nExit (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin nBound
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_fixed_iter_merged_with_continuations_framed_spec_within
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase hF
        (cpsTripleWithin_mono_nSteps (Nat.le_max_left nLoop nExit) hLoop)
        (cpsTripleWithin_mono_nSteps (Nat.le_max_right nLoop nExit) hExit))

/-- Framed peel of one fixed x19 merged iteration (closed `193`-per-iteration
    bound). -/
theorem exp_two_mul_fixed_iterations_body_peel_with_continuations_closed_bound_framed_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree) :
    (cpsTripleWithin (iterations * 193)
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin (iterations * 193)
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin ((iterations + 1) * 193)
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  rw [← expTwoMulFixedIterationsBodyBound_eq iterations] at hLoop hExit
  rw [← expTwoMulFixedIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_fixed_iter_merged_with_continuations_bounded_framed_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase hF
      (expTwoMulFixedReloadIterStepBound_add_max_fixedIterationsBodyBound_le_succ
        iterations)
      hLoop hExit

/-- Framed merged-loop induction step: thread a pcFree frame `F` (the exponent
    residual) through one iteration.  The loop-back continuation receives the
    `ptr-8` next-limb cell carried in `F`. -/
theorem exp_fixed_loop_body_succ_step_framed
    (n : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hExit :
      ∀ ps,
        (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F) ps →
        R ps)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R :=
  exp_two_mul_fixed_iterations_body_peel_with_continuations_closed_bound_framed_spec_within
    n
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base (base + 296) R F hbase hF hLoop
    (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
      (cpsTripleWithin_extend_code
        (hmono := by
          intro a i h
          cases h)
        (cpsTripleWithin_refl hExit)))

/-- Framed final merged-loop induction step (the loop-back edge is vacuous). -/
theorem exp_fixed_loop_body_final_succ_step_framed
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F) ps →
        R ps) :
    cpsTripleWithin ((0 + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R :=
  exp_fixed_loop_body_succ_step_framed
    0 e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
    base R F hbase hF hExit
    (by
      intro Rf _ s _ hPR _
      exfalso
      have hP := holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR)
      obtain ⟨_, _, h_looppost⟩ := hP
      exact expTwoMulFixedIterMergedLoopPost_zero_count_false hzero h_looppost)


/-- Body-only-code-req twins of the framed merged-step chain (path A, bug fjivz). -/
theorem exp_two_mul_fixed_iter_merged_with_continuations_framed_spec_within_bodyonly
    {nCont : Nat} {exit_ : Word} {R F : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree) :
    (cpsTripleWithin nCont (base + 44) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin nCont (base + 296) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin
      (expTwoMulFixedReloadIterStepBound + nCont)
      (base + 44)
      exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  have hbr :=
    exp_msb_bit_test_fixed_full_iter_merged_named_exits_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
  have hbrF := cpsNBranchWithin_frameR hF hbr
  refine cpsNBranchWithin_merge hbrF ?_
  intro ex hmem
  simp only [List.map] at hmem
  cases hmem with
  | head => exact hLoop
  | tail _ htail =>
      cases htail with
      | head => exact hExit
      | tail _ hnil => cases hnil

/-- Bounded framed merge (max of loop/exit bounds). -/
theorem exp_two_mul_fixed_iter_merged_with_continuations_bounded_framed_spec_within_bodyonly
    {nLoop nExit nBound : Nat} {exit_ : Word} {R F : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hBound :
      expTwoMulFixedReloadIterStepBound + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 44) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin nExit (base + 296) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin nBound
      (base + 44)
      exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_fixed_iter_merged_with_continuations_framed_spec_within_bodyonly
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase hF
        (cpsTripleWithin_mono_nSteps (Nat.le_max_left nLoop nExit) hLoop)
        (cpsTripleWithin_mono_nSteps (Nat.le_max_right nLoop nExit) hExit))

/-- Framed peel of one fixed x19 merged iteration (closed `193`-per-iteration
    bound). -/
theorem exp_two_mul_fixed_iterations_body_peel_with_continuations_closed_bound_framed_spec_within_bodyonly
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree) :
    (cpsTripleWithin (iterations * 193)
      (base + 44) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin (iterations * 193)
      (base + 296) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin ((iterations + 1) * 193)
      (base + 44)
      exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  rw [← expTwoMulFixedIterationsBodyBound_eq iterations] at hLoop hExit
  rw [← expTwoMulFixedIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_fixed_iter_merged_with_continuations_bounded_framed_spec_within_bodyonly
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase hF
      (expTwoMulFixedReloadIterStepBound_add_max_fixedIterationsBodyBound_le_succ
        iterations)
      hLoop hExit

/-- Framed merged-loop induction step: thread a pcFree frame `F` (the exponent
    residual) through one iteration.  The loop-back continuation receives the
    `ptr-8` next-limb cell carried in `F`. -/
theorem exp_fixed_loop_body_succ_step_framed_bodyonly
    (n : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hExit :
      ∀ ps,
        (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F) ps →
        R ps)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R :=
  exp_two_mul_fixed_iterations_body_peel_with_continuations_closed_bound_framed_spec_within_bodyonly
    n
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base (base + 296) R F hbase hF hLoop
    (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
      (cpsTripleWithin_extend_code
        (hmono := by
          intro a i h
          cases h)
        (cpsTripleWithin_refl hExit)))

/-- Framed final merged-loop induction step (the loop-back edge is vacuous). -/
theorem exp_fixed_loop_body_final_succ_step_framed_bodyonly
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F) ps →
        R ps) :
    cpsTripleWithin ((0 + 1) * 193) (base + 44) (base + 296)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R :=
  exp_fixed_loop_body_succ_step_framed_bodyonly
    0 e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
    base R F hbase hF hExit
    (by
      intro Rf _ s _ hPR _
      exfalso
      have hP := holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR)
      obtain ⟨_, _, h_looppost⟩ := hP
      exact expTwoMulFixedIterMergedLoopPost_zero_count_false hzero h_looppost)

end EvmAsm.Evm64.Exp.Compose
