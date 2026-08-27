/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop

  Generic composition scaffold for the two-MUL saved-bit EXP boundary:
  prologue/pointer-advance, an externally supplied loop proof, and
  pointer-restore/epilogue.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit
public import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds
public import EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge
public import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Compose the named prologue boundary, any loop proof over the named
    loop-entry/loop-exit surface, and the named epilogue boundary. The future
    256-iteration proof can instantiate `hLoop`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin (expTwoMulBoundaryLoopBound nSteps) base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBoundary :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base
  have hPrefix :=
    cpsTripleWithin_seq_same_cr hBoundary hLoop
  exact
    cpsTripleWithin_seq_same_cr hPrefix
      (exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_exit_spec_within
        sp evmSp iterCountNew tOld r0 r1 r2 r3 baseWord rest exitCond base)

/-- Bounded variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_spec_within`. This packages
    the prologue/loop/epilogue boundary into a caller-chosen closed-form bound
    for the later full-loop theorem. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : expTwoMulBoundaryLoopBound nSteps ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_boundary_loop_epilogue_of_loop_spec_within
        sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
        r0 r1 r2 r3 baseWord exponentWord rest exitCond base hLoop)

/-- Closed-form bound variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within`, using
    the normalized boundary cost `nSteps + 17`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_closed_bound_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps + 17 ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      (by simpa [expTwoMulBoundaryLoopBound_eq] using hBound)
      hLoop

/-- Exact closed-form bound variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_spec_within`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_exact_closed_bound_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin (nSteps + 17) base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_closed_bound_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base (by rfl) hLoop

/-- Specialization of the named boundary composition to the 256-iteration
    saved-bit two-MUL loop body bound. This is the outer shell expected by the
    eventual full-loop proof once the loop proof itself is available. -/
theorem exp_two_mul_full_loop_boundary_of_body_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      (by rfl)
      hLoop

/-- Boundary-level wrapper for the first peeled full-loop body iteration. It
    leaves the loop-entry-to-iteration-pre bridge and the two concrete exit
    branch bridges as caller-supplied assertion implications. -/
theorem exp_two_mul_full_loop_boundary_of_entry_tail_exit_cases_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      e iterCount r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : base &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        expTwoMulIterPre e iterCount v18 sp evmSp tOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 hp)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hEntryTriple :
      cpsTripleWithin 0 (base + 28) (base + 28)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulIterPre e iterCount v18 sp evmSp tOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3) :=
    cpsTripleWithin_extend_code
      (hmono := by
        intro a i h
        cases h)
      (cpsTripleWithin_refl hEntry)
  have hBody :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterPre e iterCount v18 sp evmSp tOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond) :=
    exp_two_mul_full_loop_body_peel_tail_with_exit_cases_spec_within
      e iterCount v18 sp evmSp tOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      iterCountNew tOld r0 r1 r2 r3
      base baseWord rest exitCond hbase hCondExit hSkipExit hTail
  have hLoop :
      cpsTripleWithin (0 + expTwoMulFullLoopBodyBound)
        (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond) :=
    cpsTripleWithin_seq_same_cr hEntryTriple hBody
  exact
    exp_two_mul_full_loop_boundary_of_body_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      (by simpa using hLoop)

/-- Closed-form variant of
    `exp_two_mul_full_loop_boundary_of_entry_tail_exit_cases_spec_within`.
    This accepts a concrete `48195`-step tail continuation and packages the
    boundary at the concrete `48401`-step bound. -/
theorem exp_two_mul_full_loop_boundary_of_entry_tail_exit_cases_closed_bound_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      e iterCount r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : base &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        expTwoMulIterPre e iterCount v18 sp evmSp tOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 hp)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin 48195 (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond)) :
    cpsTripleWithin 48401 base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hTailNamed :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld
          r0 r1 r2 r3 baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyTailBound_eq]
    exact hTail
  rw [← expTwoMulFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_full_loop_boundary_of_entry_tail_exit_cases_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      e iterCount r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      iterCountNew baseWord exponentWord rest exitCond base hbase
      hEntry hCondExit hSkipExit hTailNamed

/-- Boundary-level wrapper that factors out the loop-entry assertion bridge.
    Callers can instantiate `P` with the concrete first-iteration precondition
    once the stack-frame alignment bridge is available. -/
theorem exp_two_mul_full_loop_boundary_of_entry_body_spec_within
    {P : Assertion}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        P hp)
    (hBody :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hEntryTriple :
      cpsTripleWithin 0 (base + 28) (base + 28)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        P :=
    cpsTripleWithin_extend_code
      (hmono := by
        intro a i h
        cases h)
      (cpsTripleWithin_refl hEntry)
  have hLoop :
      cpsTripleWithin (0 + expTwoMulFullLoopBodyBound)
        (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond) :=
    cpsTripleWithin_seq_same_cr hEntryTriple hBody
  exact
    exp_two_mul_full_loop_boundary_of_body_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      (by simpa using hLoop)

/-- Closed-form variant of
    `exp_two_mul_full_loop_boundary_of_entry_body_spec_within`. -/
theorem exp_two_mul_full_loop_boundary_of_entry_body_closed_bound_spec_within
    {P : Assertion}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        P hp)
    (hBody :
      cpsTripleWithin 48384 (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin 48401 base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBodyNamed :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyBound_eq]
    exact hBody
  rw [← expTwoMulFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_full_loop_boundary_of_entry_body_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      hEntry hBodyNamed

/-- Bounded-body variant of `exp_two_mul_full_loop_boundary_of_body_spec_within`.
    This lets the future 256-iteration proof use any body proof whose bound is
    no larger than the named full-loop body bound. -/
theorem exp_two_mul_full_loop_boundary_of_bounded_body_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps ≤ expTwoMulFullLoopBodyBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_full_loop_boundary_of_body_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      (cpsTripleWithin_mono_nSteps hBound hLoop)

/-- Closed-form bounded-body variant of
    `exp_two_mul_full_loop_boundary_of_bounded_body_spec_within`. -/
theorem exp_two_mul_full_loop_boundary_of_bounded_body_closed_bound_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps ≤ 48384)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin 48401 base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBoundNamed : nSteps ≤ expTwoMulFullLoopBodyBound := by
    rw [expTwoMulFullLoopBodyBound_eq]
    exact hBound
  rw [← expTwoMulFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_full_loop_boundary_of_bounded_body_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      hBoundNamed hLoop

/-- Closed-form variant of `exp_two_mul_full_loop_boundary_of_body_spec_within`.
    The future full-loop body proof can expose the concrete 256-iteration
    bound `48384`, and this wrapper packages the boundary at `48401`. -/
theorem exp_two_mul_full_loop_boundary_of_body_closed_bound_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin 48384 (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin 48401 base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hLoopNamed :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyBound_eq]
    exact hLoop
  rw [← expTwoMulFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_full_loop_boundary_of_body_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base hLoopNamed

/-- Generalised boundary composition that accepts the full-stack loop-exit
    pre-frame directly, with `d0..d3` as a separate parameters (not forced to
    equal `r0..r3`).

    This is the correct target for the 256-iteration loop body proof because
    at the loop exit PC the memory at `evmSp + 32..56` still holds the
    original exponent bytes (the epilogue overwrites them with the result
    `r0..r3`).  The caller must provide `d0..d3` = the values that are
    actually there at exit time.

    The standard `exp_two_mul_boundary_loop_epilogue_of_loop_spec_within`
    restricts to `d = r`, but the epilogue already supports arbitrary `d`:
    `exp_pointer_restore_then_epilogue_full_stack_..._canonical_appended_mul_spec_within`
    takes d0..d3 and r0..r3 as independent. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_general_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin (expTwoMulBoundaryLoopBound nSteps) base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBoundary :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base
  have hPrefix := cpsTripleWithin_seq_same_cr hBoundary hLoop
  -- The full-stack epilogue with arbitrary d0..d3 produces FullStackPostFrame = loopExitPost.
  have hEpilogue :
      cpsTripleWithin (1 + 9) (base + 264) (base + 304)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
        (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
          baseWord rest exitCond) := by
    unfold expTwoMulLoopExitPost
    exact exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond base
  exact cpsTripleWithin_mono_nSteps
    (by unfold expTwoMulBoundaryLoopBound expTwoMulBoundaryPrefixBound
            expTwoMulBoundarySuffixBound; omega)
    (cpsTripleWithin_seq_same_cr hPrefix hEpilogue)

/-- Bounded variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_general_spec_within`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_general_bounded_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : expTwoMulBoundaryLoopBound nSteps ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_boundary_loop_epilogue_of_loop_general_spec_within
        sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
        r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base hLoop)

/-- Closed-form bound variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_general_bounded_spec_within`,
    using the normalized boundary cost `nSteps + 17`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_general_closed_bound_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps + 17 ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_general_bounded_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base
      (by simpa [expTwoMulBoundaryLoopBound_eq] using hBound)
      hLoop

/-- Exact closed-form bound variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_general_spec_within`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_general_exact_closed_bound_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin (nSteps + 17) base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_general_closed_bound_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base (by rfl) hLoop

/-- Full-loop boundary wrapper for the generalized loop-exit pre-frame.

    This is the named-bound version of
    `exp_two_mul_boundary_loop_epilogue_of_loop_general_spec_within` at the
    full 256-iteration body bound.  The loop proof may keep the stack payload
    limbs `d0..d3` independent from the eventual result limbs `r0..r3`; the
    epilogue overwrites the stack result slot afterwards. -/
theorem exp_two_mul_full_loop_boundary_of_body_general_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_general_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base hLoop

/-- Generalized boundary wrapper that factors out the loop-entry assertion
    bridge.

    Downstream full-loop wire-up can instantiate `P` with the concrete first
    iteration precondition produced from `expTwoMulLoopEntryPost`, while the
    body proof targets the generalized full-stack loop-exit pre-frame. -/
theorem exp_two_mul_full_loop_boundary_of_entry_body_general_spec_within
    {P : Assertion}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        P hp)
    (hBody :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hEntryTriple :
      cpsTripleWithin 0 (base + 28) (base + 28)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        P :=
    cpsTripleWithin_extend_code
      (hmono := by
        intro a i h
        cases h)
      (cpsTripleWithin_refl hEntry)
  have hLoop :
      cpsTripleWithin (0 + expTwoMulFullLoopBodyBound)
        (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) :=
    cpsTripleWithin_seq_same_cr hEntryTriple hBody
  exact
    exp_two_mul_full_loop_boundary_of_body_general_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base
      (by simpa using hLoop)

/-- Closed-form variant of
    `exp_two_mul_full_loop_boundary_of_entry_body_general_spec_within`. -/
theorem exp_two_mul_full_loop_boundary_of_entry_body_general_closed_bound_spec_within
    {P : Assertion}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest hp →
        P hp)
    (hBody :
      cpsTripleWithin 48384 (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 48401 base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBodyNamed :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyBound_eq]
    exact hBody
  rw [← expTwoMulFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_full_loop_boundary_of_entry_body_general_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base
      hEntry hBodyNamed

/-- Closed-form variant of
    `exp_two_mul_full_loop_boundary_of_body_general_spec_within`. -/
theorem exp_two_mul_full_loop_boundary_of_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin 48384 (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 48401 base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hLoopNamed :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyBound_eq]
    exact hLoop
  rw [← expTwoMulFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_full_loop_boundary_of_body_general_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest exitCond base hLoopNamed

end EvmAsm.Evm64.Exp.Compose
