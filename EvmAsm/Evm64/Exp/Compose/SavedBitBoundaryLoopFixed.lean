/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixed

  Boundary composition for the fixed x19 two-MUL saved-bit EXP code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Fixed-x19 boundary precondition for the EXP prologue, including ownership
    of the exponent-cursor registers that the fixed prologue initializes. -/
@[irreducible]
def expTwoMulBoundaryPreFixed
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
   (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
   (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
   ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
   ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
   ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
   ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
   expTwoMulScratchFrame vOld v18 **
   evmStackIs evmSp (baseWord :: exponentWord :: rest))

theorem expTwoMulBoundaryPreFixed_unfold
    {sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 baseWord exponentWord rest =
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       expTwoMulScratchFrame vOld v18 **
       evmStackIs evmSp (baseWord :: exponentWord :: rest)) := by
  delta expTwoMulBoundaryPreFixed
  rfl

theorem expTwoMulBoundaryPreFixed_unfold_scratch
    {sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 baseWord exponentWord rest =
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)) **
       evmStackIs evmSp (baseWord :: exponentWord :: rest)) := by
  rw [expTwoMulBoundaryPreFixed_unfold, expTwoMulScratchFrame_unfold]

theorem expTwoMulBoundaryPreFixed_pcFree
    {sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 baseWord exponentWord rest).pcFree := by
  rw [expTwoMulBoundaryPreFixed_unfold]
  pcFree

instance pcFreeInst_expTwoMulBoundaryPreFixed
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest) :=
  ⟨expTwoMulBoundaryPreFixed_pcFree⟩

/-- Bound for the fixed-x19 prologue/pointer-advance boundary. -/
abbrev expTwoMulFixedBoundaryPrefixBound : Nat := 10 + 1

/-- Bound for the fixed-x19 boundary composition around a loop proof with
    `nSteps`. -/
abbrev expTwoMulFixedBoundaryLoopBound (nSteps : Nat) : Nat :=
  (expTwoMulFixedBoundaryPrefixBound + nSteps) + expTwoMulBoundarySuffixBound

theorem expTwoMulFixedBoundaryLoopBound_eq (nSteps : Nat) :
    expTwoMulFixedBoundaryLoopBound nSteps = nSteps + 21 := by
  unfold expTwoMulFixedBoundaryLoopBound expTwoMulFixedBoundaryPrefixBound
    expTwoMulBoundarySuffixBound
  omega

/-- Conservative bound for the fixed-x19 full boundary, including prologue and
    pointer-restore/epilogue. -/
abbrev expTwoMulFixedFullLoopBoundaryBound : Nat :=
  expTwoMulFixedBoundaryLoopBound expTwoMulFixedFullLoopBodyBound

theorem expTwoMulFixedFullLoopBoundaryBound_eq :
    expTwoMulFixedFullLoopBoundaryBound = 49429 := by
  rw [expTwoMulFixedFullLoopBoundaryBound, expTwoMulFixedBoundaryLoopBound_eq,
    expTwoMulFixedFullLoopBodyBound_eq]

/-- Fixed-code analogue of the general boundary composition: fixed prologue,
    caller-supplied loop proof, and fixed pointer-restore/epilogue. -/
theorem exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin ((10 + 1 + nSteps) + (1 + 9)) base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBoundary :
      cpsTripleWithin (10 + 1) base (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
          m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest) := by
    rw [expTwoMulBoundaryPreFixed_unfold]
    exact
      exp_prologue_fixed_then_pointer_advance_full_stack_evmExpMsbSavedBitTwoMulFixedWithMulCode_spec_within
        sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
        base (base + 336)
  have hPrefix := cpsTripleWithin_seq_same_cr hBoundary hLoop
  have hEpilogue :
      cpsTripleWithin (1 + 9) (base + 296) (base + 336)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
        (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
          baseWord rest exitCond) := by
    unfold expTwoMulLoopExitPost
    exact
      exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_canonical_appended_mul_spec_within
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond base
  exact cpsTripleWithin_seq_same_cr hPrefix hEpilogue

/-- Named-bound variant of
    `exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_spec_within`. -/
theorem exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_named_bound_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin (expTwoMulFixedBoundaryLoopBound nSteps) base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  simpa [expTwoMulFixedBoundaryLoopBound_eq, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hLoop

/-- Caller-chosen bound variant of the fixed boundary composition. -/
theorem exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_bounded_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : expTwoMulFixedBoundaryLoopBound nSteps ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_named_bound_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hLoop)

/-- Closed-form bound variant of the fixed boundary composition. -/
theorem exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_closed_bound_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps + 21 ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_bounded_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
    iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
    exitCond base
    (by simpa [expTwoMulFixedBoundaryLoopBound_eq] using hBound)
    hLoop

/-- Exact closed-form bound variant of the fixed boundary composition. -/
theorem exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_exact_closed_bound_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin (nSteps + 21) base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_closed_bound_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
    iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
    exitCond base (by rfl) hLoop

/-- Fixed full-loop boundary wrapper over a caller-supplied 256-iteration loop
    proof at the conservative fixed reload-path bound. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_named_bound_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
    iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
    exitCond base hLoop

/-- Fixed boundary-level wrapper that factors out the loop-entry assertion
    bridge. Callers can instantiate `P` with the concrete first fixed-iteration
    precondition once the stack-frame alignment bridge is available. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
    {P : Assertion}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        P hp)
    (hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hEntryTriple :
      cpsTripleWithin 0 (base + 44) (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        P :=
    cpsTripleWithin_extend_code
      (hmono := by
        intro a i h
        cases h)
      (cpsTripleWithin_refl hEntry)
  have hLoop :
      cpsTripleWithin (0 + expTwoMulFixedFullLoopBodyBound)
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) :=
    cpsTripleWithin_seq_same_cr hEntryTriple hBody
  exact
    exp_two_mul_fixed_full_loop_boundary_of_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base (by simpa using hLoop)

/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_closed_bound_spec_within
    {P : Assertion}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        P hp)
    (hBody :
      cpsTripleWithin 49408 (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBodyNamed :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        P
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) := by
    rw [expTwoMulFixedFullLoopBodyBound_eq]
    exact hBody
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hEntry hBodyNamed

/-- Boundary-level wrapper for the first fixed full-loop body iteration. It
    leaves the fixed loop-entry bridge and the case-post exit bridge as
    caller-supplied assertion implications, and consumes the named case-post
    loop-back tail continuation. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) :=
    exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
        r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
      hbase hExit hTail
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hEntry hBody

/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin 49215
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hTailNamed :
      cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) := by
    rw [expTwoMulFixedFullLoopBodyTailBound_eq]
    exact hTail
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
      hEntry hExit hTailNamed

/-- Boundary-level wrapper for the first fixed full-loop body iteration with
    the iteration stack pointer separated from the boundary stack pointer. This
    is the shape needed after the fixed prologue advances `x12`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_spec_within
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) :=
    exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp iterSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
        r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
      hbase hExit hTail
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hEntry hBody

/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_closed_bound_spec_within
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin 49215
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hTailNamed :
      cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) := by
    rw [expTwoMulFixedFullLoopBodyTailBound_eq]
    exact hTail
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_spec_within
      sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
      hEntry hExit hTailNamed

/-- Bounded variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_closed_bound_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_bounded_spec_within
    {nBound : Nat}
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hBound : 49429 ≤ nBound)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin 49215
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_closed_bound_spec_within
      sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
      hEntry hExit hTail)

/-- Non-final variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_spec_within`.
    The case-post exit branch is impossible, so callers only supply the
    loop-back tail continuation at the separated iteration stack pointer. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_iter_sp_spec_within
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hTail :
      cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_spec_within
    sp evmSp iterSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 e c6 iterCount v10 ptr nextLimb
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
    hEntry
    (exp_fixed_iter_case_exit_vacuous_bridge hne)
    hTail

/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_iter_sp_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_iter_sp_closed_bound_spec_within
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hTail :
      cpsTripleWithin 49215
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_closed_bound_spec_within
    sp evmSp iterSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 e c6 iterCount v10 ptr nextLimb
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
    hEntry
    (exp_fixed_iter_case_exit_vacuous_bridge hne)
    hTail

/-- Final-count variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_iter_sp_spec_within`.
    The loop-back branch is impossible, so callers only supply the case-post
    exit bridge at the separated iteration stack pointer. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_iter_sp_spec_within
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) :=
    exp_two_mul_fixed_full_loop_body_peel_tail_case_final_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp iterSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
        r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
      hbase hzero hExit
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hEntry hBody

/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_iter_sp_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_iter_sp_closed_bound_spec_within
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp iterSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp iterSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_iter_sp_spec_within
      sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
      hzero hEntry hExit

/-- Non-final fixed boundary-level wrapper for the first full-loop body
    iteration. The current case-post exit edge is impossible, so callers only
    supply the loop-back case-post tail continuation. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hTail :
      cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
    e c6 iterCount v10 ptr nextLimb
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
    hEntry
    (exp_fixed_iter_case_exit_vacuous_bridge hne)
    hTail

/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hTail :
      cpsTripleWithin 49215
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_posts_closed_bound_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
    e c6 iterCount v10 ptr nextLimb
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
    hEntry
    (exp_fixed_iter_case_exit_vacuous_bridge hne)
    hTail

/-- Final fixed boundary-level wrapper for the first full-loop body iteration.
    The loop-back edge is impossible at the final count, so callers only supply
    the case-post exit bridge. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) :=
    exp_two_mul_fixed_full_loop_body_peel_tail_case_final_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
        r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)
      hbase hzero hExit
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hEntry hBody

/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hEntry :
      ∀ hp,
        expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest hp →
        expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 hp)
    (hExit :
      ∀ hp,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base hp →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
      hzero hEntry hExit

/-- Fixed boundary wrapper that accepts any body proof bounded by the named
    conservative fixed full-loop body bound. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_bounded_body_general_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps ≤ expTwoMulFixedFullLoopBodyBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
    iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
    exitCond base
    (cpsTripleWithin_mono_nSteps hBound hLoop)

/-- Closed-form bounded-body variant of
    `exp_two_mul_fixed_full_loop_boundary_of_bounded_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_bounded_body_general_closed_bound_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps ≤ 49408)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBoundNamed : nSteps ≤ expTwoMulFixedFullLoopBodyBound := by
    rw [expTwoMulFixedFullLoopBodyBound_eq]
    exact hBound
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_bounded_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hBoundNamed hLoop

/-- Bounded fixed full-loop boundary wrapper over a caller-supplied
    256-iteration loop proof. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_body_general_bounded_spec_within
    {nBound : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : expTwoMulFixedFullLoopBoundaryBound ≤ nBound)
    (hLoop :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_two_mul_fixed_full_loop_boundary_of_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hLoop)

/-- Closed-form fixed full-loop boundary wrapper for a 49408-step loop proof. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin 49408 (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hLoopNamed :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond) := by
    rwa [expTwoMulFixedFullLoopBodyBound_eq]
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hLoopNamed

/-- Bounded closed-form fixed full-loop boundary wrapper for a 49408-step
    loop proof. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_body_general_closed_bounded_spec_within
    {nBound : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : 49429 ≤ nBound)
    (hLoop :
      cpsTripleWithin 49408 (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_two_mul_fixed_full_loop_boundary_of_body_general_closed_bound_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      iterCountNew r0 r1 r2 r3 d0 d1 d2 d3 baseWord exponentWord rest
      exitCond base hLoop)

end EvmAsm.Evm64.Exp.Compose
