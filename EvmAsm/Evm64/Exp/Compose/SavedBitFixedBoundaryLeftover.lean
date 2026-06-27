/-
  Leftover-aware fixed boundary: composes prologue ;; loop ;; epilogue where the
  loop's exit post carries a leftover frame `L` — the registers / ownership left
  live by the *real* loop body (x19, x20, x18, x16, x1, regOwn x6/x7/x10/x11) that
  the bare `expTwoMulLoopExitFullStackPreFrame` interface of
  `exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_spec_within` omits.

  The epilogue spec is proven over the *bare* `FullStackPreFrame`, so its footprint
  provably excludes `L`; `cpsTripleWithin_frameR` therefore carries `L` through the
  epilogue automatically.  This is the missing reconciliation that lets a real loop
  induction (whose exit genuinely leaves `L` live) feed the boundary.
-/
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixed
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEntryFixedIterPre

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Leftover-aware variant of
    `exp_two_mul_fixed_boundary_loop_epilogue_of_loop_general_spec_within`:
    the loop hypothesis may leave an arbitrary pcFree frame `L` live at exit, which
    is threaded through the (bare) epilogue and appears in the boundary post. -/
theorem exp_two_mul_fixed_boundary_loop_epilogue_of_loop_leftover_general_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (L : Assertion) (hL : L.pcFree)
    (hLoop :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPostFixed sp evmSp vOld v18
          baseWord exponentWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond ** L)) :
    cpsTripleWithin ((10 + 1 + nSteps) + (1 + 9)) base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond ** L) := by
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
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond ** L)
        (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
          baseWord rest exitCond ** L) := by
    unfold expTwoMulLoopExitPost
    exact cpsTripleWithin_frameR L hL
      (exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_canonical_appended_mul_spec_within
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond base)
  exact cpsTripleWithin_seq_same_cr hPrefix hEpilogue

/-- Leftover-aware variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within`:
    the loop body is phrased over `expTwoMulFixedFirstIterPreWithResidual` (the
    surface the residual induction produces) and may leave an arbitrary pcFree
    frame `L` live at exit, which appears in the boundary post. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_leftover_general_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (L : Assertion) (hL : L.pcFree)
    (hBody :
      cpsTripleWithin nSteps (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond ** L)) :
    cpsTripleWithin ((10 + 1 + nSteps) + (1 + 9)) base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond ** L) :=
  exp_two_mul_fixed_boundary_loop_epilogue_of_loop_leftover_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord (dWord :: eWord :: rest) exitCond base L hL
    (cpsTripleWithin_weaken
      (fun _ h => expTwoMulLoopEntryPostFixed_to_firstIterPreWithResidual h)
      (fun _ h => h)
      hBody)

end EvmAsm.Evm64.Exp.Compose
