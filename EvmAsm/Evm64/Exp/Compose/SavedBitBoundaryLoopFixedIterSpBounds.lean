/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixedIterSpBounds

  Bounded variants for fixed boundary wrappers with a separated iteration
  stack pointer.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixed

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Bounded variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_iter_sp_closed_bound_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_iter_sp_bounded_spec_within
    {nBound : Nat}
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hBound : 49429 ≤ nBound)
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
    cpsTripleWithin nBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_nonfinal_iter_sp_closed_bound_spec_within
      sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
      hne hEntry hTail)

/-- Bounded variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_iter_sp_closed_bound_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_iter_sp_bounded_spec_within
    {nBound : Nat}
    (sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18
      e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
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
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond hp) :
    cpsTripleWithin nBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_two_mul_fixed_full_loop_boundary_of_entry_tail_case_final_iter_sp_closed_bound_spec_within
      sp evmSp iterSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 e c6 iterCount v10 ptr nextLimb
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 iterCountNew baseWord exponentWord rest exitCond base hbase
      hzero hEntry hExit)

end EvmAsm.Evm64.Exp.Compose
