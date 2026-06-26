/-
  EvmAsm.Evm64.Exp.Compose.FixedLoopInd

  Nat-indexed induction for the fixed-x19 EXP square-and-multiply loop body.

  The fixed loop body is assembled from the per-iteration direct head step
  `cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_tailOrSuccessorFrameN_of_pre`
  (see `SavedBitFixedInductionFrameLoopDirect`), mirroring the proven
  non-fixed template `exp_loop_from_looppost_induction_general`
  (`SavedBitLoopBodyInd`).

  This module collects the arithmetic and structural glue that the
  256-iteration assembly consumes.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFrameLoopDirect
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixedEntryExists

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The conservative fixed-x19 256-iteration full-body bound is exactly the
    256-fold iteration-body bound.  This is the closed form consumed by the
    Nat induction over the fixed loop, which counts iterations rather than
    peeling a named first iteration. -/
theorem expTwoMulFixedFullLoopBodyBound_eq_iterationsBodyBound_256 :
    expTwoMulFixedFullLoopBodyBound = expTwoMulFixedIterationsBodyBound 256 := by
  rw [expTwoMulFixedFullLoopBodyBound_eq, expTwoMulFixedIterationsBodyBound_eq]

/-- Base case of the fixed-loop induction: the final iteration `k = 255`.

    At `k = 255` every `k < 255` head-step continuation is vacuous, so the
    direct head step
    `cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_tailOrSuccessorFrameN_of_pre`
    collapses to requiring only the loop-exit bridge `hExit`. -/
theorem exp_two_mul_fixed_loop_final_iteration_spec
    {baseWord exponentWord : EvmWord} {iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (255 + 1) / 64))
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame 255 baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord 255
        controlC6 ptr nextNextLimb) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_tailOrSuccessorFrameN_of_pre
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
    nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
    e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 base Q hbase
    hControlMachine (by decide) hBase hNextNext
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun _ => hExit)

end EvmAsm.Evm64.Exp.Compose
