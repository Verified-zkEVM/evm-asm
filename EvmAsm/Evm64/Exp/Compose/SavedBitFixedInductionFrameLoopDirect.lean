/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFrameLoopDirect

  Direct-loop wrappers that consume the with-state induction-frame precondition.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFramePre
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopDirect
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopPreReload

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_reloadTail_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedReloadTailFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_reload_of_control hC6]
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadTailFrameN_of_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase hC6
      hNextNext hBranch hReloadFalse hReloadTrue hExit

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_preReload_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_pre_reload_of_control hC6]
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase hC6
      hNextNext hBranch hReloadFalse hReloadTrue hExit

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_ordinary_of_control_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
        nextLimb evmSp)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
    hC6 hNotPre]
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_succ_no_reload_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      (expTwoMulFixedControlInvariant_ordinary_no_reload_mod
        hControl hC6 hNotPre)
      hNextNext hBranch hReloadFalse hReloadTrue hExit

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_ordinary_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
        nextLimb evmSp :=
    expTwoMulFixedIterPreNWithInductionFrame_control hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_ordinary_of_control_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hControl hC6 hNotPre hNextNext hBranch hReloadFalse hReloadTrue
      hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc


@[irreducible]
def expTwoMulFixedDirectHeadTailFrameN
    (exponentWord : EvmWord) (k : Nat) (controlC6 ptr nextNextLimb : Word) :
    Assertion :=
  if expTwoMulFixedControlDec controlC6 = (0 : Word) then
    expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb
  else if (expTwoMulFixedControlDec controlC6).toNat = 1 then
    expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb
  else
    expReloadLimbDirectTailFrame ptr nextNextLimb

@[irreducible]
def expTwoMulFixedDirectHeadFalseFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  if expTwoMulFixedControlDec controlC6 = (0 : Word) then
    expReloadTailDirectFalseFrameN exponentWord k controlC6 e iterCount ptr
      nextLimb
  else if (expTwoMulFixedControlDec controlC6).toNat = 1 then
    expPreReloadDirectFalseFrameN exponentWord k controlC6 e iterCount ptr
      nextLimb
  else
    expReloadLimbDirectFalseFrame controlC6 e iterCount ptr nextLimb

@[irreducible]
def expTwoMulFixedDirectHeadTrueFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  if expTwoMulFixedControlDec controlC6 = (0 : Word) then
    expReloadTailDirectTrueFrameN exponentWord k controlC6 e iterCount ptr
      nextLimb
  else if (expTwoMulFixedControlDec controlC6).toNat = 1 then
    expPreReloadDirectTrueFrameN exponentWord k controlC6 e iterCount ptr
      nextLimb
  else
    expReloadLimbDirectTrueFrame controlC6 e iterCount ptr nextLimb


@[irreducible]
def expTwoMulFixedDirectHeadTailOrSuccessorFrameN
    (exponentWord : EvmWord) (k : Nat) (controlC6 ptr nextNextLimb : Word) :
    Assertion :=
  if expTwoMulFixedControlDec controlC6 = (0 : Word) then
    expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb
  else if (expTwoMulFixedControlDec controlC6).toNat = 1 then
    expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb
  else
    expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr

theorem expTwoMulFixedDirectHeadTailFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 ptr nextNextLimb : Word) :
    (expTwoMulFixedDirectHeadTailFrameN exponentWord k controlC6 ptr
      nextNextLimb).pcFree := by
  rw [expTwoMulFixedDirectHeadTailFrameN]
  split
  · rw [expReloadTailDirectTailFrameN_unfold]
    pcFree
    rw [expTwoMulFixedReloadLimbFrameN_unfold,
      expTwoMulFixedSavedNextLimbFrame_unfold]
    pcFree
  · split
    · rw [expPreReloadDirectTailFrameN_unfold]
      pcFree
      rw [expTwoMulFixedReloadLimbFrameN_unfold,
        expTwoMulFixedSavedNextLimbFrame_unfold]
      pcFree
    · rw [expReloadLimbDirectTailFrame_unfold]
      pcFree

theorem expTwoMulFixedDirectHeadFalseFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) :
    (expTwoMulFixedDirectHeadFalseFrameN exponentWord k controlC6 e
      iterCount ptr nextLimb).pcFree := by
  rw [expTwoMulFixedDirectHeadFalseFrameN]
  split
  · rw [expReloadTailDirectFalseFrameN_unfold]
    pcFree
    rw [expTwoMulFixedReloadLimbFrameN_unfold,
      expTwoMulFixedSavedNextLimbFrame_unfold]
    pcFree
  · split
    · rw [expPreReloadDirectFalseFrameN_unfold]
      pcFree
      rw [expTwoMulFixedReloadLimbFrameN_unfold,
        expTwoMulFixedSavedNextLimbFrame_unfold]
      pcFree
    · rw [expReloadLimbDirectFalseFrame_unfold]
      pcFree

theorem expTwoMulFixedDirectHeadTrueFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) :
    (expTwoMulFixedDirectHeadTrueFrameN exponentWord k controlC6 e
      iterCount ptr nextLimb).pcFree := by
  rw [expTwoMulFixedDirectHeadTrueFrameN]
  split
  · rw [expReloadTailDirectTrueFrameN_unfold]
    pcFree
    rw [expTwoMulFixedReloadLimbFrameN_unfold,
      expTwoMulFixedSavedNextLimbFrame_unfold]
    pcFree
  · split
    · rw [expPreReloadDirectTrueFrameN_unfold]
      pcFree
      rw [expTwoMulFixedReloadLimbFrameN_unfold,
        expTwoMulFixedSavedNextLimbFrame_unfold]
      pcFree
    · rw [expReloadLimbDirectTrueFrame_unfold]
      pcFree


theorem expTwoMulFixedDirectHeadTailOrSuccessorFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 ptr nextNextLimb : Word) :
    (expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k controlC6
      ptr nextNextLimb).pcFree := by
  rw [expTwoMulFixedDirectHeadTailOrSuccessorFrameN]
  split
  · rw [expReloadTailDirectTailFrameN_unfold]
    pcFree
    rw [expTwoMulFixedReloadLimbFrameN_unfold,
      expTwoMulFixedSavedNextLimbFrame_unfold]
    pcFree
  · split
    · rw [expPreReloadDirectTailFrameN_unfold]
      pcFree
      rw [expTwoMulFixedReloadLimbFrameN_unfold,
        expTwoMulFixedSavedNextLimbFrame_unfold]
      pcFree
    · exact expTwoMulFixedSavedNextLimbFrameN_pcFree exponentWord (k + 1) ptr

instance pcFreeInst_expTwoMulFixedDirectHeadTailFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 ptr nextNextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedDirectHeadTailFrameN exponentWord k controlC6 ptr
        nextNextLimb) :=
  ⟨expTwoMulFixedDirectHeadTailFrameN_pcFree exponentWord k controlC6 ptr
    nextNextLimb⟩

instance pcFreeInst_expTwoMulFixedDirectHeadFalseFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedDirectHeadFalseFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb) :=
  ⟨expTwoMulFixedDirectHeadFalseFrameN_pcFree exponentWord k controlC6 e
    iterCount ptr nextLimb⟩

instance pcFreeInst_expTwoMulFixedDirectHeadTrueFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedDirectHeadTrueFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb) :=
  ⟨expTwoMulFixedDirectHeadTrueFrameN_pcFree exponentWord k controlC6 e
    iterCount ptr nextLimb⟩


instance pcFreeInst_expTwoMulFixedDirectHeadTailOrSuccessorFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 ptr nextNextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k controlC6
        ptr nextNextLimb) :=
  ⟨expTwoMulFixedDirectHeadTailOrSuccessorFrameN_pcFree exponentWord k
    controlC6 ptr nextNextLimb⟩

theorem expTwoMulFixedDirectHeadTailFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedDirectHeadTailFrameN exponentWord k controlC6 ptr
        nextNextLimb =
      expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb := by
  rw [expTwoMulFixedDirectHeadTailFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  exact if_pos hC6

theorem expTwoMulFixedDirectHeadTailFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedDirectHeadTailFrameN exponentWord k controlC6 ptr
        nextNextLimb =
      expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb := by
  rw [expTwoMulFixedDirectHeadTailFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    have hNatZero : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by
      rw [hZero]
      decide
    exact False.elim (Nat.zero_ne_one (by rw [← hNatZero, hC6]))
  · rfl

theorem expTwoMulFixedDirectHeadTailFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre :
      (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedDirectHeadTailFrameN exponentWord k controlC6 ptr
        nextNextLimb =
      expReloadLimbDirectTailFrame ptr nextNextLimb := by
  rw [expTwoMulFixedDirectHeadTailFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl

theorem expTwoMulFixedDirectHeadFalseFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedDirectHeadFalseFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb =
      expReloadTailDirectFalseFrameN exponentWord k controlC6 e iterCount ptr
        nextLimb := by
  rw [expTwoMulFixedDirectHeadFalseFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  exact if_pos hC6

theorem expTwoMulFixedDirectHeadFalseFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word}
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedDirectHeadFalseFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb =
      expPreReloadDirectFalseFrameN exponentWord k controlC6 e iterCount ptr
        nextLimb := by
  rw [expTwoMulFixedDirectHeadFalseFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    have hNatZero : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by
      rw [hZero]
      decide
    exact False.elim (Nat.zero_ne_one (by rw [← hNatZero, hC6]))
  · rfl

theorem expTwoMulFixedDirectHeadFalseFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre :
      (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedDirectHeadFalseFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb =
      expReloadLimbDirectFalseFrame controlC6 e iterCount ptr nextLimb := by
  rw [expTwoMulFixedDirectHeadFalseFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl

theorem expTwoMulFixedDirectHeadTrueFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedDirectHeadTrueFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb =
      expReloadTailDirectTrueFrameN exponentWord k controlC6 e iterCount ptr
        nextLimb := by
  rw [expTwoMulFixedDirectHeadTrueFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  exact if_pos hC6

theorem expTwoMulFixedDirectHeadTrueFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word}
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedDirectHeadTrueFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb =
      expPreReloadDirectTrueFrameN exponentWord k controlC6 e iterCount ptr
        nextLimb := by
  rw [expTwoMulFixedDirectHeadTrueFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    have hNatZero : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by
      rw [hZero]
      decide
    exact False.elim (Nat.zero_ne_one (by rw [← hNatZero, hC6]))
  · rfl

theorem expTwoMulFixedDirectHeadTrueFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre :
      (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedDirectHeadTrueFrameN exponentWord k controlC6 e
        iterCount ptr nextLimb =
      expReloadLimbDirectTrueFrame controlC6 e iterCount ptr nextLimb := by
  rw [expTwoMulFixedDirectHeadTrueFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl



theorem expTwoMulFixedDirectHeadTailOrSuccessorFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k controlC6 ptr
        nextNextLimb =
      expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb := by
  rw [expTwoMulFixedDirectHeadTailOrSuccessorFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  exact if_pos hC6

theorem expTwoMulFixedDirectHeadTailOrSuccessorFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k controlC6 ptr
        nextNextLimb =
      expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb := by
  rw [expTwoMulFixedDirectHeadTailOrSuccessorFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    have hNatZero : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by
      rw [hZero]
      decide
    exact False.elim (Nat.zero_ne_one (by rw [← hNatZero, hC6]))
  · rfl

theorem expTwoMulFixedDirectHeadTailOrSuccessorFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre :
      (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k controlC6 ptr
        nextNextLimb =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedDirectHeadTailOrSuccessorFrameN]
  rw [expTwoMulFixedControlDec_unfold]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl

theorem expTwoMulFixedReloadTailFrameN_eq_direct_tail_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 ptr nextLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedReloadLimbFrameN exponentWord k ptr :=
    expTwoMulFixedReloadLimbFrameN_eq_of_control_reload_nextNext
      hControl hC6 hNextNext
  have hTailEq :
      expTwoMulFixedReloadTailFrameN exponentWord k ptr =
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
          expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
            (ptr + signExtend12 (-8 : BitVec 12))) :=
    expTwoMulFixedReloadTailFrameN_handoff_of_control hControl hC6
  rw [hTailEq, ← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold,
    expReloadTailDirectTailFrameN_unfold]

theorem expTwoMulFixedPreReloadFrameN_eq_direct_tail_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 ptr nextLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedPreReloadFrameN exponentWord k ptr =
      expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr :=
    expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext hNextNext
  have hMod : k % 64 = 62 :=
    expTwoMulFixedControlInvariant_pre_reload_mod hControl hC6
  have hSecondEq :
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12)) =
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12)) :=
    expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_pre_reload
      (ptr := ptr + signExtend12 (-8 : BitVec 12)) hMod
  rw [expTwoMulFixedPreReloadFrameN_unfold, hSecondEq, ← hFrameEq,
    expTwoMulFixedSavedNextLimbFrame_unfold,
    expPreReloadDirectTailFrameN_unfold]


theorem expTwoMulFixedDirectHeadFrameN_eq_tailFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 ptr nextLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedDirectHeadFrameN exponentWord k controlC6 ptr =
      expTwoMulFixedDirectHeadTailFrameN exponentWord k controlC6 ptr
        nextNextLimb := by
  rw [expTwoMulFixedDirectHeadFrameN_reload_of_control hC6,
    expTwoMulFixedDirectHeadTailFrameN_reload_of_control hC6]
  exact expTwoMulFixedReloadTailFrameN_eq_direct_tail_of_control
    hControl hC6 hNextNext

theorem expTwoMulFixedDirectHeadFrameN_eq_tailFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 ptr nextLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedDirectHeadFrameN exponentWord k controlC6 ptr =
      expTwoMulFixedDirectHeadTailFrameN exponentWord k controlC6 ptr
        nextNextLimb := by
  rw [expTwoMulFixedDirectHeadFrameN_pre_reload_of_control hC6,
    expTwoMulFixedDirectHeadTailFrameN_pre_reload_of_control hC6]
  exact expTwoMulFixedPreReloadFrameN_eq_direct_tail_of_control
    hControl hC6 hNextNext


theorem expTwoMulFixedDirectHeadFrameN_eq_tailOrSuccessorFrameN_of_control
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 ptr nextLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedDirectHeadFrameN exponentWord k controlC6 ptr =
      expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k controlC6
        ptr nextNextLimb := by
  rcases expTwoMulFixedControlInvariant_step_cases hControl with
      hReload | hPre | ⟨hOrd, hNotPre, _hMod⟩
  · rw [expTwoMulFixedDirectHeadFrameN_eq_tailFrameN_reload_of_control
      hControl hReload hNextNext]
    rw [expTwoMulFixedDirectHeadTailFrameN_reload_of_control hReload,
      expTwoMulFixedDirectHeadTailOrSuccessorFrameN_reload_of_control hReload]
  · rw [expTwoMulFixedDirectHeadFrameN_eq_tailFrameN_pre_reload_of_control
      hControl hPre hNextNext]
    rw [expTwoMulFixedDirectHeadTailFrameN_pre_reload_of_control hPre,
      expTwoMulFixedDirectHeadTailOrSuccessorFrameN_pre_reload_of_control hPre]
  · rw [expTwoMulFixedDirectHeadFrameN_ordinary_of_control hOrd hNotPre,
      expTwoMulFixedDirectHeadTailOrSuccessorFrameN_ordinary_of_control
        hOrd hNotPre]

theorem expTwoMulFixedDirectHeadFrameN_eq_tailOrSuccessorFrameN_from_framed_pre
    {baseWord exponentWord : EvmWord} {k : Nat}
    {controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 nextNextLimb : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedDirectHeadFrameN exponentWord k controlC6 ptr =
      expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k controlC6
        ptr nextNextLimb := by
  obtain ⟨ps, _h_compat, hPreRps⟩ := hPreR
  exact expTwoMulFixedDirectHeadFrameN_eq_tailOrSuccessorFrameN_of_control
    (expTwoMulFixedIterPreNWithInductionFrame_control_from_framed_pre hPreRps)
    hNextNext

/-- Direct head step over the folded induction precondition with a single
    post-frame selector.

    The framed precondition carries the control invariant, so this wrapper
    splits reload, pre-reload, and ordinary no-reload cases internally and
    rewrites `expTwoMulFixedDirectHeadFrameN` to the selected branch post. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_directHeadFrameN_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hReloadBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTailFrameN exponentWord k ptr
              nextNextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hPreBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTailFrameN exponentWord k ptr
              nextNextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hPreFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hPreTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hOrdBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hOrdFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hOrdTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedDirectHeadFrameN exponentWord k controlC6 ptr) := by
  intro R hR s hcr hPreR hpc
  have hCases :=
    expTwoMulFixedIterPreNWithInductionFrame_control_step_cases_from_holdsFor
      hPreR
  rcases hCases with hReload | hPreReload | ⟨hOrd, hNotPre, _hMod⟩
  · rw [expTwoMulFixedDirectHeadFrameN_reload_of_control hReload]
    exact
      cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_reloadTail_of_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
        nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 base Q hbase
        hControlMachine hk hBase hReload hNextNext hReloadBranch
        hReloadFalse hReloadTrue hExit
        R hR s hcr hPreR hpc
  · rw [expTwoMulFixedDirectHeadFrameN_pre_reload_of_control hPreReload]
    exact
      cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_preReload_of_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
        nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 base Q hbase
        hControlMachine hk hBase hPreReload hNextNext hPreBranch hPreFalse
        hPreTrue hExit
        R hR s hcr hPreR hpc
  · rw [expTwoMulFixedDirectHeadFrameN_ordinary_of_control hOrd hNotPre]
    exact
      cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_ordinary_of_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
        nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 base Q hbase
        hControlMachine hk hBase hOrd hNotPre hNextNext hOrdBranch
        hOrdFalse hOrdTrue hExit
        R hR s hcr hPreR hpc

/-- Direct head step over the folded induction precondition with the mixed
    tail-or-successor post-frame selector.

    This keeps the same continuation hypotheses as the broader direct-head
    wrapper and only rewrites the final postcondition using the control
    invariant carried by the induction frame. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_tailOrSuccessorFrameN_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hReloadBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTailFrameN exponentWord k ptr
              nextNextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hPreBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTailFrameN exponentWord k ptr
              nextNextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hPreFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hPreTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hOrdBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hOrdFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hOrdTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord k
        controlC6 ptr nextNextLimb) := by
  intro R hR s hcr hPreR hpc
  rw [← expTwoMulFixedDirectHeadFrameN_eq_tailOrSuccessorFrameN_from_framed_pre
    hPreR hNextNext]
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_directHeadFrameN_of_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 base Q hbase
      hControlMachine hk hBase hNextNext hReloadBranch hReloadFalse
      hReloadTrue hPreBranch hPreFalse hPreTrue hOrdBranch hOrdFalse
      hOrdTrue hExit
      R hR s hcr hPreR hpc


end EvmAsm.Evm64.Exp.Compose
