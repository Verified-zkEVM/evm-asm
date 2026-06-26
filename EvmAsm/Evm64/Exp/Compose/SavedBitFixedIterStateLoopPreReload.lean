/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopPreReload

  Pre-reload direct-loop adapters for the fixed EXP induction frame.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopDirect

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expPreReloadDirectTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr nextNextLimb : Word) :
    Assertion :=
  expReloadDirectTailFrame ptr nextNextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expPreReloadDirectTailFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word} :
    expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb =
      (((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))) := by
  rw [expPreReloadDirectTailFrameN, expReloadDirectTailFrame_unfold]

@[irreducible]
def expPreReloadDirectFalseFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expPreReloadDirectFalseFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expPreReloadDirectFalseFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) = 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expPreReloadDirectFalseFrameN, expReloadDirectFalseFrame_unfold]

@[irreducible]
def expPreReloadDirectTrueFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expPreReloadDirectTrueFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expPreReloadDirectTrueFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expPreReloadDirectTrueFrameN, expReloadDirectTrueFrame_unfold]

/-- Pre-reload direct head step over the two-cell lookahead frame.

    At `k % 64 = 62`, this step is still a no-reload step, but the recursive
    successor has `c6 = 1` and needs the reload-limb frame for the imminent
    reload. The pre-reload frame carries both the current saved-next cell and
    the successor reload cell. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_control_from_pre
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
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
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
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedPreReloadFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr :=
    expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext hNextNext
  have hPreReloadEq :
      expTwoMulFixedPreReloadFrameN exponentWord k ptr =
        (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
          expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12))) :=
    expTwoMulFixedPreReloadFrameN_handoff_of_control hControl hC6
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [hPreReloadEq] at h
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold] at h
        simpa only [expReloadDirectTailFrame_unfold] using h)
      (fun _ h => by
        rw [hPreReloadEq, ← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold]
        simpa only [expReloadDirectTailFrame_unfold] using h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base
        (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))
        Q
        (by
          rw [expTwoMulFixedReloadLimbFrameN_unfold,
            expTwoMulFixedSavedNextLimbFrame_unfold]
          pcFree)
        hbase hControlMachine hk hBase hNextNext
        (fun hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectBranchPre,
            expReloadDirectTailFrame_unfold,
            expPreReloadDirectTailFrameN_unfold] using
            hBranch hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v6' v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectFalsePre,
            expReloadDirectFalseFrame_unfold,
            expReloadDirectTailFrame_unfold,
            expPreReloadDirectFalseFrameN_unfold,
            expPreReloadDirectTailFrameN_unfold] using
            hReloadFalse hk_lt v6' v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v6' v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectTruePre,
            expReloadDirectTrueFrame_unfold,
            expReloadDirectTailFrame_unfold,
            expPreReloadDirectTrueFrameN_unfold,
            expPreReloadDirectTailFrameN_unfold] using
            hReloadTrue hk_lt v6' v7' v10' v11' d0' d1' d2' d3')
        hExit)

/-- From-pre variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_control_from_pre`.

    The current `WithStateFrame` precondition already carries the control
    invariant; this wrapper extracts it internally so recursive callers only
    need to provide the pre-reload branch fact. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_pre
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
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedPreReloadFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithStateFrame_pure hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_control_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hState.2.2.1 hC6 hNextNext hBranch hReloadFalse hReloadTrue hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc

end EvmAsm.Evm64.Exp.Compose
