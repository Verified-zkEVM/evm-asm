/-
  Final chain for `evm_exp_stack_spec_within`.

  Packages the fixed exit post `R` (the existential `FullStackPreFrame ** L_own`
  the relaxed exit bridge produces) and the two exit-hypothesis discharges the
  residual induction at n=255 requires:

  * `expExpFinalExitR_of_relaxed` — the live block-3 reload exit, pinned to
    `EvmWord.exp` via the proven `…_exp_regown` bridge.
  * `expExpFinalExitR_of_std` — the (dead) standard exit, vacuous via the base-`a3`
    address collision (`…_collision_false`).
-/
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedResidualInduction
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBlock3ExitExp
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExitVacuous
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoundaryLeftover

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Existential introduction on the precondition of a `cpsTripleWithin`: a triple
    whose precondition is `∃ a, P a` holds iff it holds for every `P a` (with the
    same postcondition).  `**` distributes over `∃` on the left, so the proof just
    re-packs the separating split. -/
theorem cpsTripleWithin_exists_pre
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq} {Q : Assertion}
    {α : Sort _} {P : α → Assertion}
    (h : ∀ a, cpsTripleWithin nSteps entry exit_ cr (P a) Q) :
    cpsTripleWithin nSteps entry exit_ cr (fun s => ∃ a, P a s) Q := by
  intro R hR s hcr hpre hpc
  obtain ⟨hh, hcompat, h1, h2, hdisj, hunion, ⟨a, hPa⟩, hR2⟩ := hpre
  exact h a R hR s hcr ⟨hh, hcompat, h1, h2, hdisj, hunion, hPa, hR2⟩ hpc

/-- The fixed exit post the residual induction targets at n=255: the relaxed exit
    bridge's `FullStackPreFrame` (result pinned to `EvmWord.exp`) together with the
    surrendered leftover registers `L_own`, with the loop-state-dependent scratch
    (`iterCountNew`, the squaring d-scratch `w0..w3`) existentially closed. -/
def expExpFinalExitR (sp evmSp : Word) (baseWord exponentWord : EvmWord)
    (a0 a1 a2 a3 : Word) : Assertion :=
  fun ps => ∃ (icNew w0 w1 w2 w3 : Word),
    (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64) icNew
        ((EvmWord.exp baseWord exponentWord).getLimbN 3)
        ((EvmWord.exp baseWord exponentWord).getLimbN 0)
        ((EvmWord.exp baseWord exponentWord).getLimbN 1)
        ((EvmWord.exp baseWord exponentWord).getLimbN 2)
        ((EvmWord.exp baseWord exponentWord).getLimbN 3)
        (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
        (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
        (expResultWord a0 a1 a2 a3)
        [expResultWord w0 w1 w2 w3, EvmWord.exp baseWord exponentWord]
        (icNew = 0) **
      (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
       regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)) ps

/-- Discharge of the residual induction's `hExitU_relaxed` into `expExpFinalExitR`:
    the proven `…_exp_regown` bridge pins the result to `EvmWord.exp`; we close the
    `iterCountNew`/d-scratch existentials. -/
theorem expExpFinalExitR_of_relaxed
    {e c6 iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {baseWord exponentWord : EvmWord} {ps : PartialState}
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord 255 e)
    (hInv : expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3)
    (h : (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    expExpFinalExitR sp evmSp baseWord exponentWord a0 a1 a2 a3 ps := by
  obtain ⟨w0, w1, w2, w3, hfull⟩ :=
    expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload_to_FullStackPreFrame_exp_regown
      hBase hCursor hInv h
  exact ⟨expTwoMulIterCountNew iterCount, w0, w1, w2, w3, hfull⟩

/-- Discharge of the residual induction's `hExitU` into `expExpFinalExitR`:
    at the n=255 anchor the standard merged exit post is self-contradictory
    (the reload pointer cell aliases base `a3`), so the implication is vacuous. -/
theorem expExpFinalExitR_of_std
    {e c6 iterCount ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base lookahead : Word}
    {baseWord exponentWord : EvmWord} {ps : PartialState}
    (hptr : ptr = evmSp + signExtend12
      (- (16 + 8 * (((255 - 0) / 64 : Nat) : BitVec 12))))
    (h : (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base **
          (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord **
            expTwoMulFixedExpReadPrefix 3 evmSp exponentWord)) ps) :
    expExpFinalExitR sp evmSp baseWord exponentWord a0 a1 a2 a3 ps := by
  obtain ⟨_psA, _psB, _hdisj, _hunion, hMerged, _hB⟩ := h
  have hcol : ptr + signExtend12 (0 : BitVec 12)
      = evmSp + signExtend12 (-40 : BitVec 12) := by
    rw [hptr,
      show (-(16 + 8 * (((255 - 0) / 64 : Nat) : BitVec 12))) = (-40 : BitVec 12)
        from by decide]
    bv_addr
  exact (expTwoMulFixedIterMergedExitPost_collision_false hcol hMerged).elim

/-- STEP A — the residual induction instantiated at `n = 255`: the full
    256-iteration loop body from the first `IterPre` (with `ExpResidual 0`/
    `ExpReadPrefix 0`) to `expExpFinalExitR`.  Both exit hypotheses are
    discharged by the packaged lemmas above. -/
theorem exp_final_loop_hBody
    (base sp evmSp a0 a1 a2 a3 : Word)
    (baseWord exponentWord : EvmWord) (lookahead : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (e c6 iterCount v10 v18 ptr nextLimb tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 : Word)
    (hcount : iterCount.toNat = 255 + 1)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord (255 - 255) e)
    (hControl : expTwoMulFixedControlInvariant exponentWord (255 - 255) c6 ptr
      nextLimb evmSp)
    (hInv : expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - 255)
      r0 r1 r2 r3)
    (hptr : ptr = evmSp + signExtend12
      (- (16 + 8 * (((255 - 255) / 64 : Nat) : BitVec 12)))) :
    cpsTripleWithin ((255 + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
       (expTwoMulFixedExpResidual ((255 - 255) / 64) ptr lookahead exponentWord **
         expTwoMulFixedExpReadPrefix ((255 - 255) / 64) evmSp exponentWord))
      (expExpFinalExitR sp evmSp baseWord exponentWord a0 a1 a2 a3) := by
  refine exp_merged_loop_from_iterpre_residual_induction
    base sp evmSp a0 a1 a2 a3
    (expExpFinalExitR sp evmSp baseWord exponentWord a0 a1 a2 a3)
    baseWord exponentWord lookahead hbase hBase ?_ ?_ 255 (by omega)
    e c6 iterCount v10 v18 ptr nextLimb tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11
    hcount hCursor hControl hInv hptr
  · intro e' c6' iterCount' ptr' nextLimb' r0' r1' r2' r3' ps hptr' h _hcur _hinv
    exact expExpFinalExitR_of_std hptr' h
  · intro e' c6' iterCount' r0' r1' r2' r3' ps h hcur hinv
    exact expExpFinalExitR_of_relaxed hBase hcur hinv h

end EvmAsm.Evm64.Exp.Compose
