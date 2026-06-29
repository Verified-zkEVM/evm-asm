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

theorem expExpFinalExitR_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {a0 a1 a2 a3 : Word} :
    (expExpFinalExitR sp evmSp baseWord exponentWord a0 a1 a2 a3).pcFree := by
  intro ps h_post
  unfold expExpFinalExitR at h_post
  obtain ⟨icNew, w0, w1, w2, w3, h_post⟩ := h_post
  exact
    (pcFree_sepConj expTwoMulLoopExitFullStackPreFrame_pcFree (by pcFree))
      ps h_post

instance pcFreeInst_expExpFinalExitR
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (a0 a1 a2 a3 : Word) :
    Assertion.PCFree
      (expExpFinalExitR sp evmSp baseWord exponentWord a0 a1 a2 a3) :=
  ⟨expExpFinalExitR_pcFree⟩

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

/-- STEP E — entry surgery: the `n = 255` loop body, re-expressed over the
    boundary brick's loop-body input surface `FirstIterPre ** FirstIterEntryResidual`
    (with the stack tail `evmStackIs (evmSp + 128) rest` framed through to the post). -/
theorem exp_final_loop_firstIter_hBody
    (base sp evmSp : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    ∀ v10 v7 v11,
      cpsTripleWithin ((255 + 1) * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
          baseWord exponentWord dWord eWord **
         expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
        (expExpFinalExitR sp (evmSp + signExtend12 (64 : BitVec 12))
            baseWord exponentWord
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
          evmStackIs (evmSp + 128) rest) := by
  intro v10 v7 v11
  have hCore := exp_final_loop_hBody base sp (evmSp + signExtend12 (64 : BitVec 12))
    (baseWord.getLimbN 0) (baseWord.getLimbN 1)
    (baseWord.getLimbN 2) (baseWord.getLimbN 3)
    baseWord exponentWord lookahead hbase
    (expResultWord_getLimbN_self baseWord).symm
    (exponentWord.getLimbN 3)
    ((0 : Word) + signExtend12 (64 : BitVec 12))
    (256 : Word)
    v10 v18
    (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
    (exponentWord.getLimbN 2)
    (1 : Word) vOld
    ((1 : EvmWord).getLimbN 0) ((1 : EvmWord).getLimbN 1)
    ((1 : EvmWord).getLimbN 2) ((1 : EvmWord).getLimbN 3)
    (dWord.getLimbN 0) (dWord.getLimbN 1)
    (dWord.getLimbN 2) (dWord.getLimbN 3)
    (eWord.getLimbN 0) (eWord.getLimbN 1)
    (eWord.getLimbN 2) (eWord.getLimbN 3)
    v7 v11
    (by decide)
    (expTwoMulFixedCursorInvariant_zero exponentWord)
    (by
      unfold expTwoMulFixedControlInvariant
      refine ⟨by decide, ?_⟩
      rfl)
    (by
      unfold expTwoMulFixedAccumulatorInvariant
      rw [expResultWord_getLimbN_self, expTwoMulFixedAccumulatorTarget_zero])
    (by
      rw [show (-(16 + 8 * (((255 - 255) / 64 : Nat) : BitVec 12)))
            = (-16 : BitVec 12) from by decide]
      bv_addr)
  have hFramed := cpsTripleWithin_frameR (evmStackIs (evmSp + 128) rest)
    (by pcFree) hCore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [show ((255 - 255) / 64 : Nat) = 0 from rfl]
      rw [expTwoMulFixedFirstIterPre_unfold,
        expTwoMulFixedFirstIterEntryResidual_unfold] at hp
      rw [expTwoMulFixedExpResidual_zero_unfold,
        expTwoMulFixedExpReadPrefix_zero_unfold,
        show ((evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
            + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)
          = evmSp + 40 from by bv_addr,
        show (((evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
            + signExtend12 (-8 : BitVec 12)) + signExtend12 (-8 : BitVec 12))
            + signExtend12 (0 : BitVec 12)
          = evmSp + 32 from by bv_addr,
        show ((evmSp + signExtend12 (64 : BitVec 12)) + signExtend12 (-32 : BitVec 12))
            + 24 = evmSp + 56 from by bv_addr]
      xperm_hyp hp)
    (fun _ hp => hp)
    hFramed

/-- STEP E (cont.) — the loop body over the boundary brick's input surface
    `FirstIterPreWithResidual`, obtained from `exp_final_loop_firstIter_hBody`
    through the existential entry bridge. -/
theorem exp_final_loop_firstIterPreWithResidual
    (base sp evmSp : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest)
      (expExpFinalExitR sp (evmSp + signExtend12 (64 : BitVec 12))
          baseWord exponentWord
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
        evmStackIs (evmSp + 128) rest) :=
  cpsTripleWithin_expTwoMulFixedFirstIterPreWithResidual
    (exp_final_loop_firstIter_hBody base sp evmSp baseWord exponentWord dWord eWord
      rest lookahead vOld v18 hbase)

/-- Folded final-loop post for the EXP first-iteration surface: the semantic
    exit result plus the caller stack tail framed at `evmSp + 128`.

This names the long postcondition produced by the residual induction so the
full EXP wrapper can target a stable assertion instead of repeating the
existential `expExpFinalExitR` spine at every composition step. -/
def expFinalLoopFirstIterPost (sp evmSp : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  expExpFinalExitR sp (evmSp + signExtend12 (64 : BitVec 12))
      baseWord exponentWord
      (baseWord.getLimbN 0) (baseWord.getLimbN 1)
      (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
    evmStackIs (evmSp + 128) rest

theorem expFinalLoopFirstIterPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest =
      (expExpFinalExitR sp (evmSp + signExtend12 (64 : BitVec 12))
          baseWord exponentWord
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
        evmStackIs (evmSp + 128) rest) := by
  delta expFinalLoopFirstIterPost
  rfl

theorem expFinalLoopFirstIterPost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest).pcFree := by
  rw [expFinalLoopFirstIterPost_unfold]
  exact pcFree_sepConj expExpFinalExitR_pcFree pcFree_evmStackIs

instance pcFreeInst_expFinalLoopFirstIterPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest) :=
  ⟨expFinalLoopFirstIterPost_pcFree⟩

/-- Folded-post wrapper for `exp_final_loop_firstIterPreWithResidual`. -/
theorem exp_final_loop_firstIterPreWithResidual_folded
    (base sp evmSp : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest)
      (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest) := by
  rw [expFinalLoopFirstIterPost_unfold]
  exact exp_final_loop_firstIterPreWithResidual
    base sp evmSp baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase

/-- Body-only twin of `exp_final_loop_hBody` (PATH A / arch B): the `n = 255`
    loop body over the loop-body-only code req, so it composes with a custom
    headroom prologue/epilogue (no canonical prologue/epilogue required). -/
theorem exp_final_loop_hBody_bodyonly
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
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
       (expTwoMulFixedExpResidual ((255 - 255) / 64) ptr lookahead exponentWord **
         expTwoMulFixedExpReadPrefix ((255 - 255) / 64) evmSp exponentWord))
      (expExpFinalExitR sp evmSp baseWord exponentWord a0 a1 a2 a3) := by
  refine exp_merged_loop_from_iterpre_residual_induction_bodyonly
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

/-- Body-only twin of `exp_final_loop_firstIter_hBody`. -/
theorem exp_final_loop_firstIter_hBody_bodyonly
    (base sp evmSp : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    ∀ v10 v7 v11,
      cpsTripleWithin ((255 + 1) * 193) (base + 44) (base + 296)
        (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
          baseWord exponentWord dWord eWord **
         expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
        (expExpFinalExitR sp (evmSp + signExtend12 (64 : BitVec 12))
            baseWord exponentWord
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
          evmStackIs (evmSp + 128) rest) := by
  intro v10 v7 v11
  have hCore := exp_final_loop_hBody_bodyonly base sp
    (evmSp + signExtend12 (64 : BitVec 12))
    (baseWord.getLimbN 0) (baseWord.getLimbN 1)
    (baseWord.getLimbN 2) (baseWord.getLimbN 3)
    baseWord exponentWord lookahead hbase
    (expResultWord_getLimbN_self baseWord).symm
    (exponentWord.getLimbN 3)
    ((0 : Word) + signExtend12 (64 : BitVec 12))
    (256 : Word)
    v10 v18
    (evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
    (exponentWord.getLimbN 2)
    (1 : Word) vOld
    ((1 : EvmWord).getLimbN 0) ((1 : EvmWord).getLimbN 1)
    ((1 : EvmWord).getLimbN 2) ((1 : EvmWord).getLimbN 3)
    (dWord.getLimbN 0) (dWord.getLimbN 1)
    (dWord.getLimbN 2) (dWord.getLimbN 3)
    (eWord.getLimbN 0) (eWord.getLimbN 1)
    (eWord.getLimbN 2) (eWord.getLimbN 3)
    v7 v11
    (by decide)
    (expTwoMulFixedCursorInvariant_zero exponentWord)
    (by
      unfold expTwoMulFixedControlInvariant
      refine ⟨by decide, ?_⟩
      rfl)
    (by
      unfold expTwoMulFixedAccumulatorInvariant
      rw [expResultWord_getLimbN_self, expTwoMulFixedAccumulatorTarget_zero])
    (by
      rw [show (-(16 + 8 * (((255 - 255) / 64 : Nat) : BitVec 12)))
            = (-16 : BitVec 12) from by decide]
      bv_addr)
  have hFramed := cpsTripleWithin_frameR (evmStackIs (evmSp + 128) rest)
    (by pcFree) hCore
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [show ((255 - 255) / 64 : Nat) = 0 from rfl]
      rw [expTwoMulFixedFirstIterPre_unfold,
        expTwoMulFixedFirstIterEntryResidual_unfold] at hp
      rw [expTwoMulFixedExpResidual_zero_unfold,
        expTwoMulFixedExpReadPrefix_zero_unfold,
        show ((evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
            + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)
          = evmSp + 40 from by bv_addr,
        show (((evmSp + signExtend12 (56 : BitVec 12) + signExtend12 (-8 : BitVec 12))
            + signExtend12 (-8 : BitVec 12)) + signExtend12 (-8 : BitVec 12))
            + signExtend12 (0 : BitVec 12)
          = evmSp + 32 from by bv_addr,
        show ((evmSp + signExtend12 (64 : BitVec 12)) + signExtend12 (-32 : BitVec 12))
            + 24 = evmSp + 56 from by bv_addr]
      xperm_hyp hp)
    (fun _ hp => hp)
    hFramed

/-- Body-only twin of `exp_final_loop_firstIterPreWithResidual`. -/
theorem exp_final_loop_firstIterPreWithResidual_bodyonly
    (base sp evmSp : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 44) (base + 296)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest)
      (expExpFinalExitR sp (evmSp + signExtend12 (64 : BitVec 12))
          baseWord exponentWord
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3) **
        evmStackIs (evmSp + 128) rest) :=
  cpsTripleWithin_expTwoMulFixedFirstIterPreWithResidual
    (exp_final_loop_firstIter_hBody_bodyonly base sp evmSp baseWord exponentWord
      dWord eWord rest lookahead vOld v18 hbase)

/-- Body-only folded-post wrapper for `exp_final_loop_firstIterPreWithResidual_bodyonly`. -/
theorem exp_final_loop_firstIterPreWithResidual_bodyonly_folded
    (base sp evmSp : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (lookahead vOld v18 : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsTripleWithin ((255 + 1) * 193) (base + 44) (base + 296)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
        baseWord exponentWord dWord eWord rest)
      (expFinalLoopFirstIterPost sp evmSp baseWord exponentWord rest) := by
  rw [expFinalLoopFirstIterPost_unfold]
  exact exp_final_loop_firstIterPreWithResidual_bodyonly
    base sp evmSp baseWord exponentWord dWord eWord rest lookahead vOld v18 hbase

end EvmAsm.Evm64.Exp.Compose
