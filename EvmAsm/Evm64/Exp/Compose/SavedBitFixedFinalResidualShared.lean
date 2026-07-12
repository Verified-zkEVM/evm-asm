/-
  Shared declaration home for the saved-bit residual induction and final chain.
-/

import EvmAsm.Evm64.Exp.Compose.MergedLoopInd
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedMergedFramedStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadResidualRepartition
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Induction
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpReadPrefix
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedResidualInductionBase
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBlock3ExitExp
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExitVacuous
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoundaryLeftover

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace Exp.Compose

open EvmAsm.Rv64

/-- Body-only-code-req twin of the residual-induction loop spec (path A, bug fjivz). -/
theorem exp_merged_loop_from_iterpre_residual_induction_bodyonly
    (base sp evmSp a0 a1 a2 a3 : Word) (R : Assertion)
    (baseWord exponentWord : EvmWord) (lookahead : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hExitU :
      ∀ (e c6 iterCount ptr nextLimb r0 r1 r2 r3 : Word) (ps : PartialState),
        ptr = evmSp + signExtend12
          (- (16 + 8 * (((255 - 0) / 64 : Nat) : BitVec 12))) →
        (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base **
          (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord **
            expTwoMulFixedExpReadPrefix 3 evmSp exponentWord)) ps →
        expTwoMulFixedCursorInvariant exponentWord 255 e →
        expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3 →
        R ps)
    (hExitU_relaxed :
      ∀ (e c6 iterCount r0 r1 r2 r3 : Word) (ps : PartialState),
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base **
          evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord) ps →
        expTwoMulFixedCursorInvariant exponentWord 255 e →
        expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3 →
        R ps)
    (n : Nat) :
    n ≤ 255 →
    ∀ (e c6 iterCount v10 v18 ptr nextLimb tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 : Word),
      iterCount.toNat = n + 1 →
      expTwoMulFixedCursorInvariant exponentWord (255 - n) e →
      expTwoMulFixedControlInvariant exponentWord (255 - n) c6 ptr
        nextLimb evmSp →
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - n)
        r0 r1 r2 r3 →
      ptr = evmSp + signExtend12
        (- (16 + 8 * (((255 - n) / 64 : Nat) : BitVec 12))) →
      cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
        (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
         (expTwoMulFixedExpResidual ((255 - n) / 64) ptr lookahead exponentWord **
           expTwoMulFixedExpReadPrefix ((255 - n) / 64) evmSp exponentWord))
        R := by
  induction n with
  | zero =>
    intro _hn e c6 iterCount v10 v18 ptr nextLimb tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount hCursor _hControl hInv
      hptrAnchor
    simp only [Nat.sub_zero] at hCursor hInv
    have hzero : expTwoMulIterCountNew iterCount = 0 :=
      expTwoMulIterCountNew_eq_zero_of_toNat_one hcount
    have hb : (255 - 0) / 64 = 3 := by decide
    rw [hb]
    exact
      exp_fixed_loop_body_final_succ_step_framed_bodyonly
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        base R (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord **
          expTwoMulFixedExpReadPrefix 3 evmSp exponentWord)
        hbase (pcFree_sepConj expTwoMulFixedExpResidual_pcFree
          expTwoMulFixedExpReadPrefix_pcFree)
        hzero
        (fun ps hps =>
          hExitU e c6 iterCount ptr nextLimb r0 r1 r2 r3 ps hptrAnchor hps hCursor hInv)
  | succ k IH =>
    intro hn e c6 iterCount v10 v18 ptr nextLimb tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount hCursor hControl hInv
      hptrAnchor
    have hn' : k ≤ 255 := by omega
    have hcountNew : (expTwoMulIterCountNew iterCount).toNat = k + 1 :=
      expTwoMulIterCountNew_toNat_of_eq_succ hcount
    have hne : expTwoMulIterCountNew iterCount ≠ 0 := by
      intro h; rw [h] at hcountNew; simp at hcountNew
    have hExit :
        ∀ ps,
          (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base **
            (expTwoMulFixedExpResidual ((255 - (k + 1)) / 64) ptr lookahead exponentWord **
              expTwoMulFixedExpReadPrefix ((255 - (k + 1)) / 64) evmSp exponentWord)) ps →
          R ps := by
      intro ps hps
      obtain ⟨_, _, _, _, hE, _⟩ := hps
      exact absurd hE (expTwoMulFixedIterMergedExitPost_nonzero_count_false hne)
    have hLoop :
        cpsTripleWithin ((k + 1) * 193) (base + 44) (base + 296)
          (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base **
            (expTwoMulFixedExpResidual ((255 - (k + 1)) / 64) ptr lookahead exponentWord **
              expTwoMulFixedExpReadPrefix ((255 - (k + 1)) / 64) evmSp exponentWord))
          R := by
      intro Rframe hRframe s hcr hPR hpc
      obtain ⟨hp, hcompat, psMF, psR, hdisj, hunion, hMF, hRps⟩ := hPR
      obtain ⟨psM, psF, hdMF, huMF, hLP, hFps⟩ := hMF
      rw [expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLP
      rcases hLP with hSkip | hReload
      · -- Skip (non-reload) loop-back: ((SkipCond ∨ Skip) ** PointerPost) psM
        obtain ⟨psI, psP, hdIP, huIP, hInner, hPtr⟩ := hSkip
        rcases hInner with hSC | hSk
        · -- SkipCond branch
          obtain ⟨_, hC6, hBit⟩ := expTwoMulFixedIterSkipCondCountPost_pures hSC
          have hMod := expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
          have hbk : (255 - k) / 64 = (255 - (k + 1)) / 64 := by omega
          have hControlNext :
              expTwoMulFixedControlInvariant exponentWord (255 - k)
                (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp := by
            have h := expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
            rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
          have hCursorNext :
              expTwoMulFixedCursorInvariant exponentWord (255 - k)
                (e <<< (1 : BitVec 6).toNat) := by
            have h := expTwoMulFixedCursorInvariant_succ_of_control_no_reload
              hCursor hControl hC6
            rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
          have hInvNext :
              expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - k)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) := by
            have h := expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
              (by omega : 255 - (k + 1) < 256) hBase hCursor hBit hInv
            rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
          have hInput :
              ((expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
                  r0 r1 r2 r3 a0 a1 a2 a3 base
                  (expTwoMulIterCountNew iterCount ≠ 0) **
                expTwoMulFixedIterPointerPost ptr nextLimb) **
               (expTwoMulFixedExpResidual ((255 - (k + 1)) / 64) ptr lookahead
                  exponentWord **
                expTwoMulFixedExpReadPrefix ((255 - (k + 1)) / 64) evmSp exponentWord)) psMF :=
            ⟨psM, psF, hdMF, huMF, ⟨psI, psP, hdIP, huIP, hSC, hPtr⟩, hFps⟩
          obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
            expTwoMulFixedIterSkipCondCountPost_residual_repartition hInput
          rw [← hbk] at hOut
          exact IH hn' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
            hCursorNext hControlNext hInvNext (by rw [show (255 - k) / 64 = (255 - (k + 1)) / 64 from by omega]; exact hptrAnchor) Rframe hRframe s hcr
            ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩ hpc
        · -- Skip branch
          obtain ⟨_, hC6, hBit⟩ := expTwoMulFixedIterSkipCountPost_pures hSk
          have hMod := expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
          have hbk : (255 - k) / 64 = (255 - (k + 1)) / 64 := by omega
          have hControlNext :
              expTwoMulFixedControlInvariant exponentWord (255 - k)
                (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp := by
            have h := expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
            rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
          have hCursorNext :
              expTwoMulFixedCursorInvariant exponentWord (255 - k)
                (e <<< (1 : BitVec 6).toNat) := by
            have h := expTwoMulFixedCursorInvariant_succ_of_control_no_reload
              hCursor hControl hC6
            rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
          have hInvNext :
              expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - k)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
            have h := expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
              (by omega : 255 - (k + 1) < 256) hCursor hBit hInv
            rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
          have hInput :
              ((expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
                  r0 r1 r2 r3 a0 a1 a2 a3 base
                  (expTwoMulIterCountNew iterCount ≠ 0) **
                expTwoMulFixedIterPointerPost ptr nextLimb) **
               (expTwoMulFixedExpResidual ((255 - (k + 1)) / 64) ptr lookahead
                  exponentWord **
                expTwoMulFixedExpReadPrefix ((255 - (k + 1)) / 64) evmSp exponentWord)) psMF :=
            ⟨psM, psF, hdMF, huMF, ⟨psI, psP, hdIP, huIP, hSk, hPtr⟩, hFps⟩
          obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
            expTwoMulFixedIterSkipCountPost_residual_repartition hInput
          rw [← hbk] at hOut
          exact IH hn' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
            hCursorNext hControlNext hInvNext (by rw [show (255 - k) / 64 = (255 - (k + 1)) / 64 from by omega]; exact hptrAnchor) Rframe hRframe s hcr
            ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩ hpc
      · -- Reload loop-back: (ReloadCond ∨ ReloadSkip) psM  (no PointerPost wrapper)
        rcases hReload with hRC | hRS
        · -- ReloadCond branch
          obtain ⟨_, hC6, hBit⟩ := expTwoMulFixedIterReloadCondCountPost_pures hRC
          have hMod : (255 - (k + 1)) % 64 = 63 :=
            expTwoMulFixedControlInvariant_reload_mod hControl hC6
          rcases expTwoMulFixedReloadBlock_cases hMod (by omega) with hb0 | hb1 | hb2
          · -- block 0 → 1
            have hbk : (255 - k) / 64 = 1 := by omega
            have hc64 : ((0 : Word) + signExtend12 (64 : BitVec 12)) = (64 : Word) := by
              decide
            have hControlNext :
                expTwoMulFixedControlInvariant exponentWord (255 - k)
                  ((0 : Word) + signExtend12 (64 : BitVec 12))
                  (ptr + signExtend12 (-8 : BitVec 12))
                  (exponentWord.getLimbN 1) evmSp := by
              rw [hc64]
              have h := expTwoMulFixedControlInvariant_succ_reload hControl hC6
                (nextNextLimb := exponentWord.getLimbN 1)
                (by rw [show (255 - (k + 1)) + 1 = 255 - k from by omega, hbk])
              have hidx : (255 - (k + 1)) + 1 = 255 - k := by omega
              rwa [hidx] at h
            have hCursorNext :
                expTwoMulFixedCursorInvariant exponentWord (255 - k) nextLimb := by
              have h := expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            have hInvNext :
                expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - k)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) := by
              have h := expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
                (by omega : 255 - (k + 1) < 256) hBase hCursor hBit hInv
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            rw [hb0] at hFps
            have hnl : nextLimb = exponentWord.getLimbN 2 := by
              have h2 := hControl; unfold expTwoMulFixedControlInvariant at h2
              rw [hb0] at h2; simpa using h2.2
            have hInput :
                (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb
                    sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
                    (expTwoMulIterCountNew iterCount ≠ 0) **
                 (expTwoMulFixedExpResidual 0 ptr lookahead exponentWord **
                    expTwoMulFixedExpReadPrefix 0 evmSp exponentWord)) psMF :=
              ⟨psM, psF, hdMF, huMF, hRC, hFps⟩
            obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
              expTwoMulFixedIterReloadCondCountPost_residual_repartition_zero hInput
            rw [show ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
                  = (((evmSp + signExtend12 (-32 : BitVec 12)) + 16) ↦ₘ
                      exponentWord.getLimbN 2) from by
                    rw [hnl, show (ptr + signExtend12 (0 : BitVec 12))
                      = ((evmSp + signExtend12 (-32 : BitVec 12)) + 16) from by
                        rw [hb0] at hptrAnchor; rw [hptrAnchor]; bv_addr],
              sepConj_left_comm'
                (((evmSp + signExtend12 (-32 : BitVec 12)) + 16) ↦ₘ
                  exponentWord.getLimbN 2)
                (expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
                  lookahead exponentWord)
                (expTwoMulFixedExpReadPrefix 0 evmSp exponentWord),
              ← expTwoMulFixedExpReadPrefix_succ_zero] at hOut
            exact
              IH hn'
                nextLimb ((0 : Word) + signExtend12 (64 : BitVec 12))
                (expTwoMulIterCountNew iterCount) v10'
                ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
                (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
                (((base + 44) + 140) + 68)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
                d0' d1' d2' d3'
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
                v7' v11' hcountNew hCursorNext hControlNext hInvNext
                (by rw [hb0] at hptrAnchor; rw [hbk]; rw [hptrAnchor]; bv_addr)
                Rframe hRframe s hcr
                (by rw [hbk]
                    exact ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩) hpc
          · -- block 1 → 2
            have hbk : (255 - k) / 64 = 2 := by omega
            have hc64 : ((0 : Word) + signExtend12 (64 : BitVec 12)) = (64 : Word) := by decide
            have hControlNext :
                expTwoMulFixedControlInvariant exponentWord (255 - k)
                  ((0 : Word) + signExtend12 (64 : BitVec 12))
                  (ptr + signExtend12 (-8 : BitVec 12))
                  (exponentWord.getLimbN 0) evmSp := by
              rw [hc64]
              have h := expTwoMulFixedControlInvariant_succ_reload hControl hC6
                (nextNextLimb := exponentWord.getLimbN 0)
                (by rw [show (255 - (k + 1)) + 1 = 255 - k from by omega, hbk])
              rwa [show (255 - (k + 1)) + 1 = 255 - k from by omega] at h
            have hCursorNext :
                expTwoMulFixedCursorInvariant exponentWord (255 - k) nextLimb := by
              have h := expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            have hInvNext :
                expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - k)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) := by
              have h := expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
                (by omega : 255 - (k + 1) < 256) hBase hCursor hBit hInv
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            rw [hb1] at hFps
            have hnl : nextLimb = exponentWord.getLimbN 1 := by
              have h2 := hControl; unfold expTwoMulFixedControlInvariant at h2
              rw [hb1] at h2; simpa using h2.2
            have hInput :
                (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
                    (expTwoMulIterCountNew iterCount ≠ 0) **
                 (expTwoMulFixedExpResidual 1 ptr lookahead exponentWord **
                    expTwoMulFixedExpReadPrefix 1 evmSp exponentWord)) psMF :=
              ⟨psM, psF, hdMF, huMF, hRC, hFps⟩
            obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
              expTwoMulFixedIterReloadCondCountPost_residual_repartition_one hInput
            rw [show ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
                  = (((evmSp + signExtend12 (-32 : BitVec 12)) + 8) ↦ₘ
                      exponentWord.getLimbN 1) from by
                    rw [hnl, show (ptr + signExtend12 (0 : BitVec 12))
                      = ((evmSp + signExtend12 (-32 : BitVec 12)) + 8) from by
                        rw [hb1] at hptrAnchor; rw [hptrAnchor]; bv_addr],
              sepConj_left_comm'
                (((evmSp + signExtend12 (-32 : BitVec 12)) + 8) ↦ₘ
                  exponentWord.getLimbN 1)
                (expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
                  lookahead exponentWord)
                (expTwoMulFixedExpReadPrefix 1 evmSp exponentWord),
              ← expTwoMulFixedExpReadPrefix_succ_one] at hOut
            exact
              IH hn' nextLimb ((0 : Word) + signExtend12 (64 : BitVec 12))
                (expTwoMulIterCountNew iterCount) v10'
                ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
                (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 0)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) (((base + 44) + 140) + 68)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
                d0' d1' d2' d3'
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
                v7' v11' hcountNew hCursorNext hControlNext hInvNext
                (by rw [hb1] at hptrAnchor; rw [hbk]; rw [hptrAnchor]; bv_addr)
                Rframe hRframe s hcr
                (by rw [hbk]
                    exact ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩) hpc
          · -- block 2 → 3 : hand off to the relaxed block-3 induction
            have hc64 : ((0 : Word) + signExtend12 (64 : BitVec 12)) = (64 : Word) := by decide
            have hptr : ptr + signExtend12 (-8 : BitVec 12)
                = evmSp + signExtend12 (-40 : BitVec 12) := by
              rw [hb2] at hptrAnchor; rw [hptrAnchor]; bv_addr
            have hControl192 :
                expTwoMulFixedControlInvariant exponentWord (255 - 63)
                  ((0 : Word) + signExtend12 (64 : BitVec 12))
                  (evmSp + signExtend12 (-40 : BitVec 12))
                  (exponentWord.getLimbN (2 - (255 - 63) / 64)) evmSp := by
              rw [hc64, ← hptr]
              have h := expTwoMulFixedControlInvariant_succ_reload hControl hC6
                (nextNextLimb := exponentWord.getLimbN (2 - (255 - 63) / 64))
                (by rw [show (255 - (k + 1)) + 1 = 255 - 63 from by omega])
              rwa [show (255 - (k + 1)) + 1 = 255 - 63 from by omega] at h
            have hCursor192 :
                expTwoMulFixedCursorInvariant exponentWord (255 - 63) nextLimb := by
              have h := expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6
              rwa [show 255 - (k + 1) + 1 = 255 - 63 from by omega] at h
            have hInv192 :
                expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - 63)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
                  ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) := by
              have h := expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
                (by omega : 255 - (k + 1) < 256) hBase hCursor hBit hInv
              rwa [show 255 - (k + 1) + 1 = 255 - 63 from by omega] at h
            rw [hb2] at hFps
            have hnl : nextLimb = exponentWord.getLimbN 0 := by
              have h2 := hControl; unfold expTwoMulFixedControlInvariant at h2
              rw [hb2] at h2; simpa using h2.2
            have hInput :
                (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
                    (expTwoMulIterCountNew iterCount ≠ 0) **
                 (expTwoMulFixedExpResidual 2 ptr lookahead exponentWord **
                    expTwoMulFixedExpReadPrefix 2 evmSp exponentWord)) psMF :=
              ⟨psM, psF, hdMF, huMF, hRC, hFps⟩
            obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
              expTwoMulFixedIterReloadCondCountPost_residual_repartition_two hptr hInput
            rw [show ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
                  = ((evmSp + signExtend12 (-32 : BitVec 12)) ↦ₘ
                      exponentWord.getLimbN 0) from by
                    rw [hnl, show (ptr + signExtend12 (0 : BitVec 12))
                      = (evmSp + signExtend12 (-32 : BitVec 12)) from by
                        rw [hb2] at hptrAnchor; rw [hptrAnchor]; bv_addr],
              ← expTwoMulFixedExpReadPrefix_succ_two,
              expTwoMulFixedExpReadPrefix_three_eq_evmWordIs (le_refl 3),
              ← sepConj_emp_right'
                (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord)] at hOut
            have hFull : ((_ : Assertion) ** Rframe).holdsFor s :=
              ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩
            obtain ⟨kk, hkk, s', hstep', hpc', hH⟩ :=
              exp_relaxed_block3_loop_induction_bodyonly base sp evmSp a0 a1 a2 a3
                baseWord exponentWord R
                empAssertion
                hbase pcFree_emp hBase
                (fun e' c6' ic' r0' r1' r2' r3' ps hps hc hi =>
                  hExitU_relaxed e' c6' ic' r0' r1' r2' r3' ps
                    (by rw [sepConj_emp_right'] at hps; exact hps) hc hi)
                63 (by omega)
                nextLimb ((0 : Word) + signExtend12 (64 : BitVec 12))
                (expTwoMulIterCountNew iterCount) v10'
                ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3) (((base + 44) + 140) + 68)
                (exponentWord.getLimbN (2 - (255 - 63) / 64))
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
                d0' d1' d2' d3'
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
                ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2) ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
                v7' v11'
                (by rw [hcountNew]; omega) (by rw [hc64]; decide)
                hCursor192 hControl192 hInv192
                Rframe hRframe s hcr hFull hpc
            exact ⟨kk, by rw [show k + 1 = 64 from by omega]; exact hkk, s', hstep', hpc', hH⟩
        · -- ReloadSkip branch
          obtain ⟨_, hC6, hBit⟩ := expTwoMulFixedIterReloadSkipCountPost_pures hRS
          have hMod : (255 - (k + 1)) % 64 = 63 :=
            expTwoMulFixedControlInvariant_reload_mod hControl hC6
          rcases expTwoMulFixedReloadBlock_cases hMod (by omega) with hb0 | hb1 | hb2
          · -- block 0 → 1
            have hbk : (255 - k) / 64 = 1 := by omega
            have hc64 : ((0 : Word) + signExtend12 (64 : BitVec 12)) = (64 : Word) := by decide
            have hControlNext :
                expTwoMulFixedControlInvariant exponentWord (255 - k)
                  ((0 : Word) + signExtend12 (64 : BitVec 12))
                  (ptr + signExtend12 (-8 : BitVec 12))
                  (exponentWord.getLimbN 1) evmSp := by
              rw [hc64]
              have h := expTwoMulFixedControlInvariant_succ_reload hControl hC6
                (nextNextLimb := exponentWord.getLimbN 1)
                (by rw [show (255 - (k + 1)) + 1 = 255 - k from by omega, hbk])
              rwa [show (255 - (k + 1)) + 1 = 255 - k from by omega] at h
            have hCursorNext :
                expTwoMulFixedCursorInvariant exponentWord (255 - k) nextLimb := by
              have h := expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            have hInvNext :
                expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - k)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
              have h := expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
                (by omega : 255 - (k + 1) < 256) hCursor hBit hInv
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            rw [hb0] at hFps
            have hnl : nextLimb = exponentWord.getLimbN 2 := by
              have h2 := hControl; unfold expTwoMulFixedControlInvariant at h2
              rw [hb0] at h2; simpa using h2.2
            have hInput :
                (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
                    (expTwoMulIterCountNew iterCount ≠ 0) **
                 (expTwoMulFixedExpResidual 0 ptr lookahead exponentWord **
                    expTwoMulFixedExpReadPrefix 0 evmSp exponentWord)) psMF :=
              ⟨psM, psF, hdMF, huMF, hRS, hFps⟩
            obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
              expTwoMulFixedIterReloadSkipCountPost_residual_repartition_zero hInput
            rw [show ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
                  = (((evmSp + signExtend12 (-32 : BitVec 12)) + 16) ↦ₘ
                      exponentWord.getLimbN 2) from by
                    rw [hnl, show (ptr + signExtend12 (0 : BitVec 12))
                      = ((evmSp + signExtend12 (-32 : BitVec 12)) + 16) from by
                        rw [hb0] at hptrAnchor; rw [hptrAnchor]; bv_addr],
              sepConj_left_comm'
                (((evmSp + signExtend12 (-32 : BitVec 12)) + 16) ↦ₘ
                  exponentWord.getLimbN 2)
                (expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
                  lookahead exponentWord)
                (expTwoMulFixedExpReadPrefix 0 evmSp exponentWord),
              ← expTwoMulFixedExpReadPrefix_succ_zero] at hOut
            exact
              IH hn' nextLimb ((0 : Word) + signExtend12 (64 : BitVec 12))
                (expTwoMulIterCountNew iterCount) v10'
                ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
                (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) (((base + 44) + 32) + 68)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
                d0' d1' d2' d3'
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
                v7' v11' hcountNew hCursorNext hControlNext hInvNext
                (by rw [hb0] at hptrAnchor; rw [hbk]; rw [hptrAnchor]; bv_addr)
                Rframe hRframe s hcr
                (by rw [hbk]
                    exact ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩) hpc
          · -- block 1 → 2
            have hbk : (255 - k) / 64 = 2 := by omega
            have hc64 : ((0 : Word) + signExtend12 (64 : BitVec 12)) = (64 : Word) := by decide
            have hControlNext :
                expTwoMulFixedControlInvariant exponentWord (255 - k)
                  ((0 : Word) + signExtend12 (64 : BitVec 12))
                  (ptr + signExtend12 (-8 : BitVec 12))
                  (exponentWord.getLimbN 0) evmSp := by
              rw [hc64]
              have h := expTwoMulFixedControlInvariant_succ_reload hControl hC6
                (nextNextLimb := exponentWord.getLimbN 0)
                (by rw [show (255 - (k + 1)) + 1 = 255 - k from by omega, hbk])
              rwa [show (255 - (k + 1)) + 1 = 255 - k from by omega] at h
            have hCursorNext :
                expTwoMulFixedCursorInvariant exponentWord (255 - k) nextLimb := by
              have h := expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            have hInvNext :
                expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - k)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
              have h := expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
                (by omega : 255 - (k + 1) < 256) hCursor hBit hInv
              rwa [show 255 - (k + 1) + 1 = 255 - k from by omega] at h
            rw [hb1] at hFps
            have hnl : nextLimb = exponentWord.getLimbN 1 := by
              have h2 := hControl; unfold expTwoMulFixedControlInvariant at h2
              rw [hb1] at h2; simpa using h2.2
            have hInput :
                (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
                    (expTwoMulIterCountNew iterCount ≠ 0) **
                 (expTwoMulFixedExpResidual 1 ptr lookahead exponentWord **
                    expTwoMulFixedExpReadPrefix 1 evmSp exponentWord)) psMF :=
              ⟨psM, psF, hdMF, huMF, hRS, hFps⟩
            obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
              expTwoMulFixedIterReloadSkipCountPost_residual_repartition_one hInput
            rw [show ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
                  = (((evmSp + signExtend12 (-32 : BitVec 12)) + 8) ↦ₘ
                      exponentWord.getLimbN 1) from by
                    rw [hnl, show (ptr + signExtend12 (0 : BitVec 12))
                      = ((evmSp + signExtend12 (-32 : BitVec 12)) + 8) from by
                        rw [hb1] at hptrAnchor; rw [hptrAnchor]; bv_addr],
              sepConj_left_comm'
                (((evmSp + signExtend12 (-32 : BitVec 12)) + 8) ↦ₘ
                  exponentWord.getLimbN 1)
                (expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
                  lookahead exponentWord)
                (expTwoMulFixedExpReadPrefix 1 evmSp exponentWord),
              ← expTwoMulFixedExpReadPrefix_succ_one] at hOut
            exact
              IH hn' nextLimb ((0 : Word) + signExtend12 (64 : BitVec 12))
                (expTwoMulIterCountNew iterCount) v10'
                ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
                (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 0)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) (((base + 44) + 32) + 68)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
                d0' d1' d2' d3'
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
                v7' v11' hcountNew hCursorNext hControlNext hInvNext
                (by rw [hb1] at hptrAnchor; rw [hbk]; rw [hptrAnchor]; bv_addr)
                Rframe hRframe s hcr
                (by rw [hbk]
                    exact ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩) hpc
          · -- block 2 → 3 : hand off to the relaxed block-3 induction
            have hc64 : ((0 : Word) + signExtend12 (64 : BitVec 12)) = (64 : Word) := by decide
            have hptr : ptr + signExtend12 (-8 : BitVec 12)
                = evmSp + signExtend12 (-40 : BitVec 12) := by
              rw [hb2] at hptrAnchor; rw [hptrAnchor]; bv_addr
            have hControl192 :
                expTwoMulFixedControlInvariant exponentWord (255 - 63)
                  ((0 : Word) + signExtend12 (64 : BitVec 12))
                  (evmSp + signExtend12 (-40 : BitVec 12))
                  (exponentWord.getLimbN (2 - (255 - 63) / 64)) evmSp := by
              rw [hc64, ← hptr]
              have h := expTwoMulFixedControlInvariant_succ_reload hControl hC6
                (nextNextLimb := exponentWord.getLimbN (2 - (255 - 63) / 64))
                (by rw [show (255 - (k + 1)) + 1 = 255 - 63 from by omega])
              rwa [show (255 - (k + 1)) + 1 = 255 - 63 from by omega] at h
            have hCursor192 :
                expTwoMulFixedCursorInvariant exponentWord (255 - 63) nextLimb := by
              have h := expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6
              rwa [show 255 - (k + 1) + 1 = 255 - 63 from by omega] at h
            have hInv192 :
                expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - 63)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
                  ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
              have h := expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
                (by omega : 255 - (k + 1) < 256) hCursor hBit hInv
              rwa [show 255 - (k + 1) + 1 = 255 - 63 from by omega] at h
            rw [hb2] at hFps
            have hnl : nextLimb = exponentWord.getLimbN 0 := by
              have h2 := hControl; unfold expTwoMulFixedControlInvariant at h2
              rw [hb2] at h2; simpa using h2.2
            have hInput :
                (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
                    (expTwoMulIterCountNew iterCount ≠ 0) **
                 (expTwoMulFixedExpResidual 2 ptr lookahead exponentWord **
                    expTwoMulFixedExpReadPrefix 2 evmSp exponentWord)) psMF :=
              ⟨psM, psF, hdMF, huMF, hRS, hFps⟩
            obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
              expTwoMulFixedIterReloadSkipCountPost_residual_repartition_two hptr hInput
            rw [show ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
                  = ((evmSp + signExtend12 (-32 : BitVec 12)) ↦ₘ
                      exponentWord.getLimbN 0) from by
                    rw [hnl, show (ptr + signExtend12 (0 : BitVec 12))
                      = (evmSp + signExtend12 (-32 : BitVec 12)) from by
                        rw [hb2] at hptrAnchor; rw [hptrAnchor]; bv_addr],
              ← expTwoMulFixedExpReadPrefix_succ_two,
              expTwoMulFixedExpReadPrefix_three_eq_evmWordIs (le_refl 3),
              ← sepConj_emp_right'
                (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord)] at hOut
            have hFull : ((_ : Assertion) ** Rframe).holdsFor s :=
              ⟨hp, hcompat, psMF, psR, hdisj, hunion, hOut, hRps⟩
            obtain ⟨kk, hkk, s', hstep', hpc', hH⟩ :=
              exp_relaxed_block3_loop_induction_bodyonly base sp evmSp a0 a1 a2 a3
                baseWord exponentWord R
                empAssertion
                hbase pcFree_emp hBase
                (fun e' c6' ic' r0' r1' r2' r3' ps hps hc hi =>
                  hExitU_relaxed e' c6' ic' r0' r1' r2' r3' ps
                    (by rw [sepConj_emp_right'] at hps; exact hps) hc hi)
                63 (by omega)
                nextLimb ((0 : Word) + signExtend12 (64 : BitVec 12))
                (expTwoMulIterCountNew iterCount) v10'
                ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) (((base + 44) + 32) + 68)
                (exponentWord.getLimbN (2 - (255 - 63) / 64))
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
                d0' d1' d2' d3'
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
                ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2) ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
                v7' v11'
                (by rw [hcountNew]; omega) (by rw [hc64]; decide)
                hCursor192 hControl192 hInv192
                Rframe hRframe s hcr hFull hpc
            exact ⟨kk, by rw [show k + 1 = 64 from by omega]; exact hkk, s', hstep', hpc', hH⟩
    exact
      exp_fixed_loop_body_succ_step_framed_bodyonly
        (k + 1)
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        base R (expTwoMulFixedExpResidual ((255 - (k + 1)) / 64) ptr lookahead exponentWord **
          expTwoMulFixedExpReadPrefix ((255 - (k + 1)) / 64) evmSp exponentWord)
        hbase (pcFree_sepConj expTwoMulFixedExpResidual_pcFree
          expTwoMulFixedExpReadPrefix_pcFree)
        hExit hLoop

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

end Exp.Compose
end EvmAsm.Evm64
