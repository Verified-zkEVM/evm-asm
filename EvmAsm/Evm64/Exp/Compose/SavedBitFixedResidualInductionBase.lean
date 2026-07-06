/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedResidualInductionBase

  First half of `EvmAsm.Evm64.Exp.Compose.SavedBitFixedResidualInduction`
  (the canonical-code residual induction), split out to keep each file under
  the file-size guardrail (`scripts/check-file-size.sh`). The parent module
  imports this and re-exports it transitively, so importers are unaffected.

  The `ExpResidual`-threaded merged fixed-x19 EXP loop-body induction.

  Unlike `exp_merged_loop_from_iterpre_induction` (parametric in `c6`, hence
  needing the unprovable pure `MergedReloadReshuffle`), this induction threads
  the exponent residual through the body via the framed step and carries the
  control invariant as a pure side condition, making the reload boundary a pure
  re-partition (using the proven `..._residual_repartition[_*]` lemmas).

  Bounded by `n ≤ 255` so the Nat-subtraction index alignment
  `255 - (k+1) + 1 = 255 - k` holds.
-/

import EvmAsm.Evm64.Exp.Compose.MergedLoopInd
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedMergedFramedStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadResidualRepartition
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Induction
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpReadPrefix

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem exp_merged_loop_from_iterpre_residual_induction
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
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
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
      exp_fixed_loop_body_final_succ_step_framed
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
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
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
              exp_relaxed_block3_loop_induction base sp evmSp a0 a1 a2 a3
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
              exp_relaxed_block3_loop_induction base sp evmSp a0 a1 a2 a3
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
      exp_fixed_loop_body_succ_step_framed
        (k + 1)
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        base R (expTwoMulFixedExpResidual ((255 - (k + 1)) / 64) ptr lookahead exponentWord **
          expTwoMulFixedExpReadPrefix ((255 - (k + 1)) / 64) evmSp exponentWord)
        hbase (pcFree_sepConj expTwoMulFixedExpResidual_pcFree
          expTwoMulFixedExpReadPrefix_pcFree)
        hExit hLoop



end EvmAsm.Evm64.Exp.Compose
