/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Induction

  The relaxed (block-3) merged fixed-x19 EXP loop-body induction.

  Block 3 (iterations k = 192..255) never reloads except at the final iteration
  k = 255 (which is the loop exit, the base case here).  Its limb pointer `x16`
  has walked into the base-operand region (`x16 = evmSp + se(-40) = ` base `a3`'s
  address), so the standard `IterPre` (with a pointer cell at `x16`) collides
  with base `a3`.  This induction therefore runs over the *relaxed* pre
  `expTwoMulFixedIterPreRelaxedBlock3` (`regOwn`/concrete-`x16`, no separate
  pointer cell) and uses the relaxed engine
  (`exp_fixed_loop_body_succ_step_relaxed_block3_framed` for k = 192..254 and
  `exp_fixed_loop_body_final_succ_step_relaxed_block3_framed` for k = 255), with
  the proven relaxed non-reload re-partitions for the loop-back edge.

  Indexed by `m` (block-3 position): `iterCount.toNat = c6.toNat = m + 1`, with
  `m = 0` the final iteration (k = 255) and `m = 63` the first (k = 192).
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Step
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadResidualRepartition
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCount

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

private theorem c6_add_neg1_toNat {c6 : Word} (h : 1 ≤ c6.toNat) :
    (c6 + signExtend12 (-1 : BitVec 12)).toNat = c6.toNat - 1 := by
  rw [BitVec.toNat_add,
    show (signExtend12 (-1 : BitVec 12)).toNat = 2 ^ 64 - 1 from by decide,
    show c6.toNat + (2 ^ 64 - 1) = (c6.toNat - 1) + 2 ^ 64 from by
      have := c6.isLt; omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by have := c6.isLt; omega)]

private theorem c6_succ_toNat {c6 : Word} {m : Nat} (h : c6.toNat = m + 1 + 1) :
    (c6 + signExtend12 (-1 : BitVec 12)).toNat = m + 1 := by
  rw [c6_add_neg1_toNat (by omega)]; omega

private theorem c6_succ_ne_zero {c6 : Word} {m : Nat} (h : c6.toNat = m + 1 + 1) :
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 := by
  intro hz
  have hn : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by rw [hz]; rfl
  rw [c6_succ_toNat h] at hn
  omega

private theorem c6_zero_eq_zero {c6 : Word} (h : c6.toNat = 0 + 1) :
    c6 + signExtend12 (-1 : BitVec 12) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [c6_add_neg1_toNat (by omega), show (0 : Word).toNat = 0 from rfl]
  omega

/-- The relaxed block-3 merged loop-body induction (conditional on the final
    reload-exit bridge `hExitU`). -/
theorem exp_relaxed_block3_loop_induction
    (base sp evmSp a0 a1 a2 a3 : Word)
    (baseWord exponentWord : EvmWord) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hExitU :
      ∀ (e c6 iterCount r0 r1 r2 r3 : Word) (ps : PartialState),
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base **
          (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)) ps →
        expTwoMulFixedCursorInvariant exponentWord 255 e →
        expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3 →
        R ps)
    (m : Nat) :
    m ≤ 63 →
    ∀ (e c6 iterCount v10 v18 tOld vOld nextLimbCtl
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 : Word),
      iterCount.toNat = m + 1 →
      c6.toNat = m + 1 →
      expTwoMulFixedCursorInvariant exponentWord (255 - m) e →
      expTwoMulFixedControlInvariant exponentWord (255 - m) c6
        (evmSp + signExtend12 (-40 : BitVec 12)) nextLimbCtl evmSp →
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - m)
        r0 r1 r2 r3 →
      cpsTripleWithin ((m + 1) * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPreRelaxedBlock3 e c6 iterCount v10 v18 sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
          (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F))
        R := by
  have hFe :
      (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F).pcFree :=
    pcFree_sepConj pcFree_evmWordIs hF
  induction m with
  | zero =>
    intro _hm e c6 iterCount v10 v18 tOld vOld nextLimbCtl
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount hc6
      hCursor hControl hInv
    have hCursor255 : expTwoMulFixedCursorInvariant exponentWord 255 e := by
      simpa using hCursor
    have hInv255 :
        expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3 := by
      simpa using hInv
    have hzero : expTwoMulIterCountNew iterCount = 0 :=
      expTwoMulIterCountNew_eq_zero_of_toNat_one (by omega)
    have hc6z : c6 + signExtend12 (-1 : BitVec 12) = 0 := c6_zero_eq_zero hc6
    have hfinal :=
      exp_fixed_loop_body_final_succ_step_relaxed_block3_framed
        e c6 iterCount v10 v18 sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        base R (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)
        hc6z hbase hFe hzero
        (fun ps hps => hExitU e c6 iterCount r0 r1 r2 r3 ps hps hCursor255 hInv255)
    rw [show (0 + 1) * 193 = expTwoMulFixedReloadIterStepBound from by
      rw [expTwoMulFixedReloadIterStepBound_eq]]
    refine cpsTripleWithin_weaken ?_ (fun _ h => h) hfinal
    intro ps hp
    dsimp only [expTwoMulFixedIterPreRelaxedBlock3] at hp
    xperm_hyp hp
  | succ m' IH =>
    intro hm e c6 iterCount v10 v18 tOld vOld nextLimbCtl
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount hc6
      hCursor hControl hInv
    have hcountNew : (expTwoMulIterCountNew iterCount).toNat = m' + 1 :=
      expTwoMulIterCountNew_toNat_of_eq_succ hcount
    have hne : expTwoMulIterCountNew iterCount ≠ 0 := by
      intro h; rw [h] at hcountNew; simp at hcountNew
    have hidx : 255 - (m' + 1) + 1 = 255 - m' := by omega
    refine exp_fixed_loop_body_succ_step_relaxed_block3_framed (m' + 1)
      e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      base R (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)
      (c6_succ_ne_zero hc6) hbase hFe ?hExit ?hLoop
    case hExit =>
      intro ps hps
      exfalso
      simp only [expTwoMulFixedIterMergedExitPostRelaxedBlock3] at hps
      obtain ⟨_, _, _, _, hDrf, _⟩ := hps
      obtain ⟨_, _, _, _, hD, _⟩ := hDrf
      rcases hD with hCond | hSkip
      · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hCond
        obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
        obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
        obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
        exact hne hPure.2
      · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hSkip
        obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
        obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
        obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
        exact hne hPure.2
    case hLoop =>
      intro Rframe hRframe s hcr hPR hpc
      obtain ⟨hp, hcompat, psPF, psR, hdisj, hunion, hPF, hRps⟩ := hPR
      obtain ⟨psM, psF, hdMF, huMF, hLP, hFps⟩ := hPF
      simp only [expTwoMulFixedIterMergedLoopPostRelaxedBlock3] at hLP
      obtain ⟨psDisj, psRf, hdDR, huDR, hDisj, hRf⟩ := hLP
      have hResEmp : expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord)
          = empAssertion := expTwoMulFixedExpResidual_ge_two (by omega)
      have hEmp : (expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord) **
          (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)) psF := by
        rw [hResEmp, sepConj_emp_left']; exact hFps
      rcases hDisj with hCond | hSkip
      · have hBitNe :
            e >>> (63 : BitVec 6).toNat + signExtend12 (0 : BitVec 12) ≠ 0 := by
          have hC := hCond
          obtain ⟨_, _, _, _, _, hFrame⟩ := hC
          obtain ⟨_, _, _, _, _, h1⟩ := hFrame
          obtain ⟨_, _, _, _, _, h2⟩ := h1
          obtain ⟨_, _, _, _, _, h3⟩ := h2
          obtain ⟨_, _, _, _, _, hb⟩ := h3
          exact hb.2
        have hAdv :=
          expTwoMulFixedNoReloadInvariants_succ_of_condRw (k := 255 - (m' + 1))
            (by omega) hBase hCursor hControl (c6_succ_ne_zero hc6) hBitNe hInv
        rw [hidx] at hAdv
        obtain ⟨hInv', hCursor', hControl'⟩ := hAdv
        have hInput :
            ((expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
                r0 r1 r2 r3 a0 a1 a2 a3 base
                (expTwoMulIterCountNew iterCount ≠ 0) **
              (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
             (expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord) **
              (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F))) psPF :=
          ⟨psM, psF, hdMF, huMF, ⟨psDisj, psRf, hdDR, huDR, hCond, hRf⟩, hEmp⟩
        obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
          expTwoMulFixedIterSkipCondCountPost_residual_repartition_block3 hInput
        rw [hResEmp, sepConj_emp_left'] at hOut
        exact IH (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
          (c6_succ_toNat hc6) hCursor' hControl' hInv'
          Rframe hRframe s hcr ⟨hp, hcompat, psPF, psR, hdisj, hunion, hOut, hRps⟩ hpc
      · have hBitZero :
            e >>> (63 : BitVec 6).toNat + signExtend12 (0 : BitVec 12) = 0 := by
          have hS := hSkip
          obtain ⟨_, _, _, _, hHR, _⟩ := hS
          obtain ⟨_, _, _, _, _, hSR⟩ := hHR
          obtain ⟨_, _, _, _, _, u1⟩ := hSR
          obtain ⟨_, _, _, _, _, u2⟩ := u1
          obtain ⟨_, _, _, _, _, u3⟩ := u2
          obtain ⟨_, _, _, _, _, u4⟩ := u3
          obtain ⟨_, _, _, _, _, u5⟩ := u4
          obtain ⟨_, _, _, _, _, u6⟩ := u5
          obtain ⟨_, _, _, _, _, u7⟩ := u6
          obtain ⟨_, _, _, _, _, u8⟩ := u7
          obtain ⟨_, _, _, _, _, u9⟩ := u8
          obtain ⟨_, _, _, _, _, u10⟩ := u9
          obtain ⟨_, _, _, _, _, u11⟩ := u10
          obtain ⟨_, _, _, _, _, u12⟩ := u11
          obtain ⟨_, _, _, _, _, u13⟩ := u12
          obtain ⟨_, _, _, _, _, u14⟩ := u13
          obtain ⟨_, _, _, _, _, u15⟩ := u14
          obtain ⟨_, _, _, _, _, u16⟩ := u15
          obtain ⟨_, _, _, _, _, u17⟩ := u16
          obtain ⟨_, h_bit⟩ := ((sepConj_pure_left _).1 u17).2
          exact h_bit
        have hAdv :=
          expTwoMulFixedNoReloadInvariants_succ_of_squareW (k := 255 - (m' + 1))
            (by omega) hCursor hControl (c6_succ_ne_zero hc6) hBitZero hInv
        rw [hidx] at hAdv
        obtain ⟨hInv', hCursor', hControl'⟩ := hAdv
        have hInput :
            ((expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
                r0 r1 r2 r3 a0 a1 a2 a3 base
                (expTwoMulIterCountNew iterCount ≠ 0) **
              (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
             (expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord) **
              (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F))) psPF :=
          ⟨psM, psF, hdMF, huMF, ⟨psDisj, psRf, hdDR, huDR, hSkip, hRf⟩, hEmp⟩
        obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
          expTwoMulFixedIterSkipCountPost_residual_repartition_block3 hInput
        rw [hResEmp, sepConj_emp_left'] at hOut
        exact IH (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
          (c6_succ_toNat hc6) hCursor' hControl' hInv'
          Rframe hRframe s hcr ⟨hp, hcompat, psPF, psR, hdisj, hunion, hOut, hRps⟩ hpc

/-- PATH-A body-only twin of `exp_relaxed_block3_loop_induction`: identical induction
    over the body-only code req, consuming the body-only engine succ_step/final twins. -/
theorem exp_relaxed_block3_loop_induction_bodyonly
    (base sp evmSp a0 a1 a2 a3 : Word)
    (baseWord exponentWord : EvmWord) (R F : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hExitU :
      ∀ (e c6 iterCount r0 r1 r2 r3 : Word) (ps : PartialState),
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base **
          (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)) ps →
        expTwoMulFixedCursorInvariant exponentWord 255 e →
        expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3 →
        R ps)
    (m : Nat) :
    m ≤ 63 →
    ∀ (e c6 iterCount v10 v18 tOld vOld nextLimbCtl
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 : Word),
      iterCount.toNat = m + 1 →
      c6.toNat = m + 1 →
      expTwoMulFixedCursorInvariant exponentWord (255 - m) e →
      expTwoMulFixedControlInvariant exponentWord (255 - m) c6
        (evmSp + signExtend12 (-40 : BitVec 12)) nextLimbCtl evmSp →
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (255 - m)
        r0 r1 r2 r3 →
      cpsTripleWithin ((m + 1) * 193) (base + 44) (base + 296)
        (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPreRelaxedBlock3 e c6 iterCount v10 v18 sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
          (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F))
        R := by
  have hFe :
      (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F).pcFree :=
    pcFree_sepConj pcFree_evmWordIs hF
  induction m with
  | zero =>
    intro _hm e c6 iterCount v10 v18 tOld vOld nextLimbCtl
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount hc6
      hCursor hControl hInv
    have hCursor255 : expTwoMulFixedCursorInvariant exponentWord 255 e := by
      simpa using hCursor
    have hInv255 :
        expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3 := by
      simpa using hInv
    have hzero : expTwoMulIterCountNew iterCount = 0 :=
      expTwoMulIterCountNew_eq_zero_of_toNat_one (by omega)
    have hc6z : c6 + signExtend12 (-1 : BitVec 12) = 0 := c6_zero_eq_zero hc6
    have hfinal :=
      exp_fixed_loop_body_final_succ_step_relaxed_block3_bodyonly_framed
        e c6 iterCount v10 v18 sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        base R (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)
        hc6z hbase hFe hzero
        (fun ps hps => hExitU e c6 iterCount r0 r1 r2 r3 ps hps hCursor255 hInv255)
    rw [show (0 + 1) * 193 = expTwoMulFixedReloadIterStepBound from by
      rw [expTwoMulFixedReloadIterStepBound_eq]]
    refine cpsTripleWithin_weaken ?_ (fun _ h => h) hfinal
    intro ps hp
    dsimp only [expTwoMulFixedIterPreRelaxedBlock3] at hp
    xperm_hyp hp
  | succ m' IH =>
    intro hm e c6 iterCount v10 v18 tOld vOld nextLimbCtl
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount hc6
      hCursor hControl hInv
    have hcountNew : (expTwoMulIterCountNew iterCount).toNat = m' + 1 :=
      expTwoMulIterCountNew_toNat_of_eq_succ hcount
    have hne : expTwoMulIterCountNew iterCount ≠ 0 := by
      intro h; rw [h] at hcountNew; simp at hcountNew
    have hidx : 255 - (m' + 1) + 1 = 255 - m' := by omega
    refine exp_fixed_loop_body_succ_step_relaxed_block3_bodyonly_framed (m' + 1)
      e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      base R (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)
      (c6_succ_ne_zero hc6) hbase hFe ?hExit ?hLoop
    case hExit =>
      intro ps hps
      exfalso
      simp only [expTwoMulFixedIterMergedExitPostRelaxedBlock3] at hps
      obtain ⟨_, _, _, _, hDrf, _⟩ := hps
      obtain ⟨_, _, _, _, hD, _⟩ := hDrf
      rcases hD with hCond | hSkip
      · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hCond
        obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
        obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
        obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
        exact hne hPure.2
      · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hSkip
        obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
        obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
        obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
        exact hne hPure.2
    case hLoop =>
      intro Rframe hRframe s hcr hPR hpc
      obtain ⟨hp, hcompat, psPF, psR, hdisj, hunion, hPF, hRps⟩ := hPR
      obtain ⟨psM, psF, hdMF, huMF, hLP, hFps⟩ := hPF
      simp only [expTwoMulFixedIterMergedLoopPostRelaxedBlock3] at hLP
      obtain ⟨psDisj, psRf, hdDR, huDR, hDisj, hRf⟩ := hLP
      have hResEmp : expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord)
          = empAssertion := expTwoMulFixedExpResidual_ge_two (by omega)
      have hEmp : (expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord) **
          (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F)) psF := by
        rw [hResEmp, sepConj_emp_left']; exact hFps
      rcases hDisj with hCond | hSkip
      · have hBitNe :
            e >>> (63 : BitVec 6).toNat + signExtend12 (0 : BitVec 12) ≠ 0 := by
          have hC := hCond
          obtain ⟨_, _, _, _, _, hFrame⟩ := hC
          obtain ⟨_, _, _, _, _, h1⟩ := hFrame
          obtain ⟨_, _, _, _, _, h2⟩ := h1
          obtain ⟨_, _, _, _, _, h3⟩ := h2
          obtain ⟨_, _, _, _, _, hb⟩ := h3
          exact hb.2
        have hAdv :=
          expTwoMulFixedNoReloadInvariants_succ_of_condRw (k := 255 - (m' + 1))
            (by omega) hBase hCursor hControl (c6_succ_ne_zero hc6) hBitNe hInv
        rw [hidx] at hAdv
        obtain ⟨hInv', hCursor', hControl'⟩ := hAdv
        have hInput :
            ((expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
                r0 r1 r2 r3 a0 a1 a2 a3 base
                (expTwoMulIterCountNew iterCount ≠ 0) **
              (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
             (expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord) **
              (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F))) psPF :=
          ⟨psM, psF, hdMF, huMF, ⟨psDisj, psRf, hdDR, huDR, hCond, hRf⟩, hEmp⟩
        obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
          expTwoMulFixedIterSkipCondCountPost_residual_repartition_block3 hInput
        rw [hResEmp, sepConj_emp_left'] at hOut
        exact IH (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
          (c6_succ_toNat hc6) hCursor' hControl' hInv'
          Rframe hRframe s hcr ⟨hp, hcompat, psPF, psR, hdisj, hunion, hOut, hRps⟩ hpc
      · have hBitZero :
            e >>> (63 : BitVec 6).toNat + signExtend12 (0 : BitVec 12) = 0 := by
          have hS := hSkip
          obtain ⟨_, _, _, _, hHR, _⟩ := hS
          obtain ⟨_, _, _, _, _, hSR⟩ := hHR
          obtain ⟨_, _, _, _, _, u1⟩ := hSR
          obtain ⟨_, _, _, _, _, u2⟩ := u1
          obtain ⟨_, _, _, _, _, u3⟩ := u2
          obtain ⟨_, _, _, _, _, u4⟩ := u3
          obtain ⟨_, _, _, _, _, u5⟩ := u4
          obtain ⟨_, _, _, _, _, u6⟩ := u5
          obtain ⟨_, _, _, _, _, u7⟩ := u6
          obtain ⟨_, _, _, _, _, u8⟩ := u7
          obtain ⟨_, _, _, _, _, u9⟩ := u8
          obtain ⟨_, _, _, _, _, u10⟩ := u9
          obtain ⟨_, _, _, _, _, u11⟩ := u10
          obtain ⟨_, _, _, _, _, u12⟩ := u11
          obtain ⟨_, _, _, _, _, u13⟩ := u12
          obtain ⟨_, _, _, _, _, u14⟩ := u13
          obtain ⟨_, _, _, _, _, u15⟩ := u14
          obtain ⟨_, _, _, _, _, u16⟩ := u15
          obtain ⟨_, _, _, _, _, u17⟩ := u16
          obtain ⟨_, h_bit⟩ := ((sepConj_pure_left _).1 u17).2
          exact h_bit
        have hAdv :=
          expTwoMulFixedNoReloadInvariants_succ_of_squareW (k := 255 - (m' + 1))
            (by omega) hCursor hControl (c6_succ_ne_zero hc6) hBitZero hInv
        rw [hidx] at hAdv
        obtain ⟨hInv', hCursor', hControl'⟩ := hAdv
        have hInput :
            ((expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
                r0 r1 r2 r3 a0 a1 a2 a3 base
                (expTwoMulIterCountNew iterCount ≠ 0) **
              (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
             (expTwoMulFixedExpResidual 3 evmSp (0 : Word) (0 : EvmWord) **
              (evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord ** F))) psPF :=
          ⟨psM, psF, hdMF, huMF, ⟨psDisj, psRf, hdDR, huDR, hSkip, hRf⟩, hEmp⟩
        obtain ⟨v7', v10', v11', d0', d1', d2', d3', hOut⟩ :=
          expTwoMulFixedIterSkipCountPost_residual_repartition_block3 hInput
        rw [hResEmp, sepConj_emp_left'] at hOut
        exact IH (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
          (c6_succ_toNat hc6) hCursor' hControl' hInv'
          Rframe hRframe s hcr ⟨hp, hcompat, psPF, psR, hdisj, hunion, hOut, hRps⟩ hpc

end EvmAsm.Evm64.Exp.Compose
