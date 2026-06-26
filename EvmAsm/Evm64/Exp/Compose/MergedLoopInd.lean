/-
  EvmAsm.Evm64.Exp.Compose.MergedLoopInd

  Nat-indexed induction for the fixed-x19 EXP square-and-multiply loop body,
  via the merged loop-back/exit continuation route.

  The per-iteration step `exp_fixed_loop_body_succ_step` is parametric in the
  within-limb control `c6`, so the loop-back's existential control value is
  threaded without a `control = machine` side condition.  This mirrors the
  proven non-fixed template `exp_loop_from_looppost_induction_general`.

  The reload (64-bit-boundary) loop-back disjuncts are not yet reshuffled into
  the next-iteration `IterPre` shape in the merged formulation, so they are
  taken here as an explicit reshuffle hypothesis `MergedReloadReshuffle`,
  isolating exactly that remaining pure-assertion lemma.  Everything else —
  the non-reload loop-back, the exit, the count threading, and the Nat
  induction — is proven.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostIterPreCases
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCount

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The reload-disjunct reshuffle: at a 64-bit limb boundary, the merged
    loop-back post's reload residual re-enters the next iteration's `IterPre`
    (with reloaded control, advanced pointer, and decremented count).  This is
    a pure assertion entailment — the single remaining merged-route lemma —
    taken here as a hypothesis. -/
abbrev MergedReloadReshuffle (base sp evmSp a0 a1 a2 a3 : Word) : Prop :=
  ∀ (e c6 iterCount ptr nextLimb r0 r1 r2 r3 : Word) (ps : PartialState),
    expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps →
    c6 + signExtend12 (-1 : BitVec 12) = 0 →
    ∃ (e' c6' iterCount' v10' v18' ptr' nextLimb' tOld' vOld'
        r0' r1' r2' r3' d0' d1' d2' d3' e0' e1' e2' e3' v7' v11' : Word),
      expTwoMulFixedIterPre e' c6' iterCount' v10' v18' ptr' nextLimb' sp evmSp
        tOld' vOld' r0' r1' r2' r3' d0' d1' d2' d3' e0' e1' e2' e3'
        a0 a1 a2 a3 v7' v11' ps ∧
      iterCount' = expTwoMulIterCountNew iterCount

/-- Fixed EXP loop body, by Nat induction over the outer iteration count, via
    the merged continuation route.  Conditional on the reload reshuffle and a
    universal exit bridge `hExitU`. -/
theorem exp_merged_loop_from_iterpre_induction
    (base sp evmSp a0 a1 a2 a3 : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hReload : MergedReloadReshuffle base sp evmSp a0 a1 a2 a3)
    (hExitU :
      ∀ (e c6 iterCount ptr nextLimb r0 r1 r2 r3 : Word) (ps : PartialState),
        expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps)
    (n : Nat) :
    ∀ (e c6 iterCount v10 v18 ptr nextLimb tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 : Word),
      iterCount.toNat = n + 1 →
      cpsTripleWithin ((n + 1) * 193)
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11)
        R := by
  induction n with
  | zero =>
    intro e c6 iterCount v10 v18 ptr nextLimb tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount
    have hzero : expTwoMulIterCountNew iterCount = 0 :=
      expTwoMulIterCountNew_eq_zero_of_toNat_one hcount
    exact
      exp_fixed_loop_body_final_succ_step
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        base R hbase hzero (hExitU e c6 iterCount ptr nextLimb r0 r1 r2 r3)
  | succ k IH =>
    intro e c6 iterCount v10 v18 ptr nextLimb tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 hcount
    have hcountNew : (expTwoMulIterCountNew iterCount).toNat = k + 1 :=
      expTwoMulIterCountNew_toNat_of_eq_succ hcount
    have hne : expTwoMulIterCountNew iterCount ≠ 0 := by
      intro h
      rw [h] at hcountNew
      simp at hcountNew
    have hExit :
        ∀ ps,
          expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base ps →
          R ps :=
      exp_fixed_iter_merged_exit_vacuous_bridge hne
    have hLoop :
        cpsTripleWithin ((k + 1) * 193)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base)
          R := by
      intro Rframe hRframe s hcr hPR hpc
      obtain ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hLP, hR_ps⟩ := hPR
      have hCase :
          expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base ps1 := by
        rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost]
        exact hLP
      rcases
          expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame_pures_unframed
            hCase
        with hCond | hRest
      · rcases hCond with ⟨v6, v7', v10', v11', d0', d1', d2', d3', hPre⟩
        exact IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
          Rframe hRframe s hcr ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hPre, hR_ps⟩
          hpc
      · rcases hRest with hSkip | hRest
        · rcases hSkip with ⟨v6, v7', v10', v11', d0', d1', d2', d3', hPre⟩
          exact IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
            Rframe hRframe s hcr
            ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hPre, hR_ps⟩ hpc
        · have hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0 := by
            rcases hRest with hReloadCond | hReloadSkip
            · obtain ⟨_, _, _, _, _, _, _, _, _, _, hc6, _⟩ := hReloadCond
              exact hc6
            · obtain ⟨_, _, _, _, _, _, _, _, _, _, hc6, _⟩ := hReloadSkip
              exact hc6
          obtain ⟨e', c6', iterCount', v10', v18', ptr', nextLimb', tOld',
              vOld', r0', r1', r2', r3', d0', d1', d2', d3', e0', e1', e2',
              e3', v7', v11', hPre, hcount'⟩ :=
            hReload e c6 iterCount ptr nextLimb r0 r1 r2 r3 ps1 hLP hc6
          subst hcount'
          exact IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcountNew
            Rframe hRframe s hcr
            ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hPre, hR_ps⟩ hpc
    exact
      exp_fixed_loop_body_succ_step
        (k + 1)
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        base R hbase hExit hLoop

end EvmAsm.Evm64.Exp.Compose
