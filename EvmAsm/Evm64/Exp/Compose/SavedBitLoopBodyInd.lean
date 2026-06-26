/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopBodyInd

  Abstract n-step loop body induction for the two-MUL saved-bit EXP loop.

  The key theorem `exp_loop_from_looppost_induction` proves:
    cpsTripleWithin (n * 189) (base+28) (base+264) code
      (expTwoMulIterLoopPost (↑n) ...) loopExitPre
  by induction on n, using:
  - `expTwoMulIterLoopPost_to_iterPre` (bridge: loopPost → iterPre)
  - `exp_loop_body_succ_step` (peel one iteration from iterPre)
  - `exp_loop_body_zero_step_vacuous` (base: loopPost 0 is False)
  - `exp_loop_exit_vacuous_bridge` (non-final exits are vacuous)
  Bead evm-asm-w5mk.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitIterBridges

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- `(signExtend12 (-1 : BitVec 12)).toNat = 2^64 - 1` (the max 64-bit value). -/
private theorem signExtend12_neg1_toNat :
    (signExtend12 ((-1 : BitVec 12))).toNat = 2^64 - 1 := by decide

/-- After one decrement, toNat drops by 1 (no underflow since iterCount > 0). -/
private theorem expTwoMulIterCountNew_toNat {iterCount : Word} {k : Nat}
    (h : iterCount.toNat = k + 1) :
    (expTwoMulIterCountNew iterCount).toNat = k := by
  simp only [expTwoMulIterCountNew]
  rw [BitVec.toNat_add, signExtend12_neg1_toNat, h]
  have hlt : k + 1 < 2^64 := by rw [← h]; exact iterCount.isLt
  omega

/-- When iterCount.toNat = k+1 and k ≥ 1, iterCountNew ≠ 0. -/
private theorem expTwoMulIterCountNew_ne_zero_of_toNat_pos {iterCount : Word} {k : Nat}
    (hnat : iterCount.toNat = k + 1) (hk : 0 < k) :
    expTwoMulIterCountNew iterCount ≠ 0 := by
  intro h
  have h0 : (expTwoMulIterCountNew iterCount).toNat = 0 := by simp [h]
  rw [expTwoMulIterCountNew_toNat hnat] at h0
  omega

/-- When iterCount.toNat = 1, iterCountNew = 0 (final exit). -/
private theorem expTwoMulIterCountNew_eq_zero_of_toNat_one {iterCount : Word}
    (hnat : iterCount.toNat = 1) :
    expTwoMulIterCountNew iterCount = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [expTwoMulIterCountNew_toNat (show iterCount.toNat = 0 + 1 from by omega)]

/-- Abstract n-step loop body spec from `expTwoMulIterLoopPost`.

    Starting from `loopPost iterCount ...` with `iterCount.toNat = n` and
    `iterCount ≠ 0`, running the loop body for `n * 189` steps reaches
    `expTwoMulLoopExitPre`.  The caller supplies:
    - `hExitUniv`: the exit bridge for the final iteration (iterCountNew = 0)
    - `hbase`: the code-base alignment invariant

    This theorem is the `hTail` ingredient for
    `exp_two_mul_full_loop_boundary_of_entry_tail_exit_cases_spec_within`
    when instantiated at n = 255 (255-step tail after the first peel). -/
theorem exp_loop_from_looppost_induction
    (n : Nat)
    (bit sp evmSp base a0 a1 a2 a3 : Word)
    (squarW rwW : EvmWord)
    (iterCount : Word)
    (hne : iterCount ≠ 0)
    (hnat : iterCount.toNat = n)
    (hbase : base &&& 1 = 0)
    (iterCountFinal tOld out0 out1 out2 out3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hExitUniv : ∀ (bit0 : Word) (squarW0 rwW0 : EvmWord) (ps : PartialState),
        expTwoMulIterExitPost 0 bit0 sp evmSp base a0 a1 a2 a3 squarW0 rwW0 ps →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond ps) :
    cpsTripleWithin (n * 189) (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost iterCount bit sp evmSp base a0 a1 a2 a3 squarW rwW)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  induction n generalizing bit squarW rwW iterCount with
  | zero =>
    -- n = 0: iterCount = 0 contradicts hne
    exact absurd (BitVec.eq_of_toNat_eq (by simp [hnat])) hne
  | succ k IH =>
    -- n = k + 1
    have h_icn_toNat : (expTwoMulIterCountNew iterCount).toNat = k :=
      expTwoMulIterCountNew_toNat (by omega)
    -- Work at the raw cpsTripleWithin level to avoid elaboration issues
    intro R hR s hcr hLR hpc
    obtain ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hLP, hR_ps⟩ := hLR
    -- Bridge: loopPost ps1 → ∃ iterPre values, iterPre ... ps1
    obtain ⟨e', v18', vOld', r0', r1', r2', r3', d0, d1, d2, d3,
            e0', e1', e2', e3', hPre⟩ :=
      expTwoMulIterLoopPost_to_iterPre hne hLP
    -- Reconstruct (iterPre ** R).holdsFor s with the same split
    have hPR' : ((expTwoMulIterPre e' iterCount v18' sp evmSp vOld'
        r0' r1' r2' r3' d0 d1 d2 d3 e0' e1' e2' e3' a0 a1 a2 a3) ** R).holdsFor s :=
      ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hPre, hR_ps⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · -- k = 0, n = 1: final iteration; iterCountNew = 0
      have h_icn_zero : expTwoMulIterCountNew iterCount = 0 :=
        expTwoMulIterCountNew_eq_zero_of_toNat_one (by omega)
      -- hExit: the real final exit bridge
      have hExit : ∀ ps,
          expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3) ps →
          expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
            baseWord rest exitCond ps := by
        rw [h_icn_zero]
        exact hExitUniv (expTwoMulIterBit e') (expTwoMulSquareW r0' r1' r2' r3')
          (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3)
      -- hLoop0: vacuous (loopPost 0 is False)
      have hLoop0 : cpsTripleWithin (0 * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3))
          (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
            baseWord rest exitCond) := by
        rw [h_icn_zero]; exact exp_loop_body_zero_step_vacuous
      have hSpec : cpsTripleWithin ((0 + 1) * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterPre e' iterCount v18' sp evmSp vOld'
            r0' r1' r2' r3' d0 d1 d2 d3 e0' e1' e2' e3' a0 a1 a2 a3)
          (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
            baseWord rest exitCond) :=
        exp_loop_body_succ_step 0 e' iterCount v18' sp evmSp vOld'
          r0' r1' r2' r3' d0 d1 d2 d3 e0' e1' e2' e3' a0 a1 a2 a3
          iterCountFinal tOld out0 out1 out2 out3
          base baseWord rest exitCond hbase hExit hLoop0
      exact hSpec R hR s hcr hPR' hpc
    · -- k ≥ 1: iterCountNew ≠ 0, use IH for the remaining iterations
      have h_icn_ne : expTwoMulIterCountNew iterCount ≠ 0 :=
        expTwoMulIterCountNew_ne_zero_of_toNat_pos (by omega) hk_pos
      -- hExit: vacuous (iterCountNew ≠ 0 → exitPost is False)
      have hExit : ∀ ps,
          expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3) ps →
          expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
            baseWord rest exitCond ps :=
        exp_loop_exit_vacuous_bridge h_icn_ne
      -- hLoop: apply IH with the next-iteration values
      have hLoop : cpsTripleWithin (k * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3))
          (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
            baseWord rest exitCond) :=
        IH (expTwoMulIterBit e') (expTwoMulSquareW r0' r1' r2' r3')
          (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount)
          h_icn_ne h_icn_toNat
      have hSpec : cpsTripleWithin ((k + 1) * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterPre e' iterCount v18' sp evmSp vOld'
            r0' r1' r2' r3' d0 d1 d2 d3 e0' e1' e2' e3' a0 a1 a2 a3)
          (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
            baseWord rest exitCond) :=
        exp_loop_body_succ_step k e' iterCount v18' sp evmSp vOld'
          r0' r1' r2' r3' d0 d1 d2 d3 e0' e1' e2' e3' a0 a1 a2 a3
          iterCountFinal tOld out0 out1 out2 out3
          base baseWord rest exitCond hbase hExit hLoop
      exact hSpec R hR s hcr hPR' hpc

/-- Abstract successor step for the generalized loop body target.

    This is the `exp_loop_body_succ_step` shape specialized to the
    full-stack loop-exit pre-frame used by the generalized EXP boundary proof. -/
private theorem exp_loop_body_succ_step_general
    (n : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      exitD0 exitD1 exitD2 exitD3 : Word)
    (base : Word) (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hExit : ∀ ps,
        expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) ps →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 exitD0 exitD1 exitD2 exitD3 baseWord rest exitCond ps)
    (hLoop : cpsTripleWithin (n * 189) (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 exitD0 exitD1 exitD2 exitD3 baseWord rest exitCond)) :
    cpsTripleWithin ((n + 1) * 189) (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
        out0 out1 out2 out3 exitD0 exitD1 exitD2 exitD3 baseWord rest exitCond) := by
  rw [← expTwoMulIterationsBodyBound_eq n] at hLoop
  rw [← expTwoMulIterationsBodyBound_eq (n + 1)]
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (expTwoMulNamedIterStepBound_add_max_iterationsBodyBound_zero_le_succ n)
      hLoop
      (cpsTripleWithin_extend_code
        (hmono := by
          intro a i h
          cases h)
        (cpsTripleWithin_refl hExit))

/-- Generalized n-step loop body spec from `expTwoMulIterLoopPost`.

    This mirrors `exp_loop_from_looppost_induction`, but targets
    `expTwoMulLoopExitFullStackPreFrame` with independent stack payload
    limbs `d0..d3`.  It is the induction ingredient for the generalized EXP
    boundary theorem, where the exit stack still contains the original
    exponent limbs until the epilogue overwrites them with the result. -/
theorem exp_loop_from_looppost_induction_general
    (n : Nat)
    (bit sp evmSp base a0 a1 a2 a3 : Word)
    (squarW rwW : EvmWord)
    (iterCount : Word)
    (hne : iterCount ≠ 0)
    (hnat : iterCount.toNat = n)
    (hbase : base &&& 1 = 0)
    (iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hExitUniv : ∀ (bit0 : Word) (squarW0 rwW0 : EvmWord) (ps : PartialState),
        expTwoMulIterExitPost 0 bit0 sp evmSp base a0 a1 a2 a3 squarW0 rwW0 ps →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond ps) :
    cpsTripleWithin (n * 189) (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost iterCount bit sp evmSp base a0 a1 a2 a3 squarW rwW)
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
        out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) := by
  induction n generalizing bit squarW rwW iterCount with
  | zero =>
    exact absurd (BitVec.eq_of_toNat_eq (by simp [hnat])) hne
  | succ k IH =>
    have h_icn_toNat : (expTwoMulIterCountNew iterCount).toNat = k :=
      expTwoMulIterCountNew_toNat (by omega)
    intro R hR s hcr hLR hpc
    obtain ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hLP, hR_ps⟩ := hLR
    obtain ⟨e', v18', vOld', r0', r1', r2', r3', d0', d1', d2', d3',
            e0', e1', e2', e3', hPre⟩ :=
      expTwoMulIterLoopPost_to_iterPre hne hLP
    have hPR' : ((expTwoMulIterPre e' iterCount v18' sp evmSp vOld'
        r0' r1' r2' r3' d0' d1' d2' d3' e0' e1' e2' e3' a0 a1 a2 a3) ** R).holdsFor s :=
      ⟨hp, hcompat, ps1, ps2, hdisj, hunion, hPre, hR_ps⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · have h_icn_zero : expTwoMulIterCountNew iterCount = 0 :=
        expTwoMulIterCountNew_eq_zero_of_toNat_one (by omega)
      have hExit : ∀ ps,
          expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3) ps →
          expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
            out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond ps := by
        rw [h_icn_zero]
        exact hExitUniv (expTwoMulIterBit e') (expTwoMulSquareW r0' r1' r2' r3')
          (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3)
      have hLoop0 : cpsTripleWithin (0 * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3))
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
            out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) := by
        rw [h_icn_zero]; exact exp_loop_body_zero_step_vacuous
      have hSpec : cpsTripleWithin ((0 + 1) * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterPre e' iterCount v18' sp evmSp vOld'
            r0' r1' r2' r3' d0' d1' d2' d3' e0' e1' e2' e3' a0 a1 a2 a3)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
            out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) :=
        exp_loop_body_succ_step_general 0 e' iterCount v18' sp evmSp vOld'
          r0' r1' r2' r3' d0' d1' d2' d3' e0' e1' e2' e3' a0 a1 a2 a3
          iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3
          base baseWord rest exitCond hbase hExit hLoop0
      exact hSpec R hR s hcr hPR' hpc
    · have h_icn_ne : expTwoMulIterCountNew iterCount ≠ 0 :=
        expTwoMulIterCountNew_ne_zero_of_toNat_pos (by omega) hk_pos
      have hExit : ∀ ps,
          expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3) ps →
          expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
            out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond ps :=
        exp_loop_exit_vacuous_bridge h_icn_ne
      have hLoop : cpsTripleWithin (k * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
            (expTwoMulIterBit e') sp evmSp base a0 a1 a2 a3
            (expTwoMulSquareW r0' r1' r2' r3')
            (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3))
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
            out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) :=
        IH (expTwoMulIterBit e') (expTwoMulSquareW r0' r1' r2' r3')
          (expTwoMulIterRw r0' r1' r2' r3' a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount)
          h_icn_ne h_icn_toNat
      have hSpec : cpsTripleWithin ((k + 1) * 189) (base + 28) (base + 264)
          (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
          (expTwoMulIterPre e' iterCount v18' sp evmSp vOld'
            r0' r1' r2' r3' d0' d1' d2' d3' e0' e1' e2' e3' a0 a1 a2 a3)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
            out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) :=
        exp_loop_body_succ_step_general k e' iterCount v18' sp evmSp vOld'
          r0' r1' r2' r3' d0' d1' d2' d3' e0' e1' e2' e3' a0 a1 a2 a3
          iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3
          base baseWord rest exitCond hbase hExit hLoop
      exact hSpec R hR s hcr hPR' hpc

/-- Concrete 256-iteration loop body spec starting from the loop-**entry**
    pre-state `expTwoMulIterPre` (counter `256`).

    Unlike `exp_loop_from_looppost_full_body_general_spec_within` (which starts
    from the loop-**back** post `expTwoMulIterLoopPost 256`, only reachable
    *after* the first iteration has run), this starts from `expTwoMulIterPre` —
    the state the prologue actually hands to the loop head at `base + 28`.  It
    peels the first iteration with `exp_loop_body_succ_step_general` and runs the
    remaining 255 via `exp_loop_from_looppost_induction_general`.

    This is the body spec whose precondition the prologue's `loopEntryPost` can
    bridge into by a pure separation-logic reshuffle (the analog of the fixed
    path's `expTwoMulLoopEntryPostFixed_to_firstIterPre`), avoiding the
    structurally-impossible `loopEntryPost → loopBackPost` bridge. -/
theorem exp_loop_from_iterpre_full_body_general_spec_within
    (e v18 sp evmSp vOld r0 r1 r2 r3 preD0 preD1 preD2 preD3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hExitUniv : ∀ (bit0 : Word) (squarW0 rwW0 : EvmWord) (ps : PartialState),
        expTwoMulIterExitPost 0 bit0 sp evmSp base a0 a1 a2 a3 squarW0 rwW0 ps →
        expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond ps) :
    cpsTripleWithin (256 * 189) (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e (256 : Word) v18 sp evmSp vOld r0 r1 r2 r3
        preD0 preD1 preD2 preD3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
        out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) := by
  have hsucc : (256 : Word).toNat = 255 + 1 := by decide
  have h_icn_toNat : (expTwoMulIterCountNew (256 : Word)).toNat = 255 :=
    expTwoMulIterCountNew_toNat hsucc
  have h_icn_ne : expTwoMulIterCountNew (256 : Word) ≠ 0 :=
    expTwoMulIterCountNew_ne_zero_of_toNat_pos hsucc (by omega)
  have hLoop :
      cpsTripleWithin (255 * 189) (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew (256 : Word))
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountFinal tOld
          out0 out1 out2 out3 d0 d1 d2 d3 baseWord rest exitCond) :=
    exp_loop_from_looppost_induction_general 255
      (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
      (expTwoMulSquareW r0 r1 r2 r3)
      (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
      (expTwoMulIterCountNew (256 : Word)) h_icn_ne h_icn_toNat hbase
      iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3
      baseWord rest exitCond hExitUniv
  have hStep :=
    exp_loop_body_succ_step_general 255 e (256 : Word) v18 sp evmSp vOld
      r0 r1 r2 r3 preD0 preD1 preD2 preD3 e0 e1 e2 e3 a0 a1 a2 a3
      iterCountFinal tOld out0 out1 out2 out3 d0 d1 d2 d3
      base baseWord rest exitCond hbase
      (exp_loop_exit_vacuous_bridge h_icn_ne) hLoop
  simpa using hStep

end EvmAsm.Evm64.Exp.Compose
