/-
  EvmAsm.Evm64.DivMod.Compose.FullPathV5BzeroMod

  v5 bzero MOD code path (b = 0 → remainder 0), over `modCode_noNop_v5`: phaseA
  detects b=0, the BEQ at phaseABeqOff is taken to zeroPath, which writes 0 to the
  output slots.  MOD mirror of `evm_div_bzero_lane_v5` (Compose/FullPathN1V5Bzero.lean)
  with the phaseA/zeroPath/beq code subsumptions re-pointed at `modCode_noNop_v5`
  (sharedNoNop_v5_b0_mod / b10_mod) and the dispatch post swapped to
  `modStackDispatchPostV5`.  The b=0 path never reaches the epilogue, so the code
  body is identical to the DIV bzero path apart from the code surface.
  Bead `evm-asm-wbc4i.10.3.2.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.PhaseAB
public import EvmAsm.Evm64.DivMod.Compose.V5NoNop
public import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Mod

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem divK_phaseA_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseA_code base) a = some i → (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b0_mod a i (by unfold divK_phaseA_code at h; exact h)

private theorem divK_zeroPath_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_zeroPath_code (base + zeroPathOff)) a = some i → (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b10_mod a i (by unfold divK_zeroPath_code at h; exact h)

private theorem beq_singleton_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseABeqOff) (.BEQ .x5 .x0 1020)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b0_mod a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1020) 7
      (by decide) (by decide)) a i h)

theorem evm_mod_bzero_spec_within_noNop_v5 (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbz : b0 ||| b1 ||| b2 ||| b3 = 0) :
    cpsTripleWithin (8 + 5) base (base + nopOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  have hbody := cpsTripleWithin_extend_code divK_phaseA_code_sub_modCode_noNop_v5
    (divK_phaseA_body_spec_within sp base b0 b1 b2 b3 v5 v10)
  have hbeq_raw := beq_spec_gen_within .x5 .x0 1020
    (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + phaseABeqOff)
  rw [show (base + phaseABeqOff : Word) + signExtend13 1020 = base + zeroPathOff from by rv64_addr,
      show (base + phaseABeqOff : Word) + 4 = base + phaseBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hbz ((sepConj_pure_right _).mp h_rest).2)
  have hbeq := cpsTripleWithin_extend_code beq_singleton_sub_modCode_noNop_v5 hbeq_clean
  have hbeq_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  have hzp := cpsTripleWithin_extend_code divK_zeroPath_code_sub_modCode_noNop_v5
    (divK_zeroPath_spec_within sp (base + zeroPathOff) b0 b1 b2 b3)
  rw [show (base + zeroPathOff : Word) + 20 = base + nopOff from by bv_addr] at hzp
  have hzp_framed := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hzp
  have hABZ := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hzp_framed
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [hbz] at hq; xperm_hyp hq)
    hABZ

/-- v5 no-NOP bzero MOD stack wrapper (evmWordIs form), over `modCode_noNop_v5`. -/
theorem evm_mod_bzero_stack_spec_within_noNop_v5 (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (8 + 5) base (base + nopOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.mod a b)) := by
  subst hbz
  have hg0 := EvmWord.getLimbN_zero 0
  have hg1 := EvmWord.getLimbN_zero 1
  have hg2 := EvmWord.getLimbN_zero 2
  have hg3 := EvmWord.getLimbN_zero 3
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_mod_bzero_spec_within_noNop_v5 sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 := EvmWord.mod_getLimbN_zero_right a 0
  have hr1 := EvmWord.mod_getLimbN_zero_right a 1
  have hr2 := EvmWord.mod_getLimbN_zero_right a 2
  have hr3 := EvmWord.mod_getLimbN_zero_right a 3
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

/-- v5 full-pre bzero MOD dispatcher, over `modCode_noNop_v5`. -/
theorem evm_mod_bzero_stack_spec_within_dispatch_noNop_v5_uni (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_mod_bzero_stack_spec_within_noNop_v5 sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (modCode_noNop_v5 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCall_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun _ hq => by
        dsimp [frame] at hq
        refine modStackDispatchPost_weaken_bzero_frame (sp := sp) (a := a) (b := b)
          (v1 := v1) (v2 := v2) (v6 := v6) (v7 := v7) (v11 := v11)
          (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
          (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
          (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7)
          (shiftMem := shiftMem) (nMem := nMem) (jMem := jMem)
          (retMem := retMem) (dMem := dMem) (dloMem := dloMem)
          (scratch_un0 := scratch_un0) _ ?_
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        exact hq)
      hFramed

/-- The v5 bzero MOD lane, matching `evm_mod_stack_spec_unconditional_of_lanes_v5_mod`:
    from the NoX1 stack-dispatch precondition (plus the `sp+3936` scratch cell) to
    `modStackDispatchPostV5`, over `modCode_noNop_v5`.  Frames the unused `sp+3936`
    cell through the full-pre bzero dispatcher and reconciles the NoX1 vs full
    dispatch-pre shapes (`x1` weakened into the scratch frame). -/
theorem evm_mod_bzero_lane_v5 (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have hw := cpsTripleWithin_frameR ((sp + signExtend12 3936) ↦ₘ scratchMem) (by pcFree)
    (evm_mod_bzero_stack_spec_within_dispatch_noNop_v5_uni sp base a b
      x9Val v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)
  refine cpsTripleWithin_weaken ?_ ?_ hw
  · intro h hp
    rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
    rw [divModStackDispatchPre_unfold, divScratchValuesCall_unfold]
    replace hp := sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x1 (v := raVal))))) h hp
    xperm_hyp hp
  · intro h hq
    delta modStackDispatchPostV5
    exact sepConj_mono_right
      (memIs_implies_memOwn (a := sp + signExtend12 3936) (v := scratchMem)) h hq

end EvmAsm.Evm64
