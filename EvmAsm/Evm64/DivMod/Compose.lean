/-
  EvmAsm.Evm64.DivModCompose

  Hierarchical composition of DivMod CPS specs using CodeReq to avoid
  the WHNF scalability limit (25+ instruction atoms in a single theorem type).
  Each composed spec uses `divCode base` as a persistent CodeReq side-condition.
-/

import EvmAsm.Evm64.DivMod.LimbSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Section 1: Program length lemmas (via native_decide)
-- ============================================================================

private theorem divK_phaseA_len : (divK_phaseA 1016).length = 8 := by native_decide
private theorem divK_phaseB_len : divK_phaseB.length = 21 := by native_decide
private theorem divK_clz_len : divK_clz.length = 24 := by native_decide
private theorem divK_phaseC2_len : (divK_phaseC2 172).length = 4 := by native_decide
private theorem divK_normB_len : divK_normB.length = 21 := by native_decide
private theorem divK_normA_len : (divK_normA 40).length = 21 := by native_decide
private theorem divK_copyAU_len : divK_copyAU.length = 9 := by native_decide
private theorem divK_loopSetup_len : (divK_loopSetup 460).length = 4 := by native_decide
private theorem divK_loopBody_len : (divK_loopBody 556 7740).length = 114 := by native_decide
private theorem divK_denorm_len : divK_denorm.length = 25 := by native_decide
private theorem divK_divEpilogue_len : (divK_div_epilogue 24).length = 10 := by native_decide
private theorem divK_zeroPath_len : divK_zeroPath.length = 5 := by native_decide
private theorem divK_nop_len : (ADDI .x0 .x0 0 : Program).length = 1 := by native_decide
private theorem divK_div128_len : divK_div128.length = 49 := by native_decide
private theorem divK_modEpilogue_len : (divK_mod_epilogue 24).length = 10 := by native_decide

/-- Skip one ofProg block in a right-nested union via range disjointness.
    Closes the disjointness goal using block length lemmas + bv_omega. -/
macro "skipBlock" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range _ _ _ _ (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
          divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
          divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
          divK_zeroPath_len, divK_nop_len, divK_div128_len,
          divK_modEpilogue_len] at hk1 hk2
        bv_omega)))

-- ============================================================================
-- Section 4: Full program CodeReq split into per-phase CodeReq.ofProg blocks
-- ============================================================================

/-- The full evm_div code split into 14 per-phase CodeReq.ofProg blocks.
    This is the canonical CodeReq for all composed specs. -/
abbrev divCode (base : Addr) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base (divK_phaseA 1016),             -- block 0
    CodeReq.ofProg (base + 32) divK_phaseB,              -- block 1
    CodeReq.ofProg (base + 116) divK_clz,                -- block 2
    CodeReq.ofProg (base + 212) (divK_phaseC2 172),      -- block 3
    CodeReq.ofProg (base + 228) divK_normB,              -- block 4
    CodeReq.ofProg (base + 312) (divK_normA 40),         -- block 5
    CodeReq.ofProg (base + 396) divK_copyAU,             -- block 6
    CodeReq.ofProg (base + 432) (divK_loopSetup 460),    -- block 7
    CodeReq.ofProg (base + 448) (divK_loopBody 556 7740),-- block 8
    CodeReq.ofProg (base + 904) divK_denorm,             -- block 9
    CodeReq.ofProg (base + 1004) (divK_div_epilogue 24), -- block 10
    CodeReq.ofProg (base + 1044) divK_zeroPath,          -- block 11
    CodeReq.ofProg (base + 1064) (ADDI .x0 .x0 0),      -- block 12
    CodeReq.ofProg (base + 1068) divK_div128             -- block 13
  ]

-- ============================================================================
-- Section 5: CodeReq subsumption lemmas (via mono_unionAll / mono_sub_unionAll)
-- Each sub-spec's CodeReq is subsumed by divCode using structural union reasoning.
-- ============================================================================

/-- Phase A code (8 instructions, block 0) is subsumed by divCode. -/
private theorem divK_phaseA_code_sub_divCode (base : Addr) :
    ∀ a i, (divK_phaseA_code base) a = some i → (divCode base) a = some i := by
  unfold divCode divK_phaseA_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _

/-- Zero path code (5 instructions, block 11) is subsumed by divCode. -/
private theorem divK_zeroPath_code_sub_divCode (base : Addr) :
    ∀ a i, (divK_zeroPath_code (base + 1044)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_zeroPath_code; simp only [CodeReq.unionAll_cons]
  -- Skip blocks 0-10, then match block 11
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- BEQ singleton at base+28 is subsumed by divCode (part of block 0: phaseA). -/
private theorem beq_singleton_sub_divCode (base : Addr) :
    ∀ a i, (CodeReq.singleton (base + 28) (.BEQ .x5 .x0 1016)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  exact CodeReq.union_mono_left _ _ a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1016) 7
      (by native_decide) (by native_decide)) a i h)

/-- Phase B init1 code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_init1_code_sub_divCode (base : Addr) :
    ∀ a i, (divK_phaseB_init1_code (base + 32)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  -- Lift from init1 sub-range to full phaseB block
  have h1 := CodeReq.ofProg_mono_sub (base + 32) (base + 32) divK_phaseB
    (divK_phaseB.take 7) 0
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h
  -- Skip block 0 (phaseA disjoint from phaseB), match block 1
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

/-- Phase B init2 code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_init2_code_sub_divCode (base : Addr) :
    ∀ a i, (divK_phaseB_init2_code (base + 60)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + 32) (base + 60) divK_phaseB
    (divK_phaseB.drop 7 |>.take 2) 7
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

/-- ADDI x5 x0 4 singleton at base+68 (part of block 1: phaseB) is subsumed by divCode. -/
private theorem addi_x5_singleton_sub_divCode (base : Addr) :
    ∀ a i, (CodeReq.singleton (base + 68) (.ADDI .x5 .x0 4)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 9
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 9) = (36 : Addr) from by native_decide,
      show (base + 32 : Addr) + 36 = base + 68 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

/-- BNE x10 x0 24 singleton at base+72 (part of block 1: phaseB) is subsumed by divCode. -/
private theorem bne_x10_singleton_sub_divCode (base : Addr) :
    ∀ a i, (CodeReq.singleton (base + 72) (.BNE .x10 .x0 24)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 10
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 10) = (40 : Addr) from by native_decide,
      show (base + 32 : Addr) + 40 = base + 72 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

/-- Phase B tail code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_tail_code_sub_divCode (base : Addr) :
    ∀ a i, (divK_phaseB_tail_code (base + 96)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + 32) (base + 96) divK_phaseB
    (divK_phaseB.drop 16) 16
    (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- ============================================================================
-- Section 6: signExtend13 normalization
-- ============================================================================

private theorem signExtend13_1016 : signExtend13 (1016 : BitVec 13) = (1016 : Word) := by
  native_decide

private theorem signExtend13_24 : signExtend13 (24 : BitVec 13) = (24 : Word) := by
  native_decide

-- Phase B n=4: signExtend12 4 = 4 (result of ADDI x5 x0 4 via addi_x0_spec_gen)
private theorem divK_se12_4 : signExtend12 (4 : BitVec 12) = (4 : Word) := by native_decide

-- Phase B tail address: nm1_x8 = (4 + signExtend12 4095) <<< 3 = 24
private theorem divK_phaseB_n4_nm1_x8 :
    ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (24 : Word) := by
  native_decide

-- signExtend12 32 = 32 (for tail load address: sp + 24 + signExtend12 32 = sp + 56)
private theorem divK_se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by native_decide

-- Address normalization lemmas for phaseB composition (separate theorems for heartbeat budget)
private theorem phB_off_4 (base : Addr) : (base + 32 : Addr) + 4 = base + 36 := by bv_omega
private theorem phB_off_8 (base : Addr) : (base + 32 : Addr) + 8 = base + 40 := by bv_omega
private theorem phB_off_12 (base : Addr) : (base + 32 : Addr) + 12 = base + 44 := by bv_omega
private theorem phB_off_16 (base : Addr) : (base + 32 : Addr) + 16 = base + 48 := by bv_omega
private theorem phB_off_20 (base : Addr) : (base + 32 : Addr) + 20 = base + 52 := by bv_omega
private theorem phB_off_24 (base : Addr) : (base + 32 : Addr) + 24 = base + 56 := by bv_omega
private theorem phB_off_28 (base : Addr) : (base + 32 : Addr) + 28 = base + 60 := by bv_omega
private theorem phB_i2_4 (base : Addr) : (base + 60 : Addr) + 4 = base + 64 := by bv_omega
private theorem phB_i2_8 (base : Addr) : (base + 60 : Addr) + 8 = base + 68 := by bv_omega
private theorem phB_addi_4 (base : Addr) : (base + 68 : Addr) + 4 = base + 72 := by bv_omega
private theorem phB_bne_4 (base : Addr) : (base + 72 : Addr) + 4 = base + 76 := by bv_omega
private theorem phB_t_4 (base : Addr) : (base + 96 : Addr) + 4 = base + 100 := by bv_omega
private theorem phB_t_8 (base : Addr) : (base + 96 : Addr) + 8 = base + 104 := by bv_omega
private theorem phB_t_12 (base : Addr) : (base + 96 : Addr) + 12 = base + 108 := by bv_omega
private theorem phB_t_16 (base : Addr) : (base + 96 : Addr) + 16 = base + 112 := by bv_omega
private theorem phB_t_20 (base : Addr) : (base + 96 : Addr) + 20 = base + 116 := by bv_omega
private theorem phB_sp24_32 (sp : Addr) : (sp + (24 : Addr) + (32 : Addr)) = sp + 56 := by bv_omega

-- ============================================================================
-- Section 7: Zero path composition (b = 0)
-- Phase A body → BEQ(taken) → zeroPath → exit
-- ============================================================================

set_option maxRecDepth 2048 in
/-- When b = 0 (all limbs zero), evm_div writes zeros and advances sp.
    Execution path: phaseA body (7 instrs), BEQ taken, zeroPath (5 instrs). -/
theorem evm_div_bzero_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbz : b0 ||| b1 ||| b2 ||| b3 = 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  -- Extend to divCode CodeReq
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_divCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid)
  -- Step 2: BEQ at base+28, eliminate ntaken via hbz
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hbz ((sepConj_pure_right _ _ _).mp h_rest).2)
  -- Extend BEQ to divCode CodeReq
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_divCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem (no code atoms needed in frame)
  have hbeq_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(taken): base → base+1044
  have hAB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: ZeroPath (base+1044 → base+1064)
  -- Extend to divCode CodeReq
  have hzp := cpsTriple_extend_code (divK_zeroPath_code_sub_divCode base)
    (divK_zeroPath_spec sp (base + 1044) b0 b1 b2 b3 hvalid)
  rw [show (base + 1044 : Addr) + 20 = base + 1064 from by bv_omega] at hzp
  -- Frame ZP with x5 + x10 + x0
  have hzp_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hzp
  -- Step 6: Compose AB → ZP: base → base+1064
  have hABZ := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hAB hzp_framed
  -- Step 7: Final consequence — rewrite bor → 0
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [hbz] at hq; xperm_hyp hq)
    hABZ

-- ============================================================================
-- Section 8: Phase A not-taken composition (b ≠ 0)
-- Phase A body → BEQ(ntaken) → fall through to Phase B
-- ============================================================================

set_option maxRecDepth 2048 in
/-- When b ≠ 0, evm_div falls through Phase A to Phase B at base+32.
    Execution path: phaseA body (7 instrs), BEQ not taken. -/
theorem evm_div_phaseA_ntaken_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 32) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_divCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid)
  -- Step 2: BEQ at base+28, eliminate taken path (b=0 absurd since hbnz)
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hbnz)
  -- Extend BEQ to divCode CodeReq
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_divCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(ntaken): base → base+32
  have hAB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Final consequence — permute assertions
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

-- ============================================================================
-- Section 9: Phase B composition for n=4 (b[3] ≠ 0)
-- init1 → init2 → ADDI x5=4 → BNE x10(taken) → tail
-- ============================================================================

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 4096 in
/-- Phase B when b[3] ≠ 0 (n=4): zero scratch, load b[1..2], cascade BNE taken, load leading limb.
    Execution path: init1 (7 instrs) + init2 (2) + ADDI (1) + BNE taken (1) + tail (5) = 16 instrs.
    Exit at base+116 (start of CLZ). x5 = b[3] (leading limb), x6 = b[1], x7 = b[2], n = 4. -/
theorem evm_div_phaseB_n4_spec (sp base : Addr)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 n_mem : Word)
    (hb3nz : b3 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true) :
    cpsTriple (base + 32) (base + 116) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ n_mem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  -- ---- Step 1: init1 (base+32 → base+60) — zero q[0..3] and u[5..7]
  have hinit1_raw := divK_phaseB_init1_spec sp (base + 32) q0 q1 q2 q3 u5 u6 u7
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u5 hv_u6 hv_u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- Step 2: init2 (base+60 → base+68) — load b[1], b[2]
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7 hvalid
  simp only [phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_divCode base) hinit2_raw
  have hinit2f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit2
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  -- ---- Step 3: ADDI x5 x0 4 at base+68 → base+72
  have haddi_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, divK_se12_4] at haddi_raw
  have haddi := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi_raw
  have haddif := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 haddif
  -- ---- Step 4: BNE x10 x0 24 at base+72, elim ntaken (b3=0 absurd)
  have hbne_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Addr) + signExtend13 24 = base + 96 from by
        rw [signExtend13_24]; bv_omega, phB_bne_4] at hbne_raw
  have hbne_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb3nz)
  have hbne := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne_clean
  have hbnef := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbnef
  -- ---- Step 5: Tail (base+96 → base+116) — store n=4, load leading limb b[3]
  have hv_limb : isValidDwordAccess
      ((sp + ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat)
       + signExtend12 (32 : BitVec 12)) = true := by
    rw [divK_phaseB_n4_nm1_x8, divK_se12_32, phB_sp24_32]
    exact hvalid.get (show 7 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (4 : Word) b3 n_mem (base + 96) hv_n hv_limb
  simp only [phB_t_20, divK_phaseB_n4_nm1_x8, divK_se12_32, phB_sp24_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  have htailf := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 htailf
  -- ---- Step 6: Final consequence — permute assertions
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

-- ============================================================================
-- Section 10: Phase A + Phase B n=4 composition (b≠0, b[3]≠0)
-- base → base+116 (entry to CLZ)
-- ============================================================================

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 2048 in
/-- When b ≠ 0 and b[3] ≠ 0, evm_div executes Phase A (ntaken) then Phase B (n=4).
    Execution: 8 + 16 = 24 instructions, base → base+116 (start of CLZ).
    Pre/postcondition shapes reflect frame structure from composition. -/
theorem evm_div_phaseAB_n4_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 n_mem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true) :
    cpsTriple base (base + 116) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  have hA := evm_div_phaseA_ntaken_spec sp base b0 b1 b2 b3 v5 v10 hbnz hvalid
  have hAf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
     ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hA
  have hB := evm_div_phaseB_n4_spec sp base b1 b2 b3
    (b0 ||| b1 ||| b2 ||| b3) v6 v7 q0 q1 q2 q3 u5 u6 u7 n_mem
    hb3nz hvalid hv_q0 hv_q1 hv_q2 hv_q3 hv_u5 hv_u6 hv_u7 hv_n
  have hBf := cpsTriple_frame_left _ _ _ _ _
    (((sp + 32) ↦ₘ b0))
    (by pcFree) hB
  have hAB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hAf hBf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

-- ============================================================================
-- Section 11: MOD program code infrastructure
-- ============================================================================

/-- The full evm_mod code split into 14 per-phase CodeReq.ofProg blocks.
    Identical to divCode except block 10 uses divK_mod_epilogue. -/
abbrev modCode (base : Addr) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base (divK_phaseA 1016),
    CodeReq.ofProg (base + 32) divK_phaseB,
    CodeReq.ofProg (base + 116) divK_clz,
    CodeReq.ofProg (base + 212) (divK_phaseC2 172),
    CodeReq.ofProg (base + 228) divK_normB,
    CodeReq.ofProg (base + 312) (divK_normA 40),
    CodeReq.ofProg (base + 396) divK_copyAU,
    CodeReq.ofProg (base + 432) (divK_loopSetup 460),
    CodeReq.ofProg (base + 448) (divK_loopBody 556 7740),
    CodeReq.ofProg (base + 904) divK_denorm,
    CodeReq.ofProg (base + 1004) (divK_mod_epilogue 24),  -- block 10 differs from divCode
    CodeReq.ofProg (base + 1044) divK_zeroPath,
    CodeReq.ofProg (base + 1064) (ADDI .x0 .x0 0),
    CodeReq.ofProg (base + 1068) divK_div128
  ]

-- ============================================================================
-- Section 12: MOD CodeReq subsumption lemmas (via mono_unionAll)
-- ============================================================================

private theorem divK_phaseA_code_sub_modCode (base : Addr) :
    ∀ a i, (divK_phaseA_code base) a = some i → (modCode base) a = some i := by
  unfold modCode divK_phaseA_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _

private theorem divK_zeroPath_code_sub_modCode (base : Addr) :
    ∀ a i, (divK_zeroPath_code (base + 1044)) a = some i → (modCode base) a = some i := by
  unfold modCode divK_zeroPath_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

private theorem beq_singleton_sub_modCode (base : Addr) :
    ∀ a i, (CodeReq.singleton (base + 28) (.BEQ .x5 .x0 1016)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  exact CodeReq.union_mono_left _ _ a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1016) 7
      (by native_decide) (by native_decide)) a i h)

-- ============================================================================
-- Section 13: MOD zero path composition (b = 0)
-- Phase A body → BEQ(taken) → zeroPath → exit
-- ============================================================================

set_option maxRecDepth 2048 in
/-- When b = 0 (all limbs zero), evm_mod writes zeros and advances sp.
    Execution path: phaseA body (7 instrs), BEQ taken, zeroPath (5 instrs). -/
theorem evm_mod_bzero_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbz : b0 ||| b1 ||| b2 ||| b3 = 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 1064) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_modCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid)
  -- Step 2: BEQ at base+28, eliminate ntaken via hbz
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hbz ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_modCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(taken): base → base+1044
  have hAB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: ZeroPath (base+1044 → base+1064)
  have hzp := cpsTriple_extend_code (divK_zeroPath_code_sub_modCode base)
    (divK_zeroPath_spec sp (base + 1044) b0 b1 b2 b3 hvalid)
  rw [show (base + 1044 : Addr) + 20 = base + 1064 from by bv_omega] at hzp
  -- Frame ZP with x5 + x10 + x0
  have hzp_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hzp
  -- Step 6: Compose AB → ZP: base → base+1064
  have hABZ := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hAB hzp_framed
  -- Step 7: Final consequence — rewrite bor → 0
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [hbz] at hq; xperm_hyp hq)
    hABZ

-- ============================================================================
-- Section 14: MOD Phase A not-taken composition (b ≠ 0)
-- ============================================================================

set_option maxRecDepth 2048 in
/-- When b ≠ 0, evm_mod falls through Phase A to Phase B at base+32.
    Execution path: phaseA body (7 instrs), BEQ not taken. -/
theorem evm_mod_phaseA_ntaken_spec (sp base : Addr)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 32) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  -- Step 1: Phase A body (base → base+28, 7 straight-line instructions)
  have hbody := cpsTriple_extend_code (divK_phaseA_code_sub_modCode base)
    (divK_phaseA_body_spec sp base b0 b1 b2 b3 v5 v10 hvalid)
  -- Step 2: BEQ at base+28, eliminate taken path (b=0 absurd since hbnz)
  have hbeq_raw := beq_spec_gen .x5 .x0 1016 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + 28)
  rw [show (base + 28 : Addr) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Addr) + 4 = base + 32 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hbnz)
  have hbeq := cpsTriple_extend_code (beq_singleton_sub_modCode base) hbeq_clean
  -- Step 3: Frame BEQ with regs + mem
  have hbeq_framed := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  -- Step 4: Compose body → BEQ(ntaken): base → base+32
  have hAB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  -- Step 5: Final consequence — permute assertions
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

-- ============================================================================
-- Section 15: div128 subroutine composition (Issue #88)
-- Compose 5 block specs into a single div128_spec theorem.
-- ============================================================================

-- Master subsumption: ofProg (base+1068) divK_div128 ⊆ divCode base
-- Block 13 in divCode's unionAll; skip blocks 0-12.
private theorem divK_div128_ofProg_sub_divCode (base : Addr) :
    ∀ a i, (CodeReq.ofProg (base + 1068) divK_div128) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock
  exact CodeReq.union_mono_left _ _

-- Helper: combine two subsumption proofs over a union.
private theorem CodeReq_union_sub {cr1 cr2 target : CodeReq}
    (h1 : ∀ a i, cr1 a = some i → target a = some i)
    (h2 : ∀ a i, cr2 a = some i → target a = some i) :
    ∀ a i, (cr1.union cr2) a = some i → target a = some i := by
  intro a i h
  simp only [CodeReq.union, Option.orElse] at h
  cases h1a : cr1 a with
  | some j => rw [h1a] at h; simp at h; exact h ▸ h1 a j h1a
  | none => rw [h1a] at h; simp at h; exact h2 a i h

-- Helper: singleton at index k of divK_div128 with explicit instr ⊆ divCode base.
-- Used to prove each singleton in a block's cr is subsumed by divCode.
private theorem d128_sub (base : Addr) (k : Nat) (addr : Addr) (instr : Instr)
    (hk : k < divK_div128.length)
    (h_addr : addr = (base + 1068) + BitVec.ofNat 64 (4 * k))
    (h_instr : divK_div128.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (divCode base) a = some i := by
  subst h_addr; subst h_instr
  exact fun a i h => divK_div128_ofProg_sub_divCode base a i
    (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup (base + 1068) divK_div128 k hk (by native_decide)) a i h)

-- Abbreviation for repeated `by native_decide` / `by bv_omega` calls
-- Each block's subsumption uses: CodeReq_union_sub (d128_sub ...) (CodeReq_union_sub ...)

-- Address normalization: block entry offsets relative to (base + 1068)
private theorem d128_off_40 (base : Addr) : (base + 1068 : Addr) + 40 = base + 1108 := by bv_omega
private theorem d128_off_100 (base : Addr) : (base + 1068 : Addr) + 100 = base + 1168 := by bv_omega
private theorem d128_off_120 (base : Addr) : (base + 1068 : Addr) + 120 = base + 1188 := by bv_omega
private theorem d128_off_180 (base : Addr) : (base + 1068 : Addr) + 180 = base + 1248 := by bv_omega

-- ============================================================================
-- div128_spec: compose 5 block specs into single subroutine theorem.
-- Entry: base+1068, Exit: ret_addr (via JALR), CodeReq: divCode base.
-- ============================================================================

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
theorem div128_spec (sp ret_addr d u_lo u_hi : Word) (base : Addr)
    (v1_old v6_old v11_old : Word)
    (ret_mem d_mem dlo_mem un0_mem : Word)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : (ret_addr + signExtend12 0) &&& ~~~1 = ret_addr) :
    -- Phase 1 intermediates
    let d_hi := d >>> (32 : BitVec 6).toNat
    let d_lo := (d <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let un1 := u_lo >>> (32 : BitVec 6).toNat
    let un0 := (u_lo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    -- Step 1 intermediates
    let q1 := rv64_divu u_hi d_hi
    let rhat := u_hi - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    -- Compute un21 intermediates (x5, x1 values after compute_un21)
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    -- Step 2 intermediates
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    -- End: combine q1' and q0'
    let q := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    cpsTriple (base + 1068) ret_addr (divCode base)
      (-- Precondition: caller registers + scratch memory
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ d) **
       (.x5 ↦ᵣ u_lo) ** (.x7 ↦ᵣ u_hi) **
       (.x6 ↦ᵣ v6_old) ** (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ un0_mem))
      (-- Postcondition: x11=quotient, all regs/mem updated
       (.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ ret_addr) ** (.x10 ↦ᵣ q1') **
       (.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ q0_dlo) **
       (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ rhat2_un0) ** (.x11 ↦ᵣ q) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3968 ↦ₘ ret_addr) **
       (sp + signExtend12 3960 ↦ₘ d) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ un0)) := by
  -- Introduce all let bindings
  intro d_hi; intro d_lo; intro un1; intro un0
  intro q1; intro rhat; intro hi1; intro q1c; intro rhatc
  intro q_dlo; intro rhat_un1; intro q1'; intro rhat'
  intro cu_rhat_un1; intro cu_q1_dlo; intro un21
  intro q0; intro rhat2; intro hi2; intro q0c; intro rhat2c
  intro q0_dlo; intro rhat2_un0; intro q0'
  intro q
  -- ================================================================
  -- Block 1: Phase 1 (base+1068 → base+1108)
  -- Saves ret/d, splits d and u_lo into halves.
  -- ================================================================
  have hph1 := divK_div128_phase1_spec sp ret_addr d u_lo u_hi v1_old v6_old v11_old
    ret_mem d_mem dlo_mem un0_mem (base + 1068) hv_ret hv_d hv_dlo hv_un0
  rw [show (base + 1068 : Addr) + 40 = base + 1108 from by bv_omega] at hph1
  -- Extend phase1 cr to divCode
  have hph1e := cpsTriple_extend_code (hmono := by
    -- phase1 cr: 10 singletons at (base+1068)+{0,4,...,36}, indices 0-9
    exact CodeReq_union_sub (d128_sub base 0 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 1 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 2 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 3 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 4 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 5 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 6 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 7 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 8 _ _ (by native_decide) (by bv_omega) (by native_decide))
      (d128_sub base 9 _ _ (by native_decide) (by bv_omega) (by native_decide)))))))))))
    hph1
  -- Frame phase1 with x0=0 (not used by phase1)
  have hph1f := cpsTriple_frame_left _ _ _ _ _
    (.x0 ↦ᵣ (0 : Word))
    (by pcFree) hph1e
  -- ================================================================
  -- Block 2: Step 1 (base+1108 → base+1168)
  -- Trial division q1, clamp, product check.
  -- ================================================================
  have hst1 := divK_div128_step1_spec sp u_hi d_hi un1 d_lo un0 d d_lo
    (base + 1108) hv_dlo
  rw [show (base + 1108 : Addr) + 60 = base + 1168 from by bv_omega] at hst1
  have hst1e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 10 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 11 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 12 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 13 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 14 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 15 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 16 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 17 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 18 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 19 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 20 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 21 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 22 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 23 _ _ (by native_decide) (by bv_omega) (by native_decide))
      (d128_sub base 24 _ _ (by native_decide) (by bv_omega) (by native_decide))))))))))))))))
    hst1
  -- Frame step1 with x2, mem[3968], mem[3960], mem[3944]
  have hst1f := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hst1e
  -- Compose phase1 → step1
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hph1f hst1f
  -- ================================================================
  -- Block 3: Compute un21 (base+1168 → base+1188)
  -- un21 = rhat*2^32 + un1 - q1*d_lo.
  -- ================================================================
  have hcu := divK_div128_compute_un21_spec sp q1' rhat' un1 rhat_un1 q_dlo d_lo
    (base + 1168) hv_dlo
  rw [show (base + 1168 : Addr) + 20 = base + 1188 from by bv_omega] at hcu
  have hcue := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 25 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 26 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 27 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 28 _ _ (by native_decide) (by bv_omega) (by native_decide))
      (d128_sub base 29 _ _ (by native_decide) (by bv_omega) (by native_decide))))))
    hcu
  -- Frame compute_un21 with x6, x0, x2, mem[3968], mem[3960], mem[3944]
  have hcuf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ d_hi) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x2 ↦ᵣ ret_addr) ** (sp + signExtend12 3968 ↦ₘ ret_addr) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hcue
  -- Compose (phase1→step1) → compute_un21
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 hcuf
  -- ================================================================
  -- Block 4: Step 2 (base+1188 → base+1248)
  -- Trial division q0, clamp, product check.
  -- Params: un21(x7), d_hi(x6), v1_old=cu_q1_dlo(x1),
  --         v5_old=cu_rhat_un1(x5), v11_old=un1(x11),
  --         dlo=d_lo(mem[3952]), un0(mem[3944])
  -- ================================================================
  have hst2 := divK_div128_step2_spec sp un21 d_hi cu_q1_dlo cu_rhat_un1 un1 d_lo un0
    (base + 1188) hv_dlo hv_un0
  rw [show (base + 1188 : Addr) + 60 = base + 1248 from by bv_omega] at hst2
  have hst2e := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 30 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 31 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 32 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 33 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 34 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 35 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 36 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 37 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 38 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 39 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 40 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 41 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 42 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 43 _ _ (by native_decide) (by bv_omega) (by native_decide))
      (d128_sub base 44 _ _ (by native_decide) (by bv_omega) (by native_decide))))))))))))))))
    hst2
  -- Frame step2 with x10, x2, mem[3968], mem[3960]
  have hst2f := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ q1') ** (.x2 ↦ᵣ ret_addr) **
     (sp + signExtend12 3968 ↦ₘ ret_addr) ** (sp + signExtend12 3960 ↦ₘ d))
    (by pcFree) hst2e
  -- Compose (→step1→compute_un21) → step2
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hst2f
  -- ================================================================
  -- Block 5: End (base+1248 → ret_addr via JALR)
  -- Combine q1'|q0' into q, restore return addr, return.
  -- Params: q1=q1'(x10), q0=q0'(x5), v2_old=ret_addr(x2),
  --         v11_old=un0(x11), ret_addr(mem[3968])
  -- ================================================================
  have hend := divK_div128_end_spec sp q1' q0' ret_addr un0 ret_addr
    (base + 1248) hv_ret halign
  have hende := cpsTriple_extend_code (hmono := by
    exact CodeReq_union_sub (d128_sub base 45 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 46 _ _ (by native_decide) (by bv_omega) (by native_decide))
     (CodeReq_union_sub (d128_sub base 47 _ _ (by native_decide) (by bv_omega) (by native_decide))
      (d128_sub base 48 _ _ (by native_decide) (by bv_omega) (by native_decide)))))
    hend
  -- Frame end with x7, x6, x1, x0, mem[3960], mem[3952], mem[3944]
  have hendf := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ q0_dlo) ** (.x6 ↦ᵣ d_hi) ** (.x1 ↦ᵣ rhat2_un0) **
     (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3960 ↦ₘ d) ** (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hende
  -- Compose (→step2) → end
  have h12345 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 hendf
  -- Final permutation to canonical pre/post order
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12345

end EvmAsm.Rv64
