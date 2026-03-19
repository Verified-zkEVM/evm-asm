/-
  EvmAsm.Evm64.DivModCompose

  Hierarchical composition of DivMod CPS specs using CodeReq to avoid
  the WHNF scalability limit (25+ instruction atoms in a single theorem type).
  Each composed spec uses `divCode base` as a persistent CodeReq side-condition.
-/

import EvmAsm.Evm64.DivModSpec

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

set_option maxHeartbeats 1600000 in
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
set_option maxHeartbeats 12800000 in
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
set_option maxHeartbeats 12800000 in
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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 51200000 in
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

set_option maxRecDepth 2048 in
set_option maxHeartbeats 25600000 in
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

set_option maxHeartbeats 1600000 in
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
set_option maxHeartbeats 12800000 in
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
set_option maxHeartbeats 12800000 in
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

end EvmAsm.Rv64
