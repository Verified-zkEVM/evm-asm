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
abbrev divCode (base : Word) : CodeReq :=
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
private theorem divK_phaseA_code_sub_divCode (base : Word) :
    ∀ a i, (divK_phaseA_code base) a = some i → (divCode base) a = some i := by
  unfold divCode divK_phaseA_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _

/-- Zero path code (5 instructions, block 11) is subsumed by divCode. -/
private theorem divK_zeroPath_code_sub_divCode (base : Word) :
    ∀ a i, (divK_zeroPath_code (base + 1044)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_zeroPath_code; simp only [CodeReq.unionAll_cons]
  -- Skip blocks 0-10, then match block 11
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- BEQ singleton at base+28 is subsumed by divCode (part of block 0: phaseA). -/
private theorem beq_singleton_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 28) (.BEQ .x5 .x0 1016)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  exact CodeReq.union_mono_left _ _ a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1016) 7
      (by native_decide) (by native_decide)) a i h)

/-- Phase B init1 code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_init1_code_sub_divCode (base : Word) :
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
private theorem divK_phaseB_init2_code_sub_divCode (base : Word) :
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
private theorem addi_x5_singleton_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 68) (.ADDI .x5 .x0 4)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 9
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 9) = (36 : Word) from by native_decide,
      show (base + 32 : Word) + 36 = base + 68 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

/-- BNE x10 x0 24 singleton at base+72 (part of block 1: phaseB) is subsumed by divCode. -/
private theorem bne_x10_singleton_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 72) (.BNE .x10 .x0 24)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 10
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 10) = (40 : Word) from by native_decide,
      show (base + 32 : Word) + 40 = base + 72 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

/-- Phase B tail code (ofProg sub-range of block 1) is subsumed by divCode. -/
private theorem divK_phaseB_tail_code_sub_divCode (base : Word) :
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
private theorem phB_off_4 (base : Word) : (base + 32 : Word) + 4 = base + 36 := by bv_omega
private theorem phB_off_8 (base : Word) : (base + 32 : Word) + 8 = base + 40 := by bv_omega
private theorem phB_off_12 (base : Word) : (base + 32 : Word) + 12 = base + 44 := by bv_omega
private theorem phB_off_16 (base : Word) : (base + 32 : Word) + 16 = base + 48 := by bv_omega
private theorem phB_off_20 (base : Word) : (base + 32 : Word) + 20 = base + 52 := by bv_omega
private theorem phB_off_24 (base : Word) : (base + 32 : Word) + 24 = base + 56 := by bv_omega
private theorem phB_off_28 (base : Word) : (base + 32 : Word) + 28 = base + 60 := by bv_omega
private theorem phB_i2_4 (base : Word) : (base + 60 : Word) + 4 = base + 64 := by bv_omega
private theorem phB_i2_8 (base : Word) : (base + 60 : Word) + 8 = base + 68 := by bv_omega
private theorem phB_addi_4 (base : Word) : (base + 68 : Word) + 4 = base + 72 := by bv_omega
private theorem phB_bne_4 (base : Word) : (base + 72 : Word) + 4 = base + 76 := by bv_omega
private theorem phB_t_4 (base : Word) : (base + 96 : Word) + 4 = base + 100 := by bv_omega
private theorem phB_t_8 (base : Word) : (base + 96 : Word) + 8 = base + 104 := by bv_omega
private theorem phB_t_12 (base : Word) : (base + 96 : Word) + 12 = base + 108 := by bv_omega
private theorem phB_t_16 (base : Word) : (base + 96 : Word) + 16 = base + 112 := by bv_omega
private theorem phB_t_20 (base : Word) : (base + 96 : Word) + 20 = base + 116 := by bv_omega
private theorem phB_sp24_32 (sp : Word) : (sp + (24 : Word) + (32 : Word)) = sp + 56 := by bv_omega

-- ============================================================================
-- Section 6b: Opaque memory bundle for phaseB invariant cells
-- These 7 memory cells are zeroed by init1 and stay zero throughout phaseB.
-- Bundling them reduces the atom count for xperm matching.
-- ============================================================================

/-- The 7 memory cells zeroed by phaseB init1 (q[0..3] + u[5..7]).
    Marked @[irreducible] so xperm treats this as 1 opaque atom, not 7. -/
@[irreducible]
def phaseB_zeroed_mem (sp : Word) : Assertion :=
  ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word))

/-- Fold 7 individual memory-zero assertions into the opaque bundle. -/
theorem phaseB_zeroed_mem_fold (sp : Word) :
    (((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word))) = phaseB_zeroed_mem sp := by
  delta phaseB_zeroed_mem; rfl

/-- Unfold the opaque bundle back to 7 individual assertions. -/
theorem phaseB_zeroed_mem_unfold (sp : Word) :
    phaseB_zeroed_mem sp =
    (((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word))) := by
  delta phaseB_zeroed_mem; rfl

-- ============================================================================
-- Section 7: Zero path composition (b = 0)
-- Phase A body → BEQ(taken) → zeroPath → exit
-- ============================================================================

set_option maxRecDepth 2048 in
/-- When b = 0 (all limbs zero), evm_div writes zeros and advances sp.
    Execution path: phaseA body (7 instrs), BEQ taken, zeroPath (5 instrs). -/
theorem evm_div_bzero_spec (sp base : Word)
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
  rw [show (base + 28 : Word) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbeq_raw
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
  rw [show (base + 1044 : Word) + 20 = base + 1064 from by bv_omega] at hzp
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
theorem evm_div_phaseA_ntaken_spec (sp base : Word)
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
  rw [show (base + 28 : Word) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbeq_raw
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
theorem evm_div_phaseB_n4_spec (sp base : Word)
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
  seqFrame hinit1f hinit2
  -- ---- Step 3: ADDI x5 x0 4 at base+68 → base+72
  have haddi_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, divK_se12_4] at haddi_raw
  have haddi := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi_raw
  seqFrame hinit1fhinit2 haddi
  -- ---- Step 4: BNE x10 x0 24 at base+72, elim ntaken (b3=0 absurd)
  have hbne_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rw [signExtend13_24]; bv_omega, phB_bne_4] at hbne_raw
  have hbne_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb3nz)
  have hbne := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne_clean
  seqFrame hinit1fhinit2haddi hbne
  -- ---- Step 5: Tail (base+96 → base+116) — store n=4, load leading limb b[3]
  have hv_limb : isValidDwordAccess
      ((sp + ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat)
       + signExtend12 (32 : BitVec 12)) = true := by
    rw [divK_phaseB_n4_nm1_x8, divK_se12_32, phB_sp24_32]
    exact hvalid.get (show 7 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (4 : Word) b3 n_mem (base + 96) hv_n hv_limb
  simp only [phB_t_20, divK_phaseB_n4_nm1_x8, divK_se12_32, phB_sp24_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  seqFrame hinit1fhinit2haddihbne htail
  -- ---- Step 6: Final consequence — permute assertions
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hinit1fhinit2haddihbnehtail

-- ============================================================================
-- Section 10: Phase A + Phase B n=4 composition (b≠0, b[3]≠0)
-- base → base+116 (entry to CLZ)
-- ============================================================================

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 2048 in
/-- When b ≠ 0 and b[3] ≠ 0, evm_div executes Phase A (ntaken) then Phase B (n=4).
    Execution: 8 + 16 = 24 instructions, base → base+116 (start of CLZ).
    Pre/postcondition shapes reflect frame structure from composition. -/
theorem evm_div_phaseAB_n4_spec (sp base : Word)
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
-- Section 10b: Phase B cascade step subsumption lemmas
-- ============================================================================

-- ADDI x5 x0 3 at base+76 (index 11 of phaseB)
private theorem addi_x5_3_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 76) (.ADDI .x5 .x0 3)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 11
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 11) = (44 : Word) from by native_decide,
      show (base + 32 : Word) + 44 = base + 76 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- BNE x7 x0 16 at base+80 (index 12 of phaseB)
private theorem bne_x7_16_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 80) (.BNE .x7 .x0 16)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 12
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 12) = (48 : Word) from by native_decide,
      show (base + 32 : Word) + 48 = base + 80 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- ADDI x5 x0 2 at base+84 (index 13 of phaseB)
private theorem addi_x5_2_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 84) (.ADDI .x5 .x0 2)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 13
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 13) = (52 : Word) from by native_decide,
      show (base + 32 : Word) + 52 = base + 84 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- BNE x6 x0 8 at base+88 (index 14 of phaseB)
private theorem bne_x6_8_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 88) (.BNE .x6 .x0 8)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 14
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 14) = (56 : Word) from by native_decide,
      show (base + 32 : Word) + 56 = base + 88 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- ADDI x5 x0 1 at base+92 (index 15 of phaseB)
private theorem addi_x5_1_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 92) (.ADDI .x5 .x0 1)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 15
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 15) = (60 : Word) from by native_decide,
      show (base + 32 : Word) + 60 = base + 92 from by bv_omega] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- ============================================================================
-- Section 10c: Phase B cascade constants and address lemmas
-- ============================================================================

-- signExtend constants for cascade steps
private theorem divK_se12_3 : signExtend12 (3 : BitVec 12) = (3 : Word) := by native_decide
private theorem divK_se12_2 : signExtend12 (2 : BitVec 12) = (2 : Word) := by native_decide
private theorem divK_se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by native_decide
private theorem signExtend13_16 : signExtend13 (16 : BitVec 13) = (16 : Word) := by native_decide
private theorem signExtend13_8 : signExtend13 (8 : BitVec 13) = (8 : Word) := by native_decide

-- nm1_x8 = (n + signExtend12 4095) <<< 3 for each n value
private theorem divK_phaseB_n3_nm1_x8 :
    ((3 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (16 : Word) := by
  native_decide
private theorem divK_phaseB_n2_nm1_x8 :
    ((2 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (8 : Word) := by
  native_decide
private theorem divK_phaseB_n1_nm1_x8 :
    ((1 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (0 : Word) := by
  native_decide

-- Cascade address normalization
private theorem phB_step1_4 (base : Word) : (base + 76 : Word) + 4 = base + 80 := by bv_omega
private theorem phB_step1_8 (base : Word) : (base + 80 : Word) + 4 = base + 84 := by bv_omega
private theorem phB_step2_4 (base : Word) : (base + 84 : Word) + 4 = base + 88 := by bv_omega
private theorem phB_step2_8 (base : Word) : (base + 88 : Word) + 4 = base + 92 := by bv_omega
private theorem phB_fall_4 (base : Word) : (base + 92 : Word) + 4 = base + 96 := by bv_omega

-- Tail memory address normalization
private theorem phB_sp16_32 (sp : Word) : (sp + (16 : Word) + (32 : Word)) = sp + 48 := by bv_omega
private theorem phB_sp8_32 (sp : Word) : (sp + (8 : Word) + (32 : Word)) = sp + 40 := by bv_omega
private theorem phB_sp0_32 (sp : Word) : (sp + (0 : Word) + (32 : Word)) = sp + 32 := by bv_omega

-- ============================================================================
-- Section 10d: Phase B n=3 (b[3]=0, b[2]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 taken → tail
-- ============================================================================

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 4096 in
/-- Phase B when b[3]=0, b[2]≠0 (n=3): zero scratch, load b[1..2], cascade to n=3, load b[2].
    Execution: init1(7) + init2(2) + step0(2) + step1(2) + tail(5) = 18 instrs.
    Exit at base+116 (start of CLZ). x5 = b[2] (leading limb), n = 3. -/
theorem evm_div_phaseB_n3_spec (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 n_mem : Word)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
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
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (3 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + 32) q0 q1 q2 q3 u5 u6 u7
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u5 hv_u6 hv_u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
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
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, divK_se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi0_raw
  have haddi0f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rw [signExtend13_24]; bv_omega, phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne0_clean
  have hbne0f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [phB_step1_4, divK_se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_divCode base) haddi1_raw
  have haddi1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 taken (base+80 → base+96, b2≠0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rw [signExtend13_16]; bv_omega, phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne1_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb2nz)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_divCode base) hbne1_clean
  have hbne1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Tail (base+96 → base+116)
  have hv_limb : isValidDwordAccess
      ((sp + ((3 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat)
       + signExtend12 (32 : BitVec 12)) = true := by
    rw [divK_phaseB_n3_nm1_x8, divK_se12_32, phB_sp16_32]
    exact hvalid.get (show 6 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (3 : Word) b2 n_mem (base + 96) hv_n hv_limb
  simp only [phB_t_20, divK_phaseB_n3_nm1_x8, divK_se12_32, phB_sp16_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  have htailf := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123456 htailf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

-- ============================================================================
-- Section 10e: Phase B n=2 (b[3]=b[2]=0, b[1]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 taken → tail
-- ============================================================================

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 4096 in
/-- Phase B when b[3]=b[2]=0, b[1]≠0 (n=2): zero scratch, cascade to n=2, load b[1].
    Execution: init1(7) + init2(2) + 3×step(6) + tail(5) = 20 instrs.
    Exit at base+116. x5 = b[1] (leading limb), n = 2. -/
theorem evm_div_phaseB_n2_spec (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 n_mem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
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
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b1) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (2 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + 32) q0 q1 q2 q3 u5 u6 u7
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u5 hv_u6 hv_u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
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
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, divK_se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi0_raw
  have haddi0f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rw [signExtend13_24]; bv_omega, phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne0_clean
  have hbne0f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [phB_step1_4, divK_se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_divCode base) haddi1_raw
  have haddi1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 ntaken (base+80 → base+84, b2=0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rw [signExtend13_16]; bv_omega, phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_divCode base) hbne1_clean
  have hbne1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Cascade step 2: ADDI x5=2 (base+84 → base+88)
  have haddi2_raw := addi_x0_spec_gen .x5 (3 : Word) 2 (base + 84) (by nofun)
  simp only [phB_step2_4, divK_se12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_divCode base) haddi2_raw
  have haddi2f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi2
  have h1234567 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123456 haddi2f
  -- ---- Cascade step 2: BNE x6 taken (base+88 → base+96, b1≠0)
  have hbne2_raw := bne_spec_gen .x6 .x0 8 b1 (0 : Word) (base + 88)
  rw [show (base + 88 : Word) + signExtend13 8 = base + 96 from by
        rw [signExtend13_8]; bv_omega, phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb1nz)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_divCode base) hbne2_clean
  have hbne2f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne2
  have h12345678 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234567 hbne2f
  -- ---- Tail (base+96 → base+116)
  have hv_limb : isValidDwordAccess
      ((sp + ((2 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat)
       + signExtend12 (32 : BitVec 12)) = true := by
    rw [divK_phaseB_n2_nm1_x8, divK_se12_32, phB_sp8_32]
    exact hvalid.get (show 5 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (2 : Word) b1 n_mem (base + 96) hv_n hv_limb
  simp only [phB_t_20, divK_phaseB_n2_nm1_x8, divK_se12_32, phB_sp8_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  have htailf := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12345678 htailf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

-- ============================================================================
-- Section 10f: Phase B n=1 (b[3]=b[2]=b[1]=0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 ntaken → ADDI x5=1 → tail
-- ============================================================================

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 4096 in
/-- Phase B when b[3]=b[2]=b[1]=0 (n=1): zero scratch, cascade falls through all BNEs, load b[0].
    Execution: all 21 instructions of divK_phaseB.
    Exit at base+116. x5 = b[0] (leading limb), n = 1.
    Note: b[0] must be in precondition since the tail loads from sp+32. -/
theorem evm_div_phaseB_n1_spec (sp base : Word)
    (b0 b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 n_mem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
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
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ n_mem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (1 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + 32) q0 q1 q2 q3 u5 u6 u7
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u5 hv_u6 hv_u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_divCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7 hvalid
  simp only [phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_divCode base) hinit2_raw
  have hinit2f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit2
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [phB_addi_4, divK_se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_divCode base) haddi0_raw
  have haddi0f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rw [signExtend13_24]; bv_omega, phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_divCode base) hbne0_clean
  have hbne0f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [phB_step1_4, divK_se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_divCode base) haddi1_raw
  have haddi1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 ntaken (base+80 → base+84, b2=0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rw [signExtend13_16]; bv_omega, phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_divCode base) hbne1_clean
  have hbne1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Cascade step 2: ADDI x5=2 (base+84 → base+88)
  have haddi2_raw := addi_x0_spec_gen .x5 (3 : Word) 2 (base + 84) (by nofun)
  simp only [phB_step2_4, divK_se12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_divCode base) haddi2_raw
  have haddi2f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi2
  have h1234567 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123456 haddi2f
  -- ---- Cascade step 2: BNE x6 ntaken (base+88 → base+92, b1=0)
  have hbne2_raw := bne_spec_gen .x6 .x0 8 b1 (0 : Word) (base + 88)
  rw [show (base + 88 : Word) + signExtend13 8 = base + 96 from by
        rw [signExtend13_8]; bv_omega, phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb1z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_divCode base) hbne2_clean
  have hbne2f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hbne2
  have h12345678 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234567 hbne2f
  -- ---- Fallthrough: ADDI x5=1 (base+92 → base+96)
  have haddi3_raw := addi_x0_spec_gen .x5 (2 : Word) 1 (base + 92) (by nofun)
  simp only [phB_fall_4, divK_se12_1] at haddi3_raw
  have haddi3 := cpsTriple_extend_code (addi_x5_1_sub_divCode base) haddi3_raw
  have haddi3f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) haddi3
  have h123456789 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12345678 haddi3f
  -- ---- Tail (base+96 → base+116)
  have hv_limb : isValidDwordAccess
      ((sp + ((1 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat)
       + signExtend12 (32 : BitVec 12)) = true := by
    rw [divK_phaseB_n1_nm1_x8, divK_se12_32, phB_sp0_32]
    exact hvalid.get (show 4 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (1 : Word) b0 n_mem (base + 96) hv_n hv_limb
  simp only [phB_t_20, divK_phaseB_n1_nm1_x8, divK_se12_32, phB_sp0_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_divCode base) htail_raw
  have htailf := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123456789 htailf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

-- ============================================================================
-- Section 10g: Phase C2 composition (shift check, 4 instructions)
-- base+212: SD shift, ADDI x2=0, SUB x2=-shift, BEQ shift=0
-- ============================================================================

/-- Phase C2 code (block 3) is subsumed by divCode. -/
private theorem divK_phaseC2_code_sub_divCode (base : Word) :
    ∀ a i, (divK_phaseC2_code 172 (base + 212)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_phaseC2_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- BEQ x6 x0 172 singleton at base+224 (index 3 of phaseC2) is subsumed by divCode. -/
private theorem beq_shift_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 224) (.BEQ .x6 .x0 172)) a = some i →
      (divCode base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 212) (divK_phaseC2 172) 3
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 3) = (12 : Word) from by native_decide,
      show (base + 212 : Word) + 12 = base + 224 from by bv_omega] at hlookup
  exact divK_phaseC2_code_sub_divCode base a i
    (CodeReq.singleton_mono hlookup a i h)

private theorem signExtend13_172 : signExtend13 (172 : BitVec 13) = (172 : Word) := by native_decide

/-- Phase C2 body (base+212 → base+224): store shift, compute anti_shift.
    Extends to divCode. Uses first 3 instructions of phaseC2. -/
private theorem divK_phaseC2_body_divCode (sp shift v2 shift_mem : Word) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true) :
    cpsTriple (base + 212) (base + 224) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_spec sp shift v2 shift_mem 172 (base + 212) hv_shift
  rw [show (base + 212 : Word) + 12 = base + 224 from by bv_omega] at hbody
  exact cpsTriple_extend_code (divK_phaseC2_code_sub_divCode base) hbody

set_option maxRecDepth 2048 in
/-- Phase C2 when shift ≠ 0: falls through to normB at base+228.
    Stores shift to scratch, computes anti_shift = -shift. -/
theorem divK_phaseC2_ntaken_spec (sp shift v2 shift_mem : Word) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hshift_nz : shift ≠ 0) :
    cpsTriple (base + 212) (base + 228) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode sp shift v2 shift_mem base hv_shift
  have hbeq_raw := beq_spec_gen .x6 .x0 172 shift (0 : Word) (base + 224)
  rw [show (base + 224 : Word) + signExtend13 172 = base + 396 from by
        rw [signExtend13_172]; bv_omega,
      show (base + 224 : Word) + 4 = base + 228 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 (show shift ≠ (0 : Word) from hshift_nz))
  have hbeq := cpsTriple_extend_code (beq_shift_sub_divCode base) hbeq_clean
  have hbeqf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

set_option maxRecDepth 2048 in
/-- Phase C2 when shift = 0: branches to copyAU at base+396.
    Stores shift (=0) to scratch, computes anti_shift = 0. -/
theorem divK_phaseC2_taken_spec (sp shift v2 shift_mem : Word) (base : Word)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hshift_z : shift = 0) :
    cpsTriple (base + 212) (base + 396) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_divCode sp shift v2 shift_mem base hv_shift
  have hbeq_raw := beq_spec_gen .x6 .x0 172 shift (0 : Word) (base + 224)
  rw [show (base + 224 : Word) + signExtend13 172 = base + 396 from by
        rw [signExtend13_172]; bv_omega,
      show (base + 224 : Word) + 4 = base + 228 from by bv_omega] at hbeq_raw
  have hbeq_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbeq := cpsTriple_extend_code (beq_shift_sub_divCode base) hbeq_clean
  have hbeqf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

-- ============================================================================
-- Section 10h: NormB composition (normalize divisor, 21 instructions)
-- base+228: 3 merge blocks (6 instrs each) + 1 last block (3 instrs)
-- ============================================================================

/-- NormB code (block 4) is subsumed by divCode. -/
private theorem divK_normB_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 228) divK_normB) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: NormB sub-block subsumption via ofProg_mono_sub. -/
private theorem normB_sub (base : Word) (sub_prog : List Instr) (k : Nat)
    (hk : k + sub_prog.length ≤ divK_normB.length)
    (hslice : (divK_normB.drop k).take sub_prog.length = sub_prog)
    (hbound : 4 * divK_normB.length < 2 ^ 64) :
    ∀ a i, (CodeReq.ofProg ((base + 228) + BitVec.ofNat 64 (4 * k)) sub_prog) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_normB_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 228) _ divK_normB _ k rfl hslice hk hbound a i h)

-- signExtend12 for offsets used by normB merge spec
private theorem se12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by native_decide
private theorem se12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by native_decide
private theorem se12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by native_decide
private theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by native_decide

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
/-- Full NormB: normalize divisor b[0..3] in place by left-shifting.
    base+228 → base+312 (21 instructions).
    Pre: x12=sp, x6=shift, x2=anti_shift, b[0..3] at sp+32..56.
    Post: b[i] normalized, x5=b[0]<<<shift, x7=b[0]>>>anti_shift. -/
theorem divK_normB_full_spec (sp b0 b1 b2 b3 v5 v7 shift anti_shift : Word) (base : Word)
    (hvalid : ValidMemRange sp 8) :
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    cpsTriple (base + 228) (base + 312) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x7 ↦ᵣ (b0 >>> (anti_shift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
       ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3')) := by
  intro b3' b2' b1' b0'
  -- Merge 1: b[3] with b[2] (base+228 → base+252)
  have hm1 := divK_normB_merge_spec 56 48 sp b3 b2 v5 v7 shift anti_shift (base + 228)
    (by rw [se12_56]; exact hvalid.get (show 7 < 8 from by omega))
    (by rw [se12_48]; exact hvalid.get (show 6 < 8 from by omega))
  simp only [se12_56, se12_48] at hm1
  rw [show (base + 228 : Word) + 24 = base + 252 from by bv_omega] at hm1
  have hm1e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 228) divK_normB
        (divK_normB_merge_prog 56 48) 0
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hm1
  -- Frame merge1 with b[0], b[1] (not touched by merge1)
  have hm1ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1))
    (by pcFree) hm1e
  -- Merge 2: b[2] with b[1] (base+252 → base+276)
  have hm2 := divK_normB_merge_spec 48 40 sp b2 b1 b3' (b2 >>> (anti_shift.toNat % 64))
    shift anti_shift (base + 252)
    (by rw [se12_48]; exact hvalid.get (show 6 < 8 from by omega))
    (by rw [se12_40]; exact hvalid.get (show 5 < 8 from by omega))
  simp only [se12_48, se12_40] at hm2
  rw [show (base + 252 : Word) + 24 = base + 276 from by bv_omega] at hm2
  have hm2e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 252) divK_normB
        (divK_normB_merge_prog 48 40) 6
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hm2
  have hm2ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 32) ↦ₘ b0) ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm2e
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hm1ef hm2ef
  -- Merge 3: b[1] with b[0] (base+276 → base+300)
  have hm3 := divK_normB_merge_spec 40 32 sp b1 b0
    b2' (b1 >>> (anti_shift.toNat % 64)) shift anti_shift (base + 276)
    (by rw [se12_40]; exact hvalid.get (show 5 < 8 from by omega))
    (by rw [se12_32]; exact hvalid.get (show 4 < 8 from by omega))
  simp only [se12_40, se12_32] at hm3
  rw [show (base + 276 : Word) + 24 = base + 300 from by bv_omega] at hm3
  have hm3e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 276) divK_normB
        (divK_normB_merge_prog 40 32) 12
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hm3
  have hm3ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hm3e
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 hm3ef
  -- Last: b[0] alone (base+300 → base+312)
  have hl := divK_normB_last_spec 32 sp b0 b1' shift (base + 300)
    (by rw [se12_32]; exact hvalid.get (show 4 < 8 from by omega))
  simp only [se12_32] at hl
  rw [show (base + 300 : Word) + 12 = base + 312 from by bv_omega] at hl
  have hle := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normB_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 228) (base + 300) divK_normB
        (divK_normB_last_prog 32) 18
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hl
  have hlef := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ (b0 >>> (anti_shift.toNat % 64))) ** (.x2 ↦ᵣ anti_shift) **
     ((sp + 40) ↦ₘ b1') ** ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3'))
    (by pcFree) hle
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hlef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h1234

-- ============================================================================
-- Section 10i: NormA composition (normalize dividend, 21 instructions)
-- base+312: top(3) + mergeA(5) + mergeB(5) + mergeA(5) + last(2) + JAL(1)
-- ============================================================================

/-- NormA code (block 5) is subsumed by divCode. -/
private theorem divK_normA_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 312) (divK_normA 40)) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: NormA sub-block subsumption via ofProg_mono_sub. -/
private theorem normA_sub (base : Word) (sub_prog : List Instr) (k : Nat)
    (hk : k + sub_prog.length ≤ (divK_normA 40).length)
    (hslice : ((divK_normA 40).drop k).take sub_prog.length = sub_prog)
    (hbound : 4 * (divK_normA 40).length < 2 ^ 64) :
    ∀ a i, (CodeReq.ofProg ((base + 312) + BitVec.ofNat 64 (4 * k)) sub_prog) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_normA_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 312) _ (divK_normA 40) _ k rfl hslice hk hbound a i h)

-- signExtend12 for src/dst offsets used by normA specs
private theorem se12_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by native_decide
private theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by native_decide
private theorem se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by native_decide
private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by native_decide
private theorem se12_4024 : signExtend12 (4024 : BitVec 12) = signExtend12 4024 := rfl
private theorem se12_4032 : signExtend12 (4032 : BitVec 12) = signExtend12 4032 := rfl
private theorem se12_4040 : signExtend12 (4040 : BitVec 12) = signExtend12 4040 := rfl
private theorem se12_4048 : signExtend12 (4048 : BitVec 12) = signExtend12 4048 := rfl
private theorem se12_4056 : signExtend12 (4056 : BitVec 12) = signExtend12 4056 := rfl
private theorem signExtend21_40 : signExtend21 (40 : BitVec 21) = (40 : Word) := by native_decide

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
/-- Full NormA: normalize dividend a[0..3] → u[0..4] and jump to loopSetup.
    base+312 → base+432 (21 instructions including JAL).
    u[4] = a[3]>>>anti_shift, u[3..0] = merged shifted limbs. -/
theorem divK_normA_full_spec (sp a0 a1 a2 a3 v5 v7 v10 shift anti_shift : Word)
    (u0_old u1_old u2_old u3_old u4_old : Word) (base : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    let u4 := a3 >>> (anti_shift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    cpsTriple (base + 312) (base + 432) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4056) ↦ₘ u0_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) ** (.x10 ↦ᵣ (a0 >>> (anti_shift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4056) ↦ₘ u0)) := by
  intro u4 u3 u2 u1 u0
  -- Top: LD a[3], SRL→u[4], SD u[4] (base+312 → base+324)
  have htop := divK_normA_top_spec 24 4024 sp a3 v5 v7 anti_shift u4_old (base + 312)
    (by rw [se12_24]; exact hvalid.get (show 3 < 8 from by omega)) hv_u4
  simp only [se12_24] at htop
  rw [show (base + 312 : Word) + 12 = base + 324 from by bv_omega] at htop
  have htope := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 312) (divK_normA 40)
        (divK_normA_top_prog 24 4024) 0
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) htop
  -- Frame top with x6, x10, a[0..2], u[0..3]
  have htopef := cpsTriple_frame_left _ _ _ _ _
    ((.x10 ↦ᵣ v10) ** (.x6 ↦ᵣ shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) **
     ((sp + signExtend12 4032) ↦ₘ u3_old) **
     ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
     ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) htope
  -- MergeA 1: u[3] = (a[3]<<<shift) | (a[2]>>>anti) (base+324 → base+344)
  have hma1 := divK_normA_mergeA_spec 16 4032 sp a3 a2 u4 v10 shift anti_shift u3_old (base + 324)
    (by rw [se12_16]; exact hvalid.get (show 2 < 8 from by omega)) hv_u3
  simp only [se12_16] at hma1
  rw [show (base + 324 : Word) + 20 = base + 344 from by bv_omega] at hma1
  have hma1e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 324) (divK_normA 40)
        (divK_normA_mergeA_prog 16 4032) 3
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hma1
  have hma1ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
     ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) hma1e
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) htopef hma1ef
  -- MergeB: u[2] = (a[2]<<<shift) | (a[1]>>>anti) (base+344 → base+364)
  have hmb := divK_normA_mergeB_spec 8 4040 sp a2 a1 u3 (a2 >>> (anti_shift.toNat % 64))
    shift anti_shift u2_old (base + 344)
    (by rw [se12_8]; exact hvalid.get (show 1 < 8 from by omega)) hv_u2
  simp only [se12_8] at hmb
  rw [show (base + 344 : Word) + 20 = base + 364 from by bv_omega] at hmb
  have hmbe := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 344) (divK_normA 40)
        (divK_normA_mergeB_prog 8 4040) 8
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hmb
  have hmbef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4048) ↦ₘ u1_old) ** ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) hmbe
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 hmbef
  -- MergeA 2: u[1] = (a[1]<<<shift) | (a[0]>>>anti) (base+364 → base+384)
  have hma2 := divK_normA_mergeA_spec 0 4048 sp a1 a0 u2 (a1 >>> (anti_shift.toNat % 64))
    shift anti_shift u1_old (base + 364)
    (by rw [se12_0]; exact hvalid.get (show 0 < 8 from by omega)) hv_u1
  simp only [se12_0] at hma2
  rw [show (base + 364 : Word) + 20 = base + 384 from by bv_omega] at hma2
  have hma2e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 364) (divK_normA 40)
        (divK_normA_mergeA_prog 0 4048) 13
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hma2
  have hma2ef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4056) ↦ₘ u0_old))
    (by pcFree) hma2e
  have h1234 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h123 hma2ef
  -- Last: u[0] = a[0]<<<shift (base+384 → base+392)
  have hlast := divK_normA_last_spec 4056 sp a0 shift u0_old (base + 384) hv_u0
  rw [show (base + 384 : Word) + 8 = base + 392 from by bv_omega] at hlast
  have hlaste := cpsTriple_extend_code (hmono := fun a i h =>
    divK_normA_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 312) (base + 384) (divK_normA 40)
        (divK_normA_last_prog 4056) 18
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hlast
  have hlastef := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ u1) ** (.x10 ↦ᵣ (a0 >>> (anti_shift.toNat % 64))) ** (.x2 ↦ᵣ anti_shift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1))
    (by pcFree) hlaste
  have h12345 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1234 hlastef
  -- JAL x0 40 at base+392 → base+432 (1 instruction, empAssertion pre/post)
  have hjal := jal_x0_spec_gen 40 (base + 392)
  rw [show (base + 392 : Word) + signExtend21 40 = base + 432 from by
        rw [signExtend21_40]; bv_omega] at hjal
  have hjale := cpsTriple_extend_code (hmono := by
    intro a i h
    exact divK_normA_code_sub_divCode base a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + 312) (divK_normA 40) 20
          (by native_decide) (by native_decide)
        rw [show (base + 312 : Word) + BitVec.ofNat 64 (4 * 20) = base + 392 from by bv_omega]
          at hlookup
        exact hlookup) a i h)) hjal
  -- Frame JAL with everything, then strip empAssertion via consequence
  let postAll := (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u1) ** (.x7 ↦ᵣ u0) **
    (.x10 ↦ᵣ (a0 >>> (anti_shift.toNat % 64))) **
    (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
    ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
    ((sp + signExtend12 4056) ↦ₘ u0)
  have hjalef := cpsTriple_frame_left _ _ _ _ _ postAll (by pcFree) hjale
  -- Compose h12345 with JAL by consequence (empAssertion → postAll → postAll)
  -- Since JAL has empAssertion pre/post and frame is postAll, the result is (empAssertion ** postAll).
  -- Use consequence to strip empAssertion from both sides.
  have hjal_clean : cpsTriple (base + 392) (base + 432) (divCode base) postAll postAll :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by show (empAssertion ** postAll) h; rw [sepConj_emp_left']; exact hp)
      (fun h hp => by rw [sepConj_emp_left'] at hp; exact hp)
      hjalef
  have h123456 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12345 hjal_clean
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h123456

-- ============================================================================
-- Section 10j: CopyAU composition (copy a[] to u[], 9 instructions)
-- base+396: used when shift=0 (no normalization needed)
-- ============================================================================

/-- CopyAU code (block 6) is subsumed by divCode. -/
private theorem divK_copyAU_code_sub_divCode (base : Word) :
    ∀ a i, (divK_copyAU_code (base + 396)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_copyAU_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Full CopyAU: copy a[0..3] to u[0..3], set u[4]=0.
    base+396 → base+432 (9 instructions). -/
theorem divK_copyAU_full_spec (sp : Word)
    (a0 a1 a2 a3 : Word) (u0 u1 u2 u3 u4 v5 : Word) (base : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true) :
    cpsTriple (base + 396) (base + 432) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have hcopy := divK_copyAU_spec sp (base + 396) a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
    hvalid hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
  rw [show (base + 396 : Word) + 36 = base + 432 from by bv_omega] at hcopy
  exact cpsTriple_extend_code (divK_copyAU_code_sub_divCode base) hcopy

-- ============================================================================
-- Section 10k: LoopSetup composition (4 instructions, cpsBranch at base+432)
-- LD n, ADDI 4, SUB m=4-n, BLT m<0
-- ============================================================================

/-- LoopSetup code (block 7) is subsumed by divCode. -/
private theorem divK_loopSetup_code_sub_divCode (base : Word) :
    ∀ a i, (divK_loopSetup_code 460 (base + 432)) a = some i → (divCode base) a = some i := by
  unfold divCode divK_loopSetup_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- BLT singleton at base+444 (index 3 of loopSetup) is subsumed by divCode. -/
private theorem blt_loopSetup_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 444) (.BLT .x1 .x0 460)) a = some i →
      (divCode base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 432) (divK_loopSetup 460) 3
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 3) = (12 : Word) from by native_decide,
      show (base + 432 : Word) + 12 = base + 444 from by bv_omega] at hlookup
  exact divK_loopSetup_code_sub_divCode base a i
    (CodeReq.singleton_mono hlookup a i h)

private theorem signExtend13_460 : signExtend13 (460 : BitVec 13) = (460 : Word) := by native_decide

set_option maxRecDepth 2048 in
/-- LoopSetup when m ≥ 0 (n ≤ 4): falls through to loop body at base+448.
    Loads n from scratch, computes m = 4-n, BLT not taken. -/
theorem divK_loopSetup_ntaken_spec (sp n v1 v5 : Word) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTriple (base + 432) (base + 448) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro m
  have hbody := divK_loopSetup_body_spec sp n v1 v5 460 (base + 432) hv_n
  rw [show (base + 432 : Word) + 12 = base + 444 from by bv_omega] at hbody
  have hbodye := cpsTriple_extend_code (divK_loopSetup_code_sub_divCode base) hbody
  have hblt_raw := blt_spec_gen .x1 .x0 460 m (0 : Word) (base + 444)
  rw [show (base + 444 : Word) + signExtend13 460 = base + 904 from by
        rw [signExtend13_460]; bv_omega,
      show (base + 444 : Word) + 4 = base + 448 from by bv_omega] at hblt_raw
  have hblt_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hblt_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hm_ge)
  have hblte := cpsTriple_extend_code (blt_loopSetup_sub_divCode base) hblt_clean
  have hbltef := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

set_option maxRecDepth 2048 in
/-- LoopSetup when m < 0 (n > 4, skip loop): branches to denorm at base+904. -/
theorem divK_loopSetup_taken_spec (sp n v1 v5 : Word) (base : Word)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hm_lt : BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    let m := signExtend12 (4 : BitVec 12) - n
    cpsTriple (base + 432) (base + 904) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x1 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** (.x1 ↦ᵣ m) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n)) := by
  intro m
  have hbody := divK_loopSetup_body_spec sp n v1 v5 460 (base + 432) hv_n
  rw [show (base + 432 : Word) + 12 = base + 444 from by bv_omega] at hbody
  have hbodye := cpsTriple_extend_code (divK_loopSetup_code_sub_divCode base) hbody
  have hblt_raw := blt_spec_gen .x1 .x0 460 m (0 : Word) (base + 444)
  rw [show (base + 444 : Word) + signExtend13 460 = base + 904 from by
        rw [signExtend13_460]; bv_omega,
      show (base + 444 : Word) + 4 = base + 448 from by bv_omega] at hblt_raw
  have hblt_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hblt_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hm_lt ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hblte := cpsTriple_extend_code (blt_loopSetup_sub_divCode base) hblt_clean
  have hbltef := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hblte
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hbodye hbltef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

-- ============================================================================
-- Section 10l: Denorm composition (25 instructions at base+904)
-- LD shift, BEQ skip, ADDI+SUB anti, 3×merge + last
-- ============================================================================

/-- Denorm code (block 9) is subsumed by divCode. -/
private theorem divK_denorm_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 904) divK_denorm) a = some i → (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: Denorm sub-block subsumption via ofProg_mono_sub. -/
private theorem denorm_sub (base : Word) (sub_prog : List Instr) (k : Nat)
    (hk : k + sub_prog.length ≤ divK_denorm.length)
    (hslice : (divK_denorm.drop k).take sub_prog.length = sub_prog)
    (hbound : 4 * divK_denorm.length < 2 ^ 64) :
    ∀ a i, (CodeReq.ofProg ((base + 904) + BitVec.ofNat 64 (4 * k)) sub_prog) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_denorm_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 904) _ divK_denorm _ k rfl hslice hk hbound a i h)

-- signExtend12 for u[] offsets
private theorem se12_4032' : signExtend12 (4032 : BitVec 12) = signExtend12 4032 := rfl
private theorem se12_4040' : signExtend12 (4040 : BitVec 12) = signExtend12 4040 := rfl
private theorem se12_4048' : signExtend12 (4048 : BitVec 12) = signExtend12 4048 := rfl
private theorem se12_4056' : signExtend12 (4056 : BitVec 12) = signExtend12 4056 := rfl

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
/-- Full Denorm (shift body only): denormalize u[0..3] by right-shifting.
    base+904+16 → base+904+100 (21 instructions: ADDI+SUB + 3×merge + last).
    Used when shift≠0. The BEQ and LD are handled separately. -/
theorem divK_denorm_body_spec (sp u0 u1 u2 u3 v2 v5 v7 shift : Word) (base : Word)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true) :
    let anti_shift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (anti_shift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (anti_shift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (anti_shift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    cpsTriple (base + 912) (base + 1004) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u3') ** (.x7 ↦ᵣ (u3 <<< (anti_shift.toNat % 64))) **
       (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ anti_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
       ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3')) := by
  intro anti_shift u0' u1' u2' u3'
  -- ADDI x2 x0 0 + SUB x2 x2 x6 (base+912 → base+920): compute anti_shift
  have haddi := addi_x0_spec_gen .x2 v2 0 (base + 912) (by nofun)
  rw [show (base + 912 : Word) + 4 = base + 916 from by bv_omega] at haddi
  have haddie := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 912) divK_denorm
        [.ADDI .x2 .x0 0] 2
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) haddi
  -- Frame ADDI with x12, x5, x7, x6, and all memory
  have haddief := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ shift) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) haddie
  have hsub := sub_spec_gen_rd_eq_rs1 .x2 .x6
    (signExtend12 (0 : BitVec 12)) shift (base + 916) (by nofun)
  rw [show (base + 916 : Word) + 4 = base + 920 from by bv_omega] at hsub
  have hsube := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.singleton_mono (by
        have hlookup := CodeReq.ofProg_lookup (base + 904) divK_denorm 3
          (by native_decide) (by native_decide)
        rw [show BitVec.ofNat 64 (4 * 3) = (12 : Word) from by native_decide,
            show (base + 904 : Word) + 12 = base + 916 from by bv_omega] at hlookup
        exact hlookup) a i h)) hsub
  -- Frame SUB with x12, x5, x7, x0, and all memory
  have hsubf := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hsube
  have h_anti := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) haddief hsubf
  -- Merge u[0] with u[1] (base+920 → base+944)
  have hm0 := divK_denorm_merge_spec 4056 4048 sp u0 u1 v5 v7 shift anti_shift (base + 920)
    hv_u0 hv_u1
  rw [show (base + 920 : Word) + 24 = base + 944 from by bv_omega] at hm0
  have hm0e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 920) divK_denorm
        (divK_denorm_merge_prog 4056 4048) 4
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hm0
  have hm0ef := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm0e
  have h_m0 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_anti hm0ef
  -- Merge u[1] with u[2] (base+944 → base+968)
  have hm1 := divK_denorm_merge_spec 4048 4040 sp u1 u2
    u0' (u1 <<< (anti_shift.toNat % 64)) shift anti_shift (base + 944)
    hv_u1 hv_u2
  rw [show (base + 944 : Word) + 24 = base + 968 from by bv_omega] at hm1
  have hm1e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 944) divK_denorm
        (divK_denorm_merge_prog 4048 4040) 10
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hm1
  have hm1ef := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hm1e
  have h_m1 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_m0 hm1ef
  -- Merge u[2] with u[3] (base+968 → base+992)
  have hm2 := divK_denorm_merge_spec 4040 4032 sp u2 u3
    u1' (u2 <<< (anti_shift.toNat % 64)) shift anti_shift (base + 968)
    hv_u2 hv_u3
  rw [show (base + 968 : Word) + 24 = base + 992 from by bv_omega] at hm2
  have hm2e := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 968) divK_denorm
        (divK_denorm_merge_prog 4040 4032) 16
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hm2
  have hm2ef := cpsTriple_frame_left _ _ _ _ _
    ((.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1'))
    (by pcFree) hm2e
  have h_m2 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_m1 hm2ef
  -- Last u[3] (base+992 → base+1004)
  have hl := divK_denorm_last_spec 4032 sp u3 u2' shift (base + 992) hv_u3
  rw [show (base + 992 : Word) + 12 = base + 1004 from by bv_omega] at hl
  have hle := cpsTriple_extend_code (hmono := fun a i h =>
    divK_denorm_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 904) (base + 992) divK_denorm
        (divK_denorm_last_prog 4032) 22
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hl
  have hlef := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ (u3 <<< (anti_shift.toNat % 64))) ** (.x2 ↦ᵣ anti_shift) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
     ((sp + signExtend12 4040) ↦ₘ u2'))
    (by pcFree) hle
  have h_all := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h_m2 hlef
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h_all

-- ============================================================================
-- Section 10m: DIV Epilogue composition (10 instructions at base+1004)
-- Load q[0..3], ADDI sp+32, store to output, JAL to NOP
-- ============================================================================

/-- DIV epilogue code (block 10) is subsumed by divCode. -/
private theorem divK_divEpilogue_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1004) (divK_div_epilogue 24)) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
/-- Full DIV epilogue: load q[0..3] from scratch, advance sp, store to output, JAL to NOP.
    base+1004 → base+1064 (10 instructions). -/
theorem divK_div_epilogue_spec (sp : Word) (base : Word)
    (q0 q1 q2 q3 v5 v6 v7 v10 m0 m8 m16 m24 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true) :
    cpsTriple (base + 1004) (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) ** (.x10 ↦ᵣ q3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
       ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) := by
  -- Load phase (base+1004 → base+1020)
  have hload := divK_epilogue_load_spec 4088 4080 4072 4064 sp q0 q1 q2 q3 v5 v6 v7 v10
    (base + 1004) hv_q0 hv_q1 hv_q2 hv_q3
  rw [show (base + 1004 : Word) + 16 = base + 1020 from by bv_omega] at hload
  have hloade := cpsTriple_extend_code (hmono := fun a i h =>
    divK_divEpilogue_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 1004) (base + 1004) (divK_div_epilogue 24)
        (divK_epilogue_load_prog 4088 4080 4072 4064) 0
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hload
  -- Store phase (base+1020 → base+1064 via JAL)
  have hstore := divK_epilogue_store_spec sp (base + 1020) q0 q1 q2 q3 m0 m8 m16 m24 24 hvalid
  rw [show (base + 1020 : Word) + 20 + signExtend21 24 = base + 1064 from by
        rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by native_decide]; bv_omega]
    at hstore
  have hstoree := cpsTriple_extend_code (hmono := fun a i h =>
    divK_divEpilogue_code_sub_divCode base a i
      (CodeReq.ofProg_mono_sub (base + 1004) (base + 1020) (divK_div_epilogue 24)
        (divK_epilogue_store_prog 24) 4
        (by bv_omega) (by native_decide) (by native_decide) (by native_decide) a i h)) hstore
  -- Frame load with output memory
  have hloadef := cpsTriple_frame_left _ _ _ _ _
    (((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) ** ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hloade
  -- Frame store with scratch memory
  have hstoref := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3))
    (by pcFree) hstoree
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hloadef hstoref
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

-- ============================================================================
-- Section 11: MOD program code infrastructure
-- ============================================================================

/-- The full evm_mod code split into 14 per-phase CodeReq.ofProg blocks.
    Identical to divCode except block 10 uses divK_mod_epilogue. -/
abbrev modCode (base : Word) : CodeReq :=
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

private theorem divK_phaseA_code_sub_modCode (base : Word) :
    ∀ a i, (divK_phaseA_code base) a = some i → (modCode base) a = some i := by
  unfold modCode divK_phaseA_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left _ _

private theorem divK_zeroPath_code_sub_modCode (base : Word) :
    ∀ a i, (divK_zeroPath_code (base + 1044)) a = some i → (modCode base) a = some i := by
  unfold modCode divK_zeroPath_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

private theorem beq_singleton_sub_modCode (base : Word) :
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
theorem evm_mod_bzero_spec (sp base : Word)
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
  rw [show (base + 28 : Word) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbeq_raw
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
  rw [show (base + 1044 : Word) + 20 = base + 1064 from by bv_omega] at hzp
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
theorem evm_mod_phaseA_ntaken_spec (sp base : Word)
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
  rw [show (base + 28 : Word) + signExtend13 1016 = base + 1044 from by
        rw [signExtend13_1016]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbeq_raw
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
private theorem divK_div128_ofProg_sub_divCode (base : Word) :
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
  simp only [CodeReq.union] at h
  cases h1a : cr1 a with
  | some j => rw [h1a] at h; simp at h; exact h ▸ h1 a j h1a
  | none => rw [h1a] at h; simp at h; exact h2 a i h

-- Helper: singleton at index k of divK_div128 with explicit instr ⊆ divCode base.
-- Used to prove each singleton in a block's cr is subsumed by divCode.
private theorem d128_sub (base : Word) (k : Nat) (addr : Word) (instr : Instr)
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
private theorem d128_off_40 (base : Word) : (base + 1068 : Word) + 40 = base + 1108 := by bv_omega
private theorem d128_off_100 (base : Word) : (base + 1068 : Word) + 100 = base + 1168 := by bv_omega
private theorem d128_off_120 (base : Word) : (base + 1068 : Word) + 120 = base + 1188 := by bv_omega
private theorem d128_off_180 (base : Word) : (base + 1068 : Word) + 180 = base + 1248 := by bv_omega

-- ============================================================================
-- div128_spec: compose 5 block specs into single subroutine theorem.
-- Entry: base+1068, Exit: ret_addr (via JALR), CodeReq: divCode base.
-- ============================================================================

set_option maxHeartbeats 25600000 in
set_option maxRecDepth 4096 in
theorem div128_spec (sp ret_addr d u_lo u_hi : Word) (base : Word)
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
  intro d_hi d_lo un1 un0 q1 rhat hi1 q1c rhatc q_dlo rhat_un1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0_dlo rhat2_un0 q0' q
  -- ================================================================
  -- Block 1: Phase 1 (base+1068 → base+1108)
  -- Saves ret/d, splits d and u_lo into halves.
  -- ================================================================
  have hph1 := divK_div128_phase1_spec sp ret_addr d u_lo u_hi v1_old v6_old v11_old
    ret_mem d_mem dlo_mem un0_mem (base + 1068) hv_ret hv_d hv_dlo hv_un0
  rw [show (base + 1068 : Word) + 40 = base + 1108 from by bv_omega] at hph1
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
  rw [show (base + 1108 : Word) + 60 = base + 1168 from by bv_omega] at hst1
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
  rw [show (base + 1168 : Word) + 20 = base + 1188 from by bv_omega] at hcu
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
  rw [show (base + 1188 : Word) + 60 = base + 1248 from by bv_omega] at hst2
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

-- ============================================================================
-- Section 9: CLZ (Count Leading Zeros) composition
-- 24 instructions at base+116, 6-stage binary search.
-- Computes leading zero count in x6, shifts x5 left by that count.
-- ============================================================================

/-- CLZ code (block 2) is subsumed by divCode. -/
private theorem divK_clz_code_sub_divCode (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 116) divK_clz) a = some i →
      (divCode base) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock
  exact CodeReq.union_mono_left _ _

/-- Helper: CLZ stage at instruction index k is subsumed by divCode.
    The stage has 4 instructions starting at index k of divK_clz. -/
private theorem clz_stage_sub (base : Word)
    (K M_s : BitVec 6) (M_a : BitVec 12) (k : Nat)
    (hk : k + (divK_clz_stage_prog K M_s M_a).length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take (divK_clz_stage_prog K M_s M_a).length =
      divK_clz_stage_prog K M_s M_a)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_stage_code K M_s M_a ((base + 116) + BitVec.ofNat 64 (4 * k))) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 116) _ divK_clz _ k
      rfl hslice hk hbound a i h)

/-- Helper: CLZ last stage at instruction index k is subsumed by divCode.
    The last stage has 3 instructions. -/
private theorem clz_last_sub (base : Word) (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + 116) + BitVec.ofNat 64 (4 * k))) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCode base a i
    (CodeReq.ofProg_mono_sub (base + 116) _ divK_clz _ k
      rfl hslice hk hbound a i h)

/-- Helper: CLZ init singleton (ADDI x6 x0 0 at base+116) is subsumed by divCode. -/
private theorem clz_init_sub (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 116) (.ADDI .x6 .x0 0)) a = some i →
      (divCode base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_divCode base a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + 116) divK_clz 0
      (by native_decide) (by native_decide)) a i (by rwa [show (base + 116 : Word) =
        base + 116 + BitVec.ofNat 64 (4 * 0) from by bv_omega] at h))

-- CLZ stage parameters: (SRLI_K, SLLI_M_s, ADDI_M_a, instruction_index)
-- Stage 0: K=32, M_s=32, M_a=32, index 1 (after init at index 0)
-- Stage 1: K=48, M_s=16, M_a=16, index 5
-- Stage 2: K=56, M_s=8,  M_a=8,  index 9
-- Stage 3: K=60, M_s=4,  M_a=4,  index 13
-- Stage 4: K=62, M_s=2,  M_a=2,  index 17
-- Stage 5 (last): K=63, M_a=1,   index 21

/-- CLZ result function: compute (count, shifted_val) from a 6-stage binary search. -/
noncomputable def clzResult (val : Word) : Word × Word :=
  -- Stage 0: check top 32 bits
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  -- Stage 1: check bits 48..63 of current value
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  -- Stage 2: check bits 56..63
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  -- Stage 3: check bits 60..63
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  -- Stage 4: check bits 62..63
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  -- Stage 5 (last): check bit 63
  let c5 := if v4 >>> (63 : Nat) ≠ 0 then c4 else c4 + signExtend12 (1 : BitVec 12)
  (c5, v4)

-- Address lemmas for CLZ stages
private theorem clz_addr0 (base : Word) : (base + 116 : Word) + 4 = base + 120 := by bv_omega
private theorem clz_addr1 (base : Word) : (base + 120 : Word) + 16 = base + 136 := by bv_omega
private theorem clz_addr2 (base : Word) : (base + 136 : Word) + 16 = base + 152 := by bv_omega
private theorem clz_addr3 (base : Word) : (base + 152 : Word) + 16 = base + 168 := by bv_omega
private theorem clz_addr4 (base : Word) : (base + 168 : Word) + 16 = base + 184 := by bv_omega
private theorem clz_addr5 (base : Word) : (base + 184 : Word) + 16 = base + 200 := by bv_omega
private theorem clz_addr6 (base : Word) : (base + 200 : Word) + 12 = base + 212 := by bv_omega

/-- Combined CLZ stage: handles both taken and ntaken with conditional postcondition.
    After stage: val' = if (val>>>K≠0) then val else val<<<M_s,
    count' = if (val>>>K≠0) then count else count+M_a. -/
private theorem divK_clz_stage_combined
    (K M_s : BitVec 6) (M_a : BitVec 12) (val count v7 : Word) (base : Word) :
    let cr := divK_clz_stage_code K M_s M_a base
    let val' := if val >>> K.toNat ≠ 0 then val else val <<< M_s.toNat
    let count' := if val >>> K.toNat ≠ 0 then count else count + signExtend12 M_a
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val') ** (.x6 ↦ᵣ count') **
       (.x7 ↦ᵣ (val >>> K.toNat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr; dsimp only []
  by_cases h : val >>> K.toNat ≠ 0
  · simp only [if_pos h]
    exact divK_clz_stage_taken_spec K M_s M_a val count v7 base h
  · push_neg at h
    simp only [if_neg (show ¬(val >>> K.toNat ≠ 0) from not_not.mpr h)]
    have hs := divK_clz_stage_ntaken_spec K M_s M_a val count v7 base h
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by rw [show (val >>> K.toNat : Word) = 0 from h]; exact hp) hs

/-- Combined CLZ last stage: handles both taken and ntaken. -/
private theorem divK_clz_last_combined (val count v7 : Word) (base : Word) :
    let cr := divK_clz_last_code base
    let count' := if val >>> (63 : Nat) ≠ 0 then count else count + signExtend12 (1 : BitVec 12)
    cpsTriple base (base + 12) cr
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ count') **
       (.x7 ↦ᵣ (val >>> (63 : Nat))) ** (.x0 ↦ᵣ (0 : Word))) := by
  intro cr; dsimp only []
  by_cases h : val >>> (63 : Nat) ≠ 0
  · simp only [if_pos h]
    exact divK_clz_last_taken_spec val count v7 base h
  · push_neg at h
    simp only [if_neg (show ¬(val >>> (63 : Nat) ≠ 0) from not_not.mpr h)]
    have hs := divK_clz_last_ntaken_spec val count v7 base h
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by rw [show (val >>> (63 : Nat) : Word) = 0 from h]; exact hp) hs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full CLZ composition: 24 instructions at base+116→base+212.
    Computes count of leading zeros in x6, shifts x5 left by that count.
    Entry: base+116 with x5=val, x6=v6_old, x7=v7_old, x0=0.
    Exit: base+212 with x5=(clzResult val).2, x6=(clzResult val).1, x0=0. -/
theorem divK_clz_spec (val v6_old v7_old : Word) (base : Word) :
    cpsTriple (base + 116) (base + 212) (divCode base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6_old) ** (.x7 ↦ᵣ v7_old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  -- 0. Init: ADDI x6 x0 0 (base+116 → base+120)
  have I := divK_clz_init_spec v6_old (base + 116)
  have Ie := cpsTriple_extend_code (hmono := clz_init_sub base) I
  rw [clz_addr0] at Ie
  -- Frame init with x5, x7
  have Ief := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7_old)) (by pcFree) Ie
  -- Stage 0: K=32, M_s=32, M_a=32 (base+120 → base+136)
  have S0 := divK_clz_stage_combined 32 32 32 val (signExtend12 0) v7_old
    ((base + 116) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTriple_extend_code (hmono := clz_stage_sub base 32 32 32 1
    (by native_decide) (by native_decide) (by native_decide)) S0
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 1) = base + 120 from by bv_omega] at S0e
  rw [clz_addr1] at S0e
  seqFrame Ief S0e
  -- Abbreviations for stage 0 results
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  -- Stage 1: K=48, M_s=16, M_a=16 (base+136 → base+152)
  have S1 := divK_clz_stage_combined 48 16 16 v0 c0 (val >>> (32 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 5))
  dsimp only [] at S1
  have S1e := cpsTriple_extend_code (hmono := clz_stage_sub base 48 16 16 5
    (by native_decide) (by native_decide) (by native_decide)) S1
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 5) = base + 136 from by bv_omega] at S1e
  rw [clz_addr2] at S1e
  seqFrame IefS0e S1e
  -- Stage 2: K=56, M_s=8, M_a=8 (base+152 → base+168)
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := divK_clz_stage_combined 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTriple_extend_code (hmono := clz_stage_sub base 56 8 8 9
    (by native_decide) (by native_decide) (by native_decide)) S2
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 9) = base + 152 from by bv_omega] at S2e
  rw [clz_addr3] at S2e
  seqFrame IefS0eS1e S2e
  -- Stage 3: K=60, M_s=4, M_a=4 (base+168 → base+184)
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := divK_clz_stage_combined 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTriple_extend_code (hmono := clz_stage_sub base 60 4 4 13
    (by native_decide) (by native_decide) (by native_decide)) S3
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 13) = base + 168 from by bv_omega] at S3e
  rw [clz_addr4] at S3e
  seqFrame IefS0eS1eS2e S3e
  -- Stage 4: K=62, M_s=2, M_a=2 (base+184 → base+200)
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := divK_clz_stage_combined 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTriple_extend_code (hmono := clz_stage_sub base 62 2 2 17
    (by native_decide) (by native_decide) (by native_decide)) S4
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 17) = base + 184 from by bv_omega] at S4e
  rw [clz_addr5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  -- Stage 5 (last): K=63 (base+200 → base+212)
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := divK_clz_last_combined v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + 116) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTriple_extend_code (hmono := clz_last_sub base 21
    (by native_decide) (by native_decide) (by native_decide)) S5
  rw [show (base + 116 : Word) + BitVec.ofNat 64 (4 * 21) = base + 200 from by bv_omega] at S5e
  rw [clz_addr6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  -- Final permutation
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

end EvmAsm.Rv64
