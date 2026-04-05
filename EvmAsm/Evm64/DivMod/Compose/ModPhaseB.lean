/-
  EvmAsm.Evm64.DivMod.Compose.ModPhaseB

  MOD mirrors of Phase B n=4 composition.
  Proof structure mirrors PhaseAB.lean with modCode instead of divCode.
  Blocks 0-1 are identical between divCode and modCode.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- MOD CodeReq subsumption lemmas for blocks 0 and 1
-- Proofs mirror PhaseAB.lean: skip block 0 (phaseA), match block 1 (phaseB).
-- For modCode, blocks 0-1 are at identical positions as divCode.
-- ============================================================================

private theorem divK_phaseB_init1_code_sub_modCode (base : Word) :
    ∀ a i, (divK_phaseB_init1_code (base + 32)) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + 32) (base + 32) divK_phaseB
    (divK_phaseB.take 7) 0
    (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

private theorem divK_phaseB_init2_code_sub_modCode (base : Word) :
    ∀ a i, (divK_phaseB_init2_code (base + 60)) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + 32) (base + 60) divK_phaseB
    (divK_phaseB.drop 7 |>.take 2) 7
    (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

private theorem addi_x5_singleton_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 68) (.ADDI .x5 .x0 4)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 9
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 9) = (36 : Word) from by native_decide,
      show (base + 32 : Word) + 36 = base + 68 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

private theorem bne_x10_singleton_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 72) (.BNE .x10 .x0 24)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 10
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 10) = (40 : Word) from by native_decide,
      show (base + 32 : Word) + 40 = base + 72 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

private theorem divK_phaseB_tail_code_sub_modCode (base : Word) :
    ∀ a i, (divK_phaseB_tail_code (base + 96)) a = some i → (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + 32) (base + 96) divK_phaseB
    (divK_phaseB.drop 16) 16
    (by bv_addr) (by native_decide) (by native_decide) (by native_decide) a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- Address normalization helpers
private theorem mod_phB_off_28 (base : Word) : (base + 32 : Word) + 28 = base + 60 := by bv_addr
private theorem mod_phB_i2_8 (base : Word) : (base + 60 : Word) + 8 = base + 68 := by bv_addr
private theorem mod_phB_addi_4 (base : Word) : (base + 68 : Word) + 4 = base + 72 := by bv_addr
private theorem mod_phB_bne_4 (base : Word) : (base + 72 : Word) + 4 = base + 76 := by bv_addr
private theorem mod_phB_t_20 (base : Word) : (base + 96 : Word) + 20 = base + 116 := by bv_addr
private theorem mod_signExtend13_24 : signExtend13 (24 : BitVec 13) = (24 : Word) := by
  native_decide
private theorem mod_divK_se12_4 : signExtend12 (4 : BitVec 12) = (4 : Word) := by native_decide
private theorem mod_divK_phaseB_n4_nm1_x8 :
    signExtend12 (8 : BitVec 12) = (8 : Word) := by native_decide
private theorem mod_divK_se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by native_decide
private theorem mod_phB_sp24_32 (sp : Word) :
    sp + ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat +
      signExtend12 (32 : BitVec 12) = sp + 56 := by
  simp only [show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by native_decide,
             show signExtend12 (32 : BitVec 12) = (32 : Word) from by native_decide]
  bv_addr

-- ============================================================================
-- MOD Phase B n=4 (b[3] ≠ 0): init1→init2→ADDI→BNE(taken)→tail
-- Mirror of evm_div_phaseB_n4_spec with modCode.
-- ============================================================================

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 2048 in
/-- MOD Phase B for n=4 (b[3] ≠ 0): x5 = b[3], x10 = b[3] (leading limb).
    init1 → init2 → ADDI x5=4 → BNE(taken, b[3]≠0) → tail. -/
theorem evm_mod_phaseB_n4_spec (sp base : Word)
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
    cpsTriple (base + 32) (base + 116) (modCode base)
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
  simp only [mod_phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_modCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- Step 2: init2 (base+60 → base+68) — load b[1], b[2]
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7 hvalid
  simp only [mod_phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_modCode base) hinit2_raw
  seqFrame hinit1f hinit2
  -- ---- Step 3: ADDI x5 x0 4 at base+68 → base+72
  have haddi_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [mod_phB_addi_4, mod_divK_se12_4] at haddi_raw
  have haddi := cpsTriple_extend_code (addi_x5_singleton_sub_modCode base) haddi_raw
  seqFrame hinit1fhinit2 haddi
  -- ---- Step 4: BNE x10 x0 24 at base+72, elim ntaken (b3=0 absurd)
  have hbne_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rw [mod_signExtend13_24]; bv_addr, mod_phB_bne_4] at hbne_raw
  have hbne_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb3nz)
  have hbne := cpsTriple_extend_code (bne_x10_singleton_sub_modCode base) hbne_clean
  seqFrame hinit1fhinit2haddi hbne
  -- ---- Step 5: Tail (base+96 → base+116) — store n=4, load leading limb b[3]
  have hv_limb : isValidDwordAccess
      ((sp + ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat)
       + signExtend12 (32 : BitVec 12)) = true := by
    rw [mod_phB_sp24_32]; exact hvalid.get (show 7 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (4 : Word) b3 n_mem (base + 96) hv_n hv_limb
  simp only [mod_phB_t_20, mod_phB_sp24_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_modCode base) htail_raw
  seqFrame hinit1fhinit2haddihbne htail
  -- ---- Final consequence — permute assertions
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hinit1fhinit2haddihbnehtail

-- ============================================================================
-- MOD Phase B cascade step subsumption lemmas
-- ============================================================================

-- ADDI x5 x0 3 at base+76 (index 11 of phaseB)
private theorem addi_x5_3_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 76) (.ADDI .x5 .x0 3)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 11
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 11) = (44 : Word) from by native_decide,
      show (base + 32 : Word) + 44 = base + 76 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- BNE x7 x0 16 at base+80 (index 12 of phaseB)
private theorem bne_x7_16_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 80) (.BNE .x7 .x0 16)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 12
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 12) = (48 : Word) from by native_decide,
      show (base + 32 : Word) + 48 = base + 80 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- ADDI x5 x0 2 at base+84 (index 13 of phaseB)
private theorem addi_x5_2_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 84) (.ADDI .x5 .x0 2)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 13
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 13) = (52 : Word) from by native_decide,
      show (base + 32 : Word) + 52 = base + 84 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- BNE x6 x0 8 at base+88 (index 14 of phaseB)
private theorem bne_x6_8_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 88) (.BNE .x6 .x0 8)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 14
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 14) = (56 : Word) from by native_decide,
      show (base + 32 : Word) + 56 = base + 88 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- ADDI x5 x0 1 at base+92 (index 15 of phaseB)
private theorem addi_x5_1_sub_modCode (base : Word) :
    ∀ a i, (CodeReq.singleton (base + 92) (.ADDI .x5 .x0 1)) a = some i →
      (modCode base) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + 32) divK_phaseB 15
    (by native_decide) (by native_decide)
  rw [show BitVec.ofNat 64 (4 * 15) = (60 : Word) from by native_decide,
      show (base + 32 : Word) + 60 = base + 92 from by bv_addr] at hlookup
  have h1 := CodeReq.singleton_mono hlookup a i h
  exact CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range _ _ _ _
      (fun k1 k2 hk1 hk2 => by simp only [divK_phaseA_len, divK_phaseB_len] at hk1 hk2; bv_omega))
    (CodeReq.union_mono_left _ _) a i h1

-- ============================================================================
-- MOD Phase B cascade constants and address lemmas
-- ============================================================================

-- signExtend constants for cascade steps
private theorem mod_divK_se12_3 : signExtend12 (3 : BitVec 12) = (3 : Word) := by native_decide
private theorem mod_divK_se12_2 : signExtend12 (2 : BitVec 12) = (2 : Word) := by native_decide
private theorem mod_divK_se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by native_decide
private theorem mod_signExtend13_16 : signExtend13 (16 : BitVec 13) = (16 : Word) := by
  native_decide
private theorem mod_signExtend13_8 : signExtend13 (8 : BitVec 13) = (8 : Word) := by native_decide

-- nm1_x8 = (n + signExtend12 4095) <<< 3 for each n value
private theorem mod_divK_phaseB_n3_nm1_x8 :
    ((3 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (16 : Word) := by
  native_decide
private theorem mod_divK_phaseB_n2_nm1_x8 :
    ((2 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (8 : Word) := by
  native_decide
private theorem mod_divK_phaseB_n1_nm1_x8 :
    ((1 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (0 : Word) := by
  native_decide

-- Cascade address normalization
private theorem mod_phB_step1_4 (base : Word) : (base + 76 : Word) + 4 = base + 80 := by bv_addr
private theorem mod_phB_step1_8 (base : Word) : (base + 80 : Word) + 4 = base + 84 := by bv_addr
private theorem mod_phB_step2_4 (base : Word) : (base + 84 : Word) + 4 = base + 88 := by bv_addr
private theorem mod_phB_step2_8 (base : Word) : (base + 88 : Word) + 4 = base + 92 := by bv_addr
private theorem mod_phB_fall_4 (base : Word) : (base + 92 : Word) + 4 = base + 96 := by bv_addr

-- Tail memory address normalization
private theorem mod_phB_sp16_32 (sp : Word) :
    (sp + (16 : Word) + (32 : Word)) = sp + 48 := by bv_addr
private theorem mod_phB_sp8_32 (sp : Word) :
    (sp + (8 : Word) + (32 : Word)) = sp + 40 := by bv_addr
private theorem mod_phB_sp0_32 (sp : Word) :
    (sp + (0 : Word) + (32 : Word)) = sp + 32 := by bv_addr

-- ============================================================================
-- MOD Phase B n=3 (b[3]=0, b[2]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 taken → tail
-- ============================================================================

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 4096 in
/-- MOD Phase B when b[3]=0, b[2]≠0 (n=3): zero scratch, load b[1..2], cascade to n=3, load b[2].
    Execution: init1(7) + init2(2) + step0(2) + step1(2) + tail(5) = 18 instrs.
    Exit at base+116 (start of CLZ). x5 = b[2] (leading limb), n = 3. -/
theorem evm_mod_phaseB_n3_spec (sp base : Word)
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
    cpsTriple (base + 32) (base + 116) (modCode base)
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
  simp only [mod_phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_modCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7 hvalid
  simp only [mod_phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_modCode base) hinit2_raw
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
  simp only [mod_phB_addi_4, mod_divK_se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_modCode base) haddi0_raw
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
        rw [mod_signExtend13_24]; bv_addr, mod_phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_modCode base) hbne0_clean
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
  simp only [mod_phB_step1_4, mod_divK_se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_modCode base) haddi1_raw
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
        rw [mod_signExtend13_16]; bv_addr, mod_phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne1_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb2nz)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_modCode base) hbne1_clean
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
    rw [mod_divK_phaseB_n3_nm1_x8, mod_divK_se12_32, mod_phB_sp16_32]
    exact hvalid.get (show 6 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (3 : Word) b2 n_mem (base + 96) hv_n hv_limb
  simp only [mod_phB_t_20, mod_divK_phaseB_n3_nm1_x8, mod_divK_se12_32,
    mod_phB_sp16_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_modCode base) htail_raw
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
-- MOD Phase B n=2 (b[3]=b[2]=0, b[1]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 taken → tail
-- ============================================================================

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 4096 in
/-- MOD Phase B when b[3]=b[2]=0, b[1]≠0 (n=2): zero scratch, cascade to n=2, load b[1].
    Execution: init1(7) + init2(2) + 3×step(6) + tail(5) = 20 instrs.
    Exit at base+116. x5 = b[1] (leading limb), n = 2. -/
theorem evm_mod_phaseB_n2_spec (sp base : Word)
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
    cpsTriple (base + 32) (base + 116) (modCode base)
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
  simp only [mod_phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_modCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7 hvalid
  simp only [mod_phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_modCode base) hinit2_raw
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
  simp only [mod_phB_addi_4, mod_divK_se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_modCode base) haddi0_raw
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
        rw [mod_signExtend13_24]; bv_addr, mod_phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_modCode base) hbne0_clean
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
  simp only [mod_phB_step1_4, mod_divK_se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_modCode base) haddi1_raw
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
        rw [mod_signExtend13_16]; bv_addr, mod_phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_modCode base) hbne1_clean
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
  simp only [mod_phB_step2_4, mod_divK_se12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_modCode base) haddi2_raw
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
        rw [mod_signExtend13_8]; bv_addr, mod_phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_elim_taken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb1nz)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_modCode base) hbne2_clean
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
    rw [mod_divK_phaseB_n2_nm1_x8, mod_divK_se12_32, mod_phB_sp8_32]
    exact hvalid.get (show 5 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (2 : Word) b1 n_mem (base + 96) hv_n hv_limb
  simp only [mod_phB_t_20, mod_divK_phaseB_n2_nm1_x8, mod_divK_se12_32,
    mod_phB_sp8_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_modCode base) htail_raw
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
-- MOD Phase B n=1 (b[3]=b[2]=b[1]=0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 ntaken → ADDI x5=1 → tail
-- ============================================================================

set_option maxHeartbeats 51200000 in
set_option maxRecDepth 4096 in
/-- MOD Phase B when b[3]=b[2]=b[1]=0 (n=1): zero scratch, cascade falls through all BNEs, load b[0].
    Execution: all 21 instructions of divK_phaseB.
    Exit at base+116. x5 = b[0] (leading limb), n = 1.
    Note: b[0] must be in precondition since the tail loads from sp+32. -/
theorem evm_mod_phaseB_n1_spec (sp base : Word)
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
    cpsTriple (base + 32) (base + 116) (modCode base)
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
  simp only [mod_phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_modCode base) hinit1_raw
  have hinit1f := cpsTriple_frame_left _ _ _ _ _
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ n_mem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7 hvalid
  simp only [mod_phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_modCode base) hinit2_raw
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
  simp only [mod_phB_addi_4, mod_divK_se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_modCode base) haddi0_raw
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
        rw [mod_signExtend13_24]; bv_addr, mod_phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_modCode base) hbne0_clean
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
  simp only [mod_phB_step1_4, mod_divK_se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_modCode base) haddi1_raw
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
        rw [mod_signExtend13_16]; bv_addr, mod_phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_modCode base) hbne1_clean
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
  simp only [mod_phB_step2_4, mod_divK_se12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_modCode base) haddi2_raw
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
        rw [mod_signExtend13_8]; bv_addr, mod_phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_elim_ntaken_strip_pure2 _ _ _ _ _ _ _ _ _ hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb1z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_modCode base) hbne2_clean
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
  simp only [mod_phB_fall_4, mod_divK_se12_1] at haddi3_raw
  have haddi3 := cpsTriple_extend_code (addi_x5_1_sub_modCode base) haddi3_raw
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
    rw [mod_divK_phaseB_n1_nm1_x8, mod_divK_se12_32, mod_phB_sp0_32]
    exact hvalid.get (show 4 < 8 from by omega)
  have htail_raw := divK_phaseB_tail_spec sp (1 : Word) b0 n_mem (base + 96) hv_n hv_limb
  simp only [mod_phB_t_20, mod_divK_phaseB_n1_nm1_x8, mod_divK_se12_32,
    mod_phB_sp0_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_modCode base) htail_raw
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

end EvmAsm.Rv64
