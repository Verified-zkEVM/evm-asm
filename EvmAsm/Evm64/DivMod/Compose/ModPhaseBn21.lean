/-
  MOD Phase B n=2 and n=1 compositions.
  Mirrors evm_div_phaseB_n2_spec and evm_div_phaseB_n1_spec with modCode.
-/
import EvmAsm.Evm64.DivMod.Compose.ModPhaseB
open EvmAsm.Rv64.Tactics
namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (se12_1 se12_2 se12_3 se12_4)
open EvmAsm.Rv64.AddrNorm (se13_8 se13_16 se13_24 se12_32)

-- ============================================================================
-- MOD Phase B n=2 (b[3]=b[2]=0, b[1]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 taken → tail
-- ============================================================================

/-- MOD Phase B when b[3]=b[2]=0, b[1]≠0 (n=2): zero scratch, cascade to n=2, load b[1].
    Execution: init1(7) + init2(2) + 3×step(6) + tail(5) = 20 instrs.
    Exit at base+116. x5 = b[1] (leading limb), n = 2. -/
theorem evm_mod_phaseB_n2_spec (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0) :
    cpsTriple (base + phaseBOff) (base + clzOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b1) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (2 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_modCode base) hinit1_raw
  have hinit1f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7
  simp only [mod_phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_modCode base) hinit2_raw
  have hinit2f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit2
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [mod_phB_addi_4, se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_modCode base) haddi0_raw
  have haddi0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rw [se13_24]; bv_addr, mod_phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_modCode base) hbne0_clean
  have hbne0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [mod_phB_step1_4, se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_modCode base) haddi1_raw
  have haddi1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 ntaken (base+80 → base+84, b2=0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rw [se13_16]; bv_addr, mod_phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_modCode base) hbne1_clean
  have hbne1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Cascade step 2: ADDI x5=2 (base+84 → base+88)
  have haddi2_raw := addi_x0_spec_gen .x5 (3 : Word) 2 (base + 84) (by nofun)
  simp only [mod_phB_step2_4, se12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_modCode base) haddi2_raw
  have haddi2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi2
  have h1234567 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456 haddi2f
  -- ---- Cascade step 2: BNE x6 taken (base+88 → base+96, b1≠0)
  have hbne2_raw := bne_spec_gen .x6 .x0 8 b1 (0 : Word) (base + 88)
  rw [show (base + 88 : Word) + signExtend13 8 = base + 96 from by
        rw [se13_8]; bv_addr, mod_phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_takenStripPure2 hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb1nz)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_modCode base) hbne2_clean
  have hbne2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne2
  have h12345678 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234567 hbne2f
  -- ---- Tail (base+96 → base+116)
  have htail_raw := divK_phaseB_tail_spec sp (2 : Word) b1 nMem (base + 96)
  simp only [mod_phB_t_20, mod_divK_phaseB_n2_nm1_x8, se12_32,
    mod_phB_sp8_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_modCode base) htail_raw
  have htailf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345678 htailf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

-- ============================================================================
-- MOD Phase B n=1 (b[3]=b[2]=b[1]=0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 ntaken
-- → ADDI x5=2 → BNE x6 ntaken → ADDI x5=1 → tail
-- ============================================================================

/-- MOD Phase B when b[3]=b[2]=b[1]=0 (n=1): zero scratch, cascade falls through all BNEs, load b[0].
    Execution: all 21 instructions of divK_phaseB.
    Exit at base+116. x5 = b[0] (leading limb), n = 1.
    Note: b[0] must be in precondition since the tail loads from sp+32. -/
theorem evm_mod_phaseB_n1_spec (sp base : Word)
    (b0 b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0) :
    cpsTriple (base + phaseBOff) (base + clzOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (1 : Word))) := by
  -- ---- init1 (base+32 → base+60)
  have hinit1_raw := divK_phaseB_init1_spec sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTriple_extend_code (divK_phaseB_init1_code_sub_modCode base) hinit1_raw
  have hinit1f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  -- ---- init2 (base+60 → base+68)
  have hinit2_raw := divK_phaseB_init2_spec sp (base + 60) b1 b2 v6 v7
  simp only [mod_phB_i2_8] at hinit2_raw
  have hinit2 := cpsTriple_extend_code (divK_phaseB_init2_code_sub_modCode base) hinit2_raw
  have hinit2f := cpsTriple_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit2
  have h12 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  -- ---- Cascade step 0: ADDI x5=4 (base+68 → base+72)
  have haddi0_raw := addi_x0_spec_gen .x5 v5 4 (base + 68) (by nofun)
  simp only [mod_phB_addi_4, se12_4] at haddi0_raw
  have haddi0 := cpsTriple_extend_code (addi_x5_singleton_sub_modCode base) haddi0_raw
  have haddi0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi0
  have h123 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  -- ---- Cascade step 0: BNE x10 ntaken (base+72 → base+76, b3=0)
  have hbne0_raw := bne_spec_gen .x10 .x0 24 b3 (0 : Word) (base + 72)
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by
        rw [se13_24]; bv_addr, mod_phB_bne_4] at hbne0_raw
  have hbne0_clean := cpsBranch_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne0 := cpsTriple_extend_code (bne_x10_singleton_sub_modCode base) hbne0_clean
  have hbne0f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne0
  have h1234 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  -- ---- Cascade step 1: ADDI x5=3 (base+76 → base+80)
  have haddi1_raw := addi_x0_spec_gen .x5 (4 : Word) 3 (base + 76) (by nofun)
  simp only [mod_phB_step1_4, se12_3] at haddi1_raw
  have haddi1 := cpsTriple_extend_code (addi_x5_3_sub_modCode base) haddi1_raw
  have haddi1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi1
  have h12345 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  -- ---- Cascade step 1: BNE x7 ntaken (base+80 → base+84, b2=0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by
        rw [se13_16]; bv_addr, mod_phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne1 := cpsTriple_extend_code (bne_x7_16_sub_modCode base) hbne1_clean
  have hbne1f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne1
  have h123456 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  -- ---- Cascade step 2: ADDI x5=2 (base+84 → base+88)
  have haddi2_raw := addi_x0_spec_gen .x5 (3 : Word) 2 (base + 84) (by nofun)
  simp only [mod_phB_step2_4, se12_2] at haddi2_raw
  have haddi2 := cpsTriple_extend_code (addi_x5_2_sub_modCode base) haddi2_raw
  have haddi2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi2
  have h1234567 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456 haddi2f
  -- ---- Cascade step 2: BNE x6 ntaken (base+88 → base+92, b1=0)
  have hbne2_raw := bne_spec_gen .x6 .x0 8 b1 (0 : Word) (base + 88)
  rw [show (base + 88 : Word) + signExtend13 8 = base + 96 from by
        rw [se13_8]; bv_addr, mod_phB_step2_8] at hbne2_raw
  have hbne2_clean := cpsBranch_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb1z ((sepConj_pure_right _ _ _).mp h_rest).2)
  have hbne2 := cpsTriple_extend_code (bne_x6_8_sub_modCode base) hbne2_clean
  have hbne2f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne2
  have h12345678 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234567 hbne2f
  -- ---- Fallthrough: ADDI x5=1 (base+92 → base+96)
  have haddi3_raw := addi_x0_spec_gen .x5 (2 : Word) 1 (base + 92) (by nofun)
  simp only [mod_phB_fall_4, se12_1] at haddi3_raw
  have haddi3 := cpsTriple_extend_code (addi_x5_1_sub_modCode base) haddi3_raw
  have haddi3f := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi3
  have h123456789 := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345678 haddi3f
  -- ---- Tail (base+96 → base+116)
  have htail_raw := divK_phaseB_tail_spec sp (1 : Word) b0 nMem (base + 96)
  simp only [mod_phB_t_20, mod_divK_phaseB_n1_nm1_x8, se12_32,
    mod_phB_sp0_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_modCode base) htail_raw
  have htailf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456789 htailf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

end EvmAsm.Evm64
