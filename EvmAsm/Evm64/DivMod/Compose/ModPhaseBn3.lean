/-
  MOD Phase B n=3 composition (b[3]=0, b[2]≠0).
  Mirrors evm_div_phaseB_n3_spec with modCode.
-/
import EvmAsm.Evm64.DivMod.Compose.ModPhaseB
open EvmAsm.Rv64.Tactics
namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (se12_3 se12_4)
open EvmAsm.Rv64.AddrNorm (se12_32)

-- ============================================================================
-- MOD Phase B n=3 (b[3]=0, b[2]≠0)
-- init1 → init2 → ADDI x5=4 → BNE x10 ntaken → ADDI x5=3 → BNE x7 taken → tail
-- ============================================================================

/-- MOD Phase B when b[3]=0, b[2]≠0 (n=3): zero scratch, load b[1..2], cascade to n=3, load b[2].
    Execution: init1(7) + init2(2) + step0(2) + step1(2) + tail(5) = 18 instrs.
    Exit at base+116 (start of CLZ). x5 = b[2] (leading limb), n = 3. -/
theorem evm_mod_phaseB_n3_spec (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTriple (base + phaseBOff) (base + clzOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (3 : Word))) := by
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
  rw [show (base + 72 : Word) + signExtend13 24 = base + 96 from by rv64_addr,
      mod_phB_bne_4] at hbne0_raw
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
  -- ---- Cascade step 1: BNE x7 taken (base+80 → base+96, b2≠0)
  have hbne1_raw := bne_spec_gen .x7 .x0 16 b2 (0 : Word) (base + 80)
  rw [show (base + 80 : Word) + signExtend13 16 = base + 96 from by rv64_addr,
      mod_phB_step1_8] at hbne1_raw
  have hbne1_clean := cpsBranch_takenStripPure2 hbne1_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _ _ _).mp h_rest).2 hb2nz)
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
  -- ---- Tail (base+96 → base+116)
  have htail_raw := divK_phaseB_tail_spec sp (3 : Word) b2 nMem (base + 96)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
    mod_phB_t_20, mod_divK_phaseB_n3_nm1_x8, se12_32,
    mod_phB_sp16_32] at htail_raw
  have htail := cpsTriple_extend_code (divK_phaseB_tail_code_sub_modCode base) htail_raw
  have htailf := cpsTriple_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTriple_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456 htailf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

end EvmAsm.Evm64
