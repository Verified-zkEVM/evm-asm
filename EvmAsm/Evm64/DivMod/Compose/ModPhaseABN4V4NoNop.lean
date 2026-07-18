/-
  EvmAsm.Evm64.DivMod.Compose.ModPhaseABN4V4NoNop

  v4/no-NOP MOD PhaseA/PhaseB n=4 wrappers.
-/

import EvmAsm.Evm64.DivMod.Compose.V4Code
import EvmAsm.Evm64.DivMod.Compose.ModCLZ
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseA
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBInit
import EvmAsm.Evm64.DivMod.LimbSpec.PhaseBTail

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm
  (bv64_4mul_9 bv64_4mul_10 bv64_4mul_11 bv64_4mul_12 se12_32)
open EvmAsm.Evm64.DivMod.AddrNorm (se12_3)

private theorem divK_phaseA_code_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (divK_phaseA_code base) a = some i → (modCode_noNop_v4 base) a = some i := by
  unfold divK_phaseA_code
  intro a i h
  exact sharedNoNop_v4_b0_mod a i h

private theorem beq_phaseA_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseABeqOff) (.BEQ .x5 .x0 1020)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  exact sharedNoNop_v4_b0_mod a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1020) 7
      (by decide) (by decide)) a i h)

private theorem divK_phaseB_init1_code_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (divK_phaseB_init1_code (base + phaseBOff)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBOff) divK_phaseB
    (divK_phaseB.take 7) 0
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sharedNoNop_v4_b1_mod a i h1

private theorem divK_phaseB_init2_code_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (divK_phaseB_init2_code (base + phaseBInit2Off)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBInit2Off) divK_phaseB
    (divK_phaseB.drop 7 |>.take 2) 7
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sharedNoNop_v4_b1_mod a i h1

private theorem divK_phaseB_tail_code_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (divK_phaseB_tail_code (base + phaseBTailOff)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  have h1 := CodeReq.ofProg_mono_sub (base + phaseBOff) (base + phaseBTailOff) divK_phaseB
    (divK_phaseB.drop 16) 16
    (by bv_addr) (by decide) (by decide) (by decide) a i h
  exact sharedNoNop_v4_b1_mod a i h1

private theorem addi_x5_singleton_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBStep0Off) (.ADDI .x5 .x0 4)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 9
    (by decide) (by decide)
  rw [bv64_4mul_9,
      show (base + phaseBOff : Word) + 36 = base + phaseBStep0Off from by bv_addr] at hlookup
  exact sharedNoNop_v4_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

private theorem bne_x10_singleton_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBBneOff) (.BNE .x10 .x0 24)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 10
    (by decide) (by decide)
  rw [bv64_4mul_10,
      show (base + phaseBOff : Word) + 40 = base + phaseBBneOff from by bv_addr] at hlookup
  exact sharedNoNop_v4_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

private theorem addi_x5_3_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBStep1Off) (.ADDI .x5 .x0 3)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 11
    (by decide) (by decide)
  rw [bv64_4mul_11,
      show (base + phaseBOff : Word) + 44 = base + phaseBStep1Off from by bv_addr] at hlookup
  exact sharedNoNop_v4_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

private theorem bne_x7_16_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseBBne2Off) (.BNE .x7 .x0 16)) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseBOff) divK_phaseB 12
    (by decide) (by decide)
  rw [bv64_4mul_12,
      show (base + phaseBOff : Word) + 48 = base + phaseBBne2Off from by bv_addr] at hlookup
  exact sharedNoNop_v4_b1_mod a i (CodeReq.singleton_mono hlookup a i h)

private theorem phB_i2_8_mod_v4 {base : Word} :
    (base + phaseBInit2Off : Word) + 8 = base + phaseBStep0Off := by bv_addr
private theorem phB_addi_4_mod_v4 {base : Word} :
    (base + phaseBStep0Off : Word) + 4 = base + phaseBBneOff := by bv_addr
private theorem phB_bne_4_mod_v4 {base : Word} :
    (base + phaseBBneOff : Word) + 4 = base + phaseBStep1Off := by bv_addr
private theorem phB_step1_4_mod_v4 {base : Word} :
    (base + phaseBStep1Off : Word) + 4 = base + phaseBBne2Off := by bv_addr
private theorem phB_step1_8_mod_v4 {base : Word} :
    (base + phaseBBne2Off : Word) + 4 = base + phaseBStep2Off := by bv_addr
private theorem phB_t_20_mod_v4 {base : Word} :
    (base + phaseBTailOff : Word) + 20 = base + clzOff := by bv_addr
private theorem divK_phaseB_n4_nm1_x8_mod_v4 :
    ((4 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (24 : Word) := by
  decide
private theorem divK_phaseB_n3_nm1_x8_mod_v4 :
    ((3 : Word) + signExtend12 (4095 : BitVec 12)) <<< (3 : BitVec 6).toNat = (16 : Word) := by
  decide
private theorem phB_sp24_32_mod_v4 {sp : Word} :
    (sp + (24 : Word) + (32 : Word)) = sp + 56 := by
  bv_addr
private theorem phB_sp16_32_mod_v4 {sp : Word} :
    (sp + (16 : Word) + (32 : Word)) = sp + 48 := by
  bv_addr

/-- PhaseA nonzero path over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_phaseA_ntaken_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    cpsTripleWithin 8 base (base + phaseBOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have hbody := cpsTripleWithin_extend_code divK_phaseA_code_sub_modCode_noNop_v4
    (divK_phaseA_body_spec_within sp base b0 b1 b2 b3 v5 v10)
  have hbeq_raw := beq_spec_gen_within .x5 .x0 1020 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + phaseABeqOff)
  rw [show (base + phaseABeqOff : Word) + signExtend13 1020 = base + zeroPathOff from by rv64_addr,
      show (base + phaseABeqOff : Word) + 4 = base + phaseBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hbnz)
  have hbeq := cpsTripleWithin_extend_code beq_phaseA_sub_modCode_noNop_v4 hbeq_clean
  have hbeq_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

/-- PhaseB n=4 over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_phaseB_n4_spec_within_v4_noNop (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3nz : b3 ≠ 0) :
    cpsTripleWithin 21 (base + phaseBOff) (base + clzOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  have hinit1_raw := divK_phaseB_init1_spec_within sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTripleWithin_extend_code divK_phaseB_init1_code_sub_modCode_noNop_v4 hinit1_raw
  have hinit1f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  have hinit2_raw := divK_phaseB_init2_spec_within sp (base + phaseBInit2Off) b1 b2 v6 v7
  simp only [phB_i2_8_mod_v4] at hinit2_raw
  have hinit2 := cpsTripleWithin_extend_code divK_phaseB_init2_code_sub_modCode_noNop_v4 hinit2_raw
  seqFrame hinit1f hinit2
  have haddi_raw := addi_x0_spec_gen_within .x5 v5 4 (base + phaseBStep0Off) (by nofun)
  simp only [phB_addi_4_mod_v4, signExtend12_4] at haddi_raw
  have haddi := cpsTripleWithin_extend_code addi_x5_singleton_sub_modCode_noNop_v4 haddi_raw
  seqFrame hinit1fhinit2 haddi
  have hbne_raw := bne_spec_gen_within .x10 .x0 24 b3 (0 : Word) (base + phaseBBneOff)
  rw [show (base + phaseBBneOff : Word) + signExtend13 24 = base + phaseBTailOff from by
        rv64_addr, phB_bne_4_mod_v4] at hbne_raw
  have hbne_clean := cpsBranchWithin_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb3nz)
  have hbne := cpsTripleWithin_extend_code bne_x10_singleton_sub_modCode_noNop_v4 hbne_clean
  seqFrame hinit1fhinit2haddi hbne
  have htail_raw := divK_phaseB_tail_spec_within sp (4 : Word) b3 nMem (base + phaseBTailOff)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20_mod_v4, divK_phaseB_n4_nm1_x8_mod_v4, signExtend12_32,
             phB_sp24_32_mod_v4] at htail_raw
  have htail := cpsTripleWithin_extend_code divK_phaseB_tail_code_sub_modCode_noNop_v4 htail_raw
  seqFrame hinit1fhinit2haddihbne htail
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hinit1fhinit2haddihbnehtail

/-- PhaseB n=3 over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_phaseB_n3_spec_within_v4_noNop (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTripleWithin 21 (base + phaseBOff) (base + clzOff) (modCode_noNop_v4 base)
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
  have hinit1_raw := divK_phaseB_init1_spec_within sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTripleWithin_extend_code divK_phaseB_init1_code_sub_modCode_noNop_v4 hinit1_raw
  have hinit1f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  have hinit2_raw := divK_phaseB_init2_spec_within sp (base + phaseBInit2Off) b1 b2 v6 v7
  simp only [phB_i2_8_mod_v4] at hinit2_raw
  have hinit2 := cpsTripleWithin_extend_code divK_phaseB_init2_code_sub_modCode_noNop_v4 hinit2_raw
  have hinit2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  have haddi0_raw := addi_x0_spec_gen_within .x5 v5 4 (base + phaseBStep0Off) (by nofun)
  simp only [phB_addi_4_mod_v4, signExtend12_4] at haddi0_raw
  have haddi0 := cpsTripleWithin_extend_code addi_x5_singleton_sub_modCode_noNop_v4 haddi0_raw
  have haddi0f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi0
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  have hbne0_raw := bne_spec_gen_within .x10 .x0 24 b3 (0 : Word) (base + phaseBBneOff)
  rw [show (base + phaseBBneOff : Word) + signExtend13 24 = base + phaseBTailOff from by
        rv64_addr, phB_bne_4_mod_v4] at hbne0_raw
  have hbne0_clean := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _).mp h_rest).2)
  have hbne0 := cpsTripleWithin_extend_code bne_x10_singleton_sub_modCode_noNop_v4 hbne0_clean
  have hbne0f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne0
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  have haddi1_raw := addi_x0_spec_gen_within .x5 (4 : Word) 3 (base + phaseBStep1Off) (by nofun)
  simp only [phB_step1_4_mod_v4, se12_3] at haddi1_raw
  have haddi1 := cpsTripleWithin_extend_code addi_x5_3_sub_modCode_noNop_v4 haddi1_raw
  have haddi1f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi1
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  have hbne1_raw := bne_spec_gen_within .x7 .x0 16 b2 (0 : Word) (base + phaseBBne2Off)
  rw [show (base + phaseBBne2Off : Word) + signExtend13 16 = base + phaseBTailOff from by
        rv64_addr, phB_step1_8_mod_v4] at hbne1_raw
  have hbne1_clean := cpsBranchWithin_takenStripPure2 hbne1_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb2nz)
  have hbne1 := cpsTripleWithin_extend_code bne_x7_16_sub_modCode_noNop_v4 hbne1_clean
  have hbne1f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne1
  have h123456 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  have htail_raw := divK_phaseB_tail_spec_within sp (3 : Word) b2 nMem (base + phaseBTailOff)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20_mod_v4, divK_phaseB_n3_nm1_x8_mod_v4, signExtend12_32,
             phB_sp16_32_mod_v4] at htail_raw
  have htail := cpsTripleWithin_extend_code divK_phaseB_tail_code_sub_modCode_noNop_v4 htail_raw
  have htailf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123456 htailf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

/-- PhaseAB n=3 over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_phaseAB_n3_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTripleWithin (8 + 21) base (base + clzOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word))) := by
  have hA := evm_mod_phaseA_ntaken_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v10 hbnz
  have hAf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
     ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hA
  have hB := evm_mod_phaseB_n3_spec_within_v4_noNop sp base b1 b2 b3
    (b0 ||| b1 ||| b2 ||| b3) v6 v7 q0 q1 q2 q3 u5 u6 u7 nMem
    hb3z hb2nz
  have hBf := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0))
    (by pcFree) hB
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

/-- MOD PhaseAB n=3 plus CLZ over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_phaseAB_n3_clz_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24) base (base + phaseC2Off) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b2).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b2).1) ** (.x7 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word))) := by
  have hAB := evm_mod_phaseAB_n3_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2nz
  have hCLZ := mod_clz_spec_within_v4_noNop b2 b1 b2 base
  have hCLZf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)))
    (by pcFree) hCLZ
  have hABCLZ := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hCLZf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABCLZ

/-- PhaseA nonzero path over the full v4 MOD code bundle. -/
theorem evm_mod_phaseA_ntaken_spec_within_v4 (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    cpsTripleWithin 8 base (base + phaseBOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_phaseA_ntaken_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v10 hbnz)

/-- PhaseB n=4 over the full v4 MOD code bundle. -/
theorem evm_mod_phaseB_n4_spec_within_v4 (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3nz : b3 ≠ 0) :
    cpsTripleWithin 21 (base + phaseBOff) (base + clzOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_phaseB_n4_spec_within_v4_noNop sp base b1 b2 b3 v5 v6 v7
      q0 q1 q2 q3 u5 u6 u7 nMem hb3nz)

/-- PhaseAB n=4 over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_phaseAB_n4_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    cpsTripleWithin (8 + 21) base (base + clzOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  have hA := evm_mod_phaseA_ntaken_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v10 hbnz
  have hAf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
     ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hA
  have hB := evm_mod_phaseB_n4_spec_within_v4_noNop sp base b1 b2 b3
    (b0 ||| b1 ||| b2 ||| b3) v6 v7 q0 q1 q2 q3 u5 u6 u7 nMem
    hb3nz
  have hBf := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0))
    (by pcFree) hB
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

/-- PhaseAB n=4 over the full v4 MOD code bundle. -/
theorem evm_mod_phaseAB_n4_spec_within_v4 (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    cpsTripleWithin (8 + 21) base (base + clzOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b3) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 32) ↦ₘ b0) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_phaseAB_n4_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
      q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz)

/-- MOD PhaseAB n=4 plus CLZ over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_phaseAB_n4_clz_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24) base (base + phaseC2Off) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b3).1) ** (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  have hAB := evm_mod_phaseAB_n4_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz
  have hCLZ := mod_clz_spec_within_v4_noNop b3 b1 b2 base
  have hCLZf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hCLZ
  have hABCLZ := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hCLZf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABCLZ

/-- MOD PhaseAB n=4 plus CLZ over the full v4 MOD code bundle. -/
theorem evm_mod_phaseAB_n4_clz_spec_within_v4 (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24) base (base + phaseC2Off) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b3).1) ** (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word))) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (evm_mod_phaseAB_n4_clz_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
      q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz)

end EvmAsm.Evm64
