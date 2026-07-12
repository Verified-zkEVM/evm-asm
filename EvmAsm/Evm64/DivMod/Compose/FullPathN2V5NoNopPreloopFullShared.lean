/-
  Shared declaration home for the n=2 v5/no-NOP preloop, selected loop, and full path.
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseBV5
import EvmAsm.Evm64.DivMod.Compose.PhaseAV5
import EvmAsm.Evm64.DivMod.Compose.CLZV5
import EvmAsm.Evm64.DivMod.Compose.PhaseC2V5
import EvmAsm.Evm64.DivMod.Compose.NormBV5
import EvmAsm.Evm64.DivMod.Compose.NormAV5
import EvmAsm.Evm64.DivMod.Compose.LoopSetupV5
import EvmAsm.Evm64.DivMod.Compose.PhaseABV4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopDispatchShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopLoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- v5 phase-B (n=2 detection: b3=b2=0, b1≠0), over `divCode_noNop_v5`.
    Mirror of `evm_div_phaseB_n2_spec_within_v4_noNop` with v5 code subsumption. -/
theorem evm_div_phaseB_n2_spec_within_v5_noNop (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0) :
    cpsTripleWithin 21 (base + phaseBOff) (base + clzOff) (divCode_noNop_v5 base)
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
  have hinit1_raw := divK_phaseB_init1_spec_within sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTripleWithin_extend_code divK_phaseB_init1_code_sub_divCode_noNop_v5 hinit1_raw
  have hinit1f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  have hinit2_raw := divK_phaseB_init2_spec_within sp (base + phaseBInit2Off) b1 b2 v6 v7
  simp only [phB_i2_8_v4] at hinit2_raw
  have hinit2 := cpsTripleWithin_extend_code divK_phaseB_init2_code_sub_divCode_noNop_v5 hinit2_raw
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
  simp only [phB_addi_4_v4, signExtend12_4] at haddi0_raw
  have haddi0 := cpsTripleWithin_extend_code addi_x5_singleton_sub_divCode_noNop_v5 haddi0_raw
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
        rv64_addr, phB_bne_4_v4] at hbne0_raw
  have hbne0_clean := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _).mp h_rest).2)
  have hbne0 := cpsTripleWithin_extend_code bne_x10_singleton_sub_divCode_noNop_v5 hbne0_clean
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
  simp only [phB_step1_4_v4, signExtend12_3] at haddi1_raw
  have haddi1 := cpsTripleWithin_extend_code addi_x5_3_sub_divCode_noNop_v5 haddi1_raw
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
        rv64_addr, phB_step1_8_v4] at hbne1_raw
  have hbne1_clean := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _).mp h_rest).2)
  have hbne1 := cpsTripleWithin_extend_code bne_x7_16_sub_divCode_noNop_v5 hbne1_clean
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
  have haddi2_raw := addi_x0_spec_gen_within .x5 (3 : Word) 2 (base + phaseBStep2Off) (by nofun)
  simp only [phB_step2_4_v4, signExtend12_2] at haddi2_raw
  have haddi2 := cpsTripleWithin_extend_code addi_x5_2_sub_divCode_noNop_v5 haddi2_raw
  have haddi2f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi2
  have h1234567 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_chunked hp) h123456 haddi2f
  have hbne2_raw := bne_spec_gen_within .x6 .x0 8 b1 (0 : Word) (base + phaseBBne3Off)
  rw [show (base + phaseBBne3Off : Word) + signExtend13 8 = base + phaseBTailOff from by
        rv64_addr, phB_step2_8_v4] at hbne2_raw
  have hbne2_clean := cpsBranchWithin_takenStripPure2 hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb1nz)
  have hbne2 := cpsTripleWithin_extend_code bne_x6_8_sub_divCode_noNop_v5 hbne2_clean
  have hbne2f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne2
  have h12345678 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_chunked hp) h1234567 hbne2f
  have htail_raw := divK_phaseB_tail_spec_within sp (2 : Word) b1 nMem (base + phaseBTailOff)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20_v4, divK_phaseB_n2_nm1_x8_v4, signExtend12_32, phB_sp8_32_v4] at htail_raw
  have htail := cpsTripleWithin_extend_code divK_phaseB_tail_code_sub_divCode_noNop_v5 htail_raw
  have htailf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345678 htailf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

/-- PhaseAB(n=2) + CLZ over `divCode_noNop_v5`. base → base+phaseC2Off. -/
theorem evm_div_phaseAB_n2_clz_spec_within_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24) base (base + phaseC2Off) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b1).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b1).1) ** (.x7 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word))) := by
  have hA := evm_div_phaseA_ntaken_spec_within_v5_noNop sp base b0 b1 b2 b3 v5 v10 hbnz
  have hAf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
     ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hA
  have hB := evm_div_phaseB_n2_spec_within_v5_noNop sp base b1 b2 b3
    (b0 ||| b1 ||| b2 ||| b3) v6 v7 q0 q1 q2 q3 u5 u6 u7 nMem
    hb3z hb2z hb1nz
  have hBf := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0))
    (by pcFree) hB
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  have hCLZ := divK_clz_spec_within_v5_noNop b1 b1 b2 base
  have hCLZf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)))
    (by pcFree) hCLZ
  have hABCLZ := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAB hCLZf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABCLZ

/-- PhaseAB(n=2) + CLZ + PhaseC2(shift≠0) + NormB over `divCode_noNop_v5`. -/
theorem evm_div_n2_to_normB_spec_within_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (normBPost sp (2 : Word) (clzResult b1).1 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  have hABCLZ := evm_div_phaseAB_n2_clz_spec_within_v5_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2z hb1nz
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ x2In) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_ntaken_spec_within_v5_noNop sp shift x2In
    shiftMem base hshift_nz
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b1).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  have hNB := divK_normB_full_spec_within_v5_noNop sp b0 b1 b2 b3
    (clzResult b1).2 ((clzResult b1).2 >>> (63 : Nat))
    shift antiShift base
  simp only [normBFullPost_unfold] at hNB
  have hNBf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2 hNBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta normBPost; xperm_hyp hq)
    hFull

/-- n=2 preloop entry-to-loopSetup over `divCode_noNop_v5`. base → base+loopBodyOff. -/
theorem evm_div_n2_to_loopSetup_spec_within_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       (.x9 ↦ᵣ x9In) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (loopSetupPost sp (2 : Word) (clzResult b1).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b1).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have hNB := evm_div_n2_to_normB_spec_within_v5_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem shiftMem x2In hbnz hb3z hb2z hb1nz hshift_nz
  have hNBf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ x9In) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hNB
  have hNormA := divK_normA_full_spec_within_v5_noNop sp a0 a1 a2 a3
    b0' (b0 >>> (antiShift.toNat % 64)) b3 shift antiShift
    u0Old u1Old u2Old u3Old u4Old base
  rw [divKNormAFullPreNoNop_unfold] at hNormA
  simp only [normAFullPost_unfold] at hNormA
  have hNormAf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (.x9 ↦ᵣ x9In) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ ((b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)))) **
     ((sp + 56) ↦ₘ ((b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)))) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNormA
  have hNA := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by delta normBPost at hp; xperm_hyp hp) hNBf hNormAf
  have hLS := divK_loopSetup_ntaken_spec_within_v5_noNop sp (2 : Word)
    (x9In) u1 base
    (by decide)
  simp only [divKLoopSetupNtakenPreNoNop_unfold,
      divKLoopSetupNtakenPostNoNop_unfold] at hLS
  have hLSf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
     (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ ((b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)))) **
     ((sp + 56) ↦ₘ ((b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)))) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) **
     ((sp + signExtend12 4032) ↦ₘ (a3 <<< (shift.toNat % 64) ||| a2 >>> (antiShift.toNat % 64))) **
     ((sp + signExtend12 4024) ↦ₘ (a3 >>> (antiShift.toNat % 64))) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLS
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hNA hLSf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta loopSetupPost; xperm_hyp hq)
    hFull

/-- n=2 v5/no-NOP entry→loopSetup with the loop's x1+scratch frame already in
    place.  Mirror of `evm_div_n2_to_loopSetup_spec_within_v4_noNop_exact_x1_scratch_frame`
    (frameR + weaken around `evm_div_n2_to_loopSetup_spec_within_v5_noNop`). -/
theorem evm_div_n2_to_loopSetup_spec_within_v5_noNop_exact_x1_scratch_frame
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      (loopSetupPost sp (2 : Word) (clzResult b1).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  have hPre :=
    evm_div_n2_to_loopSetup_spec_within_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3
      v5 v6 v7 v10 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In x2In
      hbnz hb3z hb2z hb1nz hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
      (sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      (sp + signExtend12 3944 ↦ₘ scratchUn0) **
      (sp + signExtend12 3936 ↦ₘ scratchMem) **
      (.x1 ↦ᵣ raVal)))
    (by pcFree) hPre
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFramed

open EvmAsm.Rv64

/-- Instantiated selected-carry n=2 v5 loop, register-slot form. -/
theorem evm_div_n2_loop_unified_inst_noNop_exact_x1_v5_selectedCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift v0' v1' v2' v3' u0S u1S u2S u3S u4_s : Word)
    (v10_val v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u4_s v1')
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false => BitVec.ult (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1'
      | true =>
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
          v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1')
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1')
    (hcarry : loopN2SelectedCarryV5 bltu_2 bltu_1 bltu_0
      v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S) :
    cpsTripleWithin 702 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jMem (2 : Word) shift u0S v10_val v11Old antiShift
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
        u1S u0S (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;>
  (simp only at hbltu_0 hbltu_1 hbltu_2;
   exact divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
     _ _ _ sp base
     jMem (2 : Word) shift u0S v10_val v11Old antiShift
     v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
     (0 : Word) (0 : Word) (0 : Word) raVal
     retMem dMem dloMem scratch_un0 scratchMem
     halign hbltu_2 hbltu_1 hbltu_0 hcarry)

open EvmAsm.Rv64

theorem fullDivN2_preloop_loop_unified_exact_x1_scratch_v5_noNop_selectedCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 =
      BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
        (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false =>
        BitVec.ult (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | true, false =>
        BitVec.ult (iterN2Max (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
                (fullDivN2NormV b0 b1 b2 b3).2.1)
              (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
                (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
                (fullDivN2NormV b0 b1 b2 b3).2.1)
              (fullDivN2NormV b0 b1 b2 b3).1
              (fullDivN2NormV b0 b1 b2 b3).2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1
          (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
              (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1
            (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hcarry : loopN2SelectedCarryV5 bltu_2 bltu_1 bltu_0
      (fullDivN2NormV b0 b1 b2 b3).1
      (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.2
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
      (0 : Word) (0 : Word)
      (fullDivN2NormU a0 a1 a2 a3 b1).2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).1) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 702) base (base + denormOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        (fullDivN2NormV b0 b1 b2 b3).1
        (fullDivN2NormV b0 b1 b2 b3).2.1
        (fullDivN2NormV b0 b1 b2 b3).2.2.1
        (fullDivN2NormV b0 b1 b2 b3).2.2.2
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
        (0 : Word) (0 : Word)
        (fullDivN2NormU a0 a1 a2 a3 b1).2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) := by
  have hPre := evm_div_n2_to_loopSetup_spec_within_v5_noNop_exact_x1_scratch_frame
    sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In
    hbnz hb3z hb2z hb1nz hshift_nz
  have hLoop := evm_div_n2_loop_unified_inst_noNop_exact_x1_v5_selectedCarry
    bltu_2 bltu_1 bltu_0 sp base
    (fullDivN2Shift b1) (fullDivN2AntiShift b1)
    (fullDivN2NormV b0 b1 b2 b3).1
    (fullDivN2NormV b0 b1 b2 b3).2.1
    (fullDivN2NormV b0 b1 b2 b3).2.2.1
    (fullDivN2NormV b0 b1 b2 b3).2.2.2
    (fullDivN2NormU a0 a1 a2 a3 b1).1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
    (a0 >>> ((fullDivN2AntiShift b1).toNat % 64)) v11Old jMem
    retMem dMem dloMem scratchUn0 scratchMem raVal
    halign hbltu_2 (by cases bltu_2 <;> simpa using hbltu_1)
    (by cases bltu_2 <;> cases bltu_1 <;> simpa using hbltu_0) hcarry
  have hLoopf := cpsTripleWithin_frameR
    ((((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
      ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
      ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1)))
    (by pcFree) hLoop
  have hBridge := loopSetupPost_to_loopN2PreWithScratchV4NoX1_framed
    sp a0 a1 a2 a3 b0 b1 b2 b3 v11Old
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal
  have hPre' := cpsTripleWithin_weaken
    (fun h hp => hp)
    hBridge
    hPre
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hPre' hLoopf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hq => hq)
    hFull

end EvmAsm.Evm64
