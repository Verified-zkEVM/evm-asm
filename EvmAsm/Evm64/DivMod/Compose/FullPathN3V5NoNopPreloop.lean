/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopPreloop

  The v5 n=3 preloop execution-spec chain (entry → loop setup) over
  `divCode_noNop_v5`.  The n=3 analog of `FullPathN2V5NoNopPreloop`, and the
  V4→V5 lift of the n=3 preloop pieces in `FullPathN3V4NoNopPreloop` /
  `PhaseABV4NoNop`: the preloop instructions are identical between v4 and v5
  (they precede the div128 block), so each piece re-proves over `divCode_noNop_v5`
  by swapping the per-instruction code-subsumption lemmas `*_sub_divCode_noNop_v4`
  → `*_sub_divCode_noNop_v5` (PhaseBV5).  Bead `evm-asm-wbc4i.9.3.3.1`.

  This file currently provides phase B (n=3 divisor-width detection: b3=0, b2≠0,
  writing nMem=3).  The branch structure differs from n=2: the `bne x7` (b2)
  check is TAKEN (b2≠0), jumping straight to the tail with x5=3.
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseBV5
import EvmAsm.Evm64.DivMod.Compose.PhaseAV5
import EvmAsm.Evm64.DivMod.Compose.CLZV5
import EvmAsm.Evm64.DivMod.Compose.PhaseC2V5
import EvmAsm.Evm64.DivMod.Compose.NormBV5
import EvmAsm.Evm64.DivMod.Compose.NormAV5
import EvmAsm.Evm64.DivMod.Compose.LoopSetupV5
import EvmAsm.Evm64.DivMod.Compose.PhaseABV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 phase-B (n=3 detection: b3=0, b2≠0), over `divCode_noNop_v5`.
    V4→V5 lift of `evm_div_phaseB_n3_spec_within_v4_noNop` (swapping the
    per-instruction code-subsumption lemmas to their v5 forms). -/
theorem evm_div_phaseB_n3_spec_within_v5_noNop (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTripleWithin 21 (base + phaseBOff) (base + clzOff) (divCode_noNop_v5 base)
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
    (fun h hp => by xperm_chunked hp) hinit1f hinit2f
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
    (fun h hp => by xperm_chunked hp) h12 haddi0f
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
    (fun h hp => by xperm_chunked hp) h123 hbne0f
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
    (fun h hp => by xperm_chunked hp) h1234 haddi1f
  have hbne1_raw := bne_spec_gen_within .x7 .x0 16 b2 (0 : Word) (base + phaseBBne2Off)
  rw [show (base + phaseBBne2Off : Word) + signExtend13 16 = base + phaseBTailOff from by
        rv64_addr, phB_step1_8_v4] at hbne1_raw
  have hbne1_clean := cpsBranchWithin_takenStripPure2 hbne1_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb2nz)
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
    (fun h hp => by xperm_chunked hp) h12345 hbne1f
  have htail_raw := divK_phaseB_tail_spec_within sp (3 : Word) b2 nMem (base + phaseBTailOff)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20_v4, divK_phaseB_n3_nm1_x8_v4, signExtend12_32, phB_sp16_32_v4] at htail_raw
  have htail := cpsTripleWithin_extend_code divK_phaseB_tail_code_sub_divCode_noNop_v5 htail_raw
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

/-- PhaseA(ntaken) + PhaseB(n=3) + CLZ(b2) over `divCode_noNop_v5`.
    Mirror of `evm_div_phaseAB_n2_clz_spec_within_v5_noNop`, with phase-B n=3 and
    the CLZ taken on `b2` (the n=3 top divisor limb). -/
theorem evm_div_phaseAB_n3_clz_spec_within_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24) base (base + phaseC2Off) (divCode_noNop_v5 base)
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
  have hA := evm_div_phaseA_ntaken_spec_within_v5_noNop sp base b0 b1 b2 b3 v5 v10 hbnz
  have hAf := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
     ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hA
  have hB := evm_div_phaseB_n3_spec_within_v5_noNop sp base b1 b2 b3
    (b0 ||| b1 ||| b2 ||| b3) v6 v7 q0 q1 q2 q3 u5 u6 u7 nMem
    hb3z hb2nz
  have hBf := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ b0))
    (by pcFree) hB
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  have hCLZ := divK_clz_spec_within_v5_noNop b2 b1 b2 base
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

/-- PhaseAB(n=3) + CLZ + PhaseC2(ntaken) + NormB over `divCode_noNop_v5`. -/
theorem evm_div_n3_to_normB_spec_within_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (normBPost sp (3 : Word) (clzResult b2).1 b0 b1 b2 b3) := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  have hABCLZ := evm_div_phaseAB_n3_clz_spec_within_v5_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2nz
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_ntaken_spec_within_v5_noNop sp shift ((clzResult b2).2 >>> (63 : Nat))
    shiftMem base hshift_nz
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b2).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  have hNB := divK_normB_full_spec_within_v5_noNop sp b0 b1 b2 b3
    (clzResult b2).2 ((clzResult b2).2 >>> (63 : Nat))
    shift antiShift base
  simp only [normBFullPost_unfold] at hNB
  have hNBf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2 hNBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta normBPost; xperm_hyp hq)
    hFull

/-- n=3 preloop entry-to-loopSetup over `divCode_noNop_v5`. base → base+loopBodyOff. -/
theorem evm_div_n3_to_loopSetup_spec_within_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
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
      (loopSetupPost sp (3 : Word) (clzResult b2).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have hNB := evm_div_n3_to_normB_spec_within_v5_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3z hb2nz hshift_nz
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
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNormA
  have hNA := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by delta normBPost at hp; xperm_hyp hp) hNBf hNormAf
  have hLS := divK_loopSetup_ntaken_spec_within_v5_noNop sp (3 : Word)
    x9In u1 base
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

/-- n=3 v5/no-NOP entry→loopSetup with the loop's x1+scratch frame already in
    place.  frameR + weaken around `evm_div_n3_to_loopSetup_spec_within_v5_noNop`. -/
theorem evm_div_n3_to_loopSetup_spec_within_v5_noNop_exact_x1_scratch_frame
    (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff)
      (divCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
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
      (loopSetupPost sp (3 : Word) (clzResult b2).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  have hPre :=
    evm_div_n3_to_loopSetup_spec_within_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3
      v5 v6 v7 v10 q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In
      hbnz hb3z hb2nz hshift_nz
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

end EvmAsm.Evm64
