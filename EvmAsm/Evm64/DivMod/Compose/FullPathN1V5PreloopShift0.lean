/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5PreloopShift0

  v5 n=1 shift=0 preloop composition over `divCode_noNop_v5`.  On the shift = 0
  branch the divisor is already top-bit-aligned, so normalization is skipped:
  phase-C2 takes the BEQ to copyAU, the dividend is copied verbatim into the
  u-cells, and loop-setup falls through to the loop body.  This file composes the
  shift=0-specific middle segment `copyAU + loopSetup` (copyAUOff → loopBodyOff),
  the analog of the shift≠0 `normB + normA + loopSetup` tail in
  `FullPathN1V5Preloop`.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.CopyAUV5
import EvmAsm.Evm64.DivMod.Compose.LoopSetupV5
import EvmAsm.Evm64.DivMod.Compose.PhaseC2V5
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Preloop

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- v5 shift=0 middle segment: copy-AU then loop-setup (BLT-not-taken), from
    `copyAUOff` to `loopBodyOff`, over `divCode_noNop_v5`.  The dividend `a[0..3]`
    lands in the u-cells (`u[4]` zeroed) and the loop counter `x5 ← n`,
    `x9 ← m = 4 − n`.  `hm_ge` rules out the degenerate `n > 4` BLT-taken case
    (holds for the n=1 lane where `n = 1`). -/
theorem divK_copyAU_loopSetup_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 v5 v1 n : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    cpsTripleWithin 13 (base + copyAUOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x9 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - n)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have hCopy := divK_copyAU_spec_within_v5_noNop sp base a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
  have hCopyF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hCopy
  have hLS := divK_loopSetup_ntaken_spec_within_v5_noNop sp n v1 a3 base hm_ge
  simp only [divKLoopSetupNtakenPreNoNop_unfold, divKLoopSetupNtakenPostNoNop_unfold] at hLS
  have hLSF := cpsTripleWithin_frameR
    (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
     ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word)))
    (by pcFree) hLS
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hCopyF hLSF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

/-- DIV PhaseAB(n=1) + CLZ + PhaseC2(taken, shift=0) over `divCode_noNop_v5`,
    `base → copyAUOff`.  Shift=0 analog of `evm_div_phaseAB_n1_clz_c2_spec_v5_noNop`
    (which goes to normBOff on the not-taken branch). -/
theorem evm_div_phaseAB_n1_clz_c2taken_spec_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_z : (clzResult b0).1 = 0) :
    cpsTripleWithin (8 + 21 + 24 + 4) base (base + copyAUOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b0).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b0).1) **
       (.x7 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b0).1)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)) := by
  have hABCLZ := evm_div_phaseAB_n1_clz_spec_v5_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2z hb1z
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ x2In) ** ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_taken_spec_within_v5_noNop sp (clzResult b0).1
    x2In shiftMem base hshift_z
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b0).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABC2

/-- Full n=1 shift=0 preloop, `base → loopBodyOff`, over `divCode_noNop_v5`.
    Shift=0 analog of `evm_div_n1_to_loopSetup_spec_v5_noNop`: same entry shape,
    but on the shift=0 branch (`(clzResult b0).1 = 0`) the dividend is copied
    verbatim (u-cells ← a-cells, u[4] = 0) instead of normalized.  Loop counter
    `x5 ← 1`, `x9 ← 4 − 1`. -/
theorem evm_div_n1_to_loopSetup_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_z : (clzResult b0).1 = 0) :
    cpsTripleWithin ((8 + 21 + 24 + 4) + 13) base (base + loopBodyOff)
      (divCode_noNop_v5 base)
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
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (1 : Word)) **
       (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (1 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ (clzResult b0).1) **
       (.x7 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b0).1)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)) := by
  have hC2 := evm_div_phaseAB_n1_clz_c2taken_spec_v5_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem shiftMem x2In hbnz hb3z hb2z hb1z hshift_z
  have hC2f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ x9In) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hC2
  have hSeg := divK_copyAU_loopSetup_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 u0Old u1Old u2Old u3Old u4Old (clzResult b0).2
    x9In (1 : Word) (by decide)
  have hSegf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ (clzResult b0).1) **
     (.x7 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
     (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b0).1)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1))
    (by pcFree) hSeg
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [signExtend12_0] at hp ⊢; xperm_hyp hp) hC2f hSegf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [signExtend12_0] at hq ⊢; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
