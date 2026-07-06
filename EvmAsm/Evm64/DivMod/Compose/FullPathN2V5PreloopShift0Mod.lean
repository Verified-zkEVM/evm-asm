/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5PreloopShift0Mod

  v5 n=2 shift=0 preloop pieces over `modCode_noNop_v5`.  On the shift=0 branch
  the divisor is already top-bit-aligned, so normalization is skipped: phase-C2
  takes the BEQ to copyAU.  This file builds the n=2 phaseAB-clz + phaseC2-taken
  segment (`base → copyAUOff`), the n=2 analog of
  `evm_mod_phaseAB_n1_clz_c2taken_spec_v5_noNop`.  Composes the n=2 phaseAB clz
  (`evm_mod_phaseAB_n2_clz_spec_within_v5_noNop`) with the shared shift=0 phase-C2
  branch (`divK_phaseC2_taken_spec_within_v5_noNop_mod`).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopPreloopMod
import EvmAsm.Evm64.DivMod.Compose.PhaseC2V5Mod
import EvmAsm.Evm64.DivMod.Compose.CopyAUV5Mod
import EvmAsm.Evm64.DivMod.Compose.LoopSetupV5Mod

namespace EvmAsm.Evm64

open EvmAsm.Rv64


/-- MOD v5 copyAU + loop setup for the shift=0 path. -/
theorem divK_copyAU_loopSetup_shift0_spec_v5_noNop_mod (sp base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 v5 v1 n : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    cpsTripleWithin 13 (base + copyAUOff) (base + loopBodyOff) (modCode_noNop_v5 base)
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
  have hCopy := divK_copyAU_spec_within_v5_noNop_mod sp base a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
  have hCopyF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hCopy
  have hLS := divK_loopSetup_ntaken_spec_within_v5_noNop_mod sp n v1 a3 base hm_ge
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

/-- v5 n=2 phaseAB-clz + phaseC2(shift=0 taken), `base → copyAUOff`, over
    `modCode_noNop_v5`.  Shift=0 branch (`(clzResult b1).1 = 0`): the divisor is
    already aligned, so phase-C2 takes the BEQ to copyAU. -/
theorem evm_mod_phaseAB_n2_clz_c2taken_spec_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0) :
    cpsTripleWithin (8 + 21 + 24 + 4) base (base + copyAUOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b1).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b1).1) ** (.x7 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b1).1)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1)) := by
  have hABCLZ := evm_mod_phaseAB_n2_clz_spec_within_v5_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2z hb1nz
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2) ** ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_taken_spec_within_v5_noNop_mod sp (clzResult b1).1
    v2 shiftMem base hshift_z
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
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABC2

/-- Full n=2 shift=0 preloop, `base → loopBodyOff`, over `modCode_noNop_v5`.
    Shift=0 analog of the n=2 preloop: on the shift=0 branch
    (`(clzResult b1).1 = 0`) the dividend is copied verbatim (u-cells ← a-cells,
    u[4] = 0) instead of normalized.  Loop counter `x5 ← 2`, `x9 ← 4 − 2`. -/
theorem evm_mod_n2_to_loopSetup_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0) :
    cpsTripleWithin ((8 + 21 + 24 + 4) + 13) base (base + loopBodyOff)
      (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
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
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) **
       (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (2 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ (clzResult b1).1) **
       (.x7 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b1).1)) **
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
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1)) := by
  have hC2 := evm_mod_phaseAB_n2_clz_c2taken_spec_v5_noNop sp base b0 b1 b2 b3
    v2 v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3z hb2z hb1nz hshift_z
  have hC2f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ x9In) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hC2
  have hSeg := divK_copyAU_loopSetup_shift0_spec_v5_noNop_mod sp base
    a0 a1 a2 a3 u0Old u1Old u2Old u3Old u4Old (clzResult b1).2
    x9In (2 : Word) (by decide)
  have hSegf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ (clzResult b1).1) **
     (.x7 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
     (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b1).1)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))
    (by pcFree) hSeg
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [signExtend12_0] at hp ⊢; xperm_hyp hp) hC2f hSegf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [signExtend12_0] at hq ⊢; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
