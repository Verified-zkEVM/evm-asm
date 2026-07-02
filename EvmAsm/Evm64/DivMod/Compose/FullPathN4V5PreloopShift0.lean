/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5PreloopShift0

  v5 n=4 shift=0 preloop pieces over `divCode_noNop_v5`.  On the shift=0 branch
  the divisor is already top-bit-aligned (`(clzResult b3).1 = 0`, i.e. `b3 ≥ 2^63`),
  so normalization is skipped: phase-C2 takes the BEQ to copyAU and the dividend
  is copied verbatim into the u-cells.  This file builds the n=4 phaseAB-clz +
  phaseC2(taken) segment (`base → copyAUOff`) and the full n=4 shift=0 preloop
  (`base → loopBodyOff`), the n=4 analog of the n=2 `FullPathN2V5PreloopShift0`.
  Reuses the n=4 clz phase (`evm_div_phaseAB_n4_clz_spec_within_v5_noNop`, which is
  shift-agnostic) and the shared shift=0 machinery
  (`divK_phaseC2_taken_spec_within_v5_noNop`, `divK_copyAU_loopSetup_shift0_spec_v5_noNop`).
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopPreloop
import EvmAsm.Evm64.DivMod.Compose.PhaseC2V5
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5PreloopShift0

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=4 phaseAB-clz + phaseC2(shift=0 taken), `base → copyAUOff`, over
    `divCode_noNop_v5`.  Shift=0 branch (`(clzResult b3).1 = 0`): the divisor is
    already aligned, so phase-C2 takes the BEQ to copyAU.  n=4 analog of
    `evm_div_phaseAB_n2_clz_c2taken_spec_v5_noNop`. -/
theorem evm_div_phaseAB_n4_clz_c2taken_spec_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0) :
    cpsTripleWithin (8 + 21 + 24 + 4) base (base + copyAUOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ (clzResult b3).1) ** (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b3).1)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1)) := by
  have hABCLZ := evm_div_phaseAB_n4_clz_spec_within_v5_noNop sp base b0 b1 b2 b3
    v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3nz
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ v2) ** ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_taken_spec_within_v5_noNop sp (clzResult b3).1
    v2 shiftMem base hshift_z
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b3).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hABC2

/-- Full n=4 shift=0 preloop, `base → loopBodyOff`, over `divCode_noNop_v5`.
    Shift=0 analog of the n=4 preloop: on the shift=0 branch
    (`(clzResult b3).1 = 0`) the dividend is copied verbatim (u-cells ← a-cells,
    u[4] = 0) instead of normalized.  Loop counter `x5 ← 4`, `x9 ← 4 − 4`. -/
theorem evm_div_n4_to_loopSetup_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem x9In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0) :
    cpsTripleWithin ((8 + 21 + 24 + 4) + 13) base (base + loopBodyOff)
      (divCode_noNop_v5 base)
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
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) **
       (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ (clzResult b3).1) **
       (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b3).1)) **
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
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (4 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1)) := by
  have hC2 := evm_div_phaseAB_n4_clz_c2taken_spec_v5_noNop sp base b0 b1 b2 b3
    v2 v5 v6 v7 v10 q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3nz hshift_z
  have hC2f := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ x9In) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hC2
  have hSeg := divK_copyAU_loopSetup_shift0_spec_v5_noNop sp base
    a0 a1 a2 a3 u0Old u1Old u2Old u3Old u4Old (clzResult b3).2
    x9In (4 : Word) (by decide)
  have hSegf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ (clzResult b3).1) **
     (.x7 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
     (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b3).1)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hSeg
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by simp only [signExtend12_0] at hp ⊢; xperm_hyp hp) hC2f hSegf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [signExtend12_0] at hq ⊢; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
