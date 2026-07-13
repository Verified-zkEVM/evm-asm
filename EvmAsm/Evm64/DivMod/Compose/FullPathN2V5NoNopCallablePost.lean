/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallablePost

  Bridge lemmas `loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_*` (8 cases)
  plus the combined `evm_div_n2_stack_pre_to_unified_post_v5_noNop` theorem.
  Mirrors FullPathN2V4NoNopCallablePost (v4 bridges) for the v5 code surface.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopDispatchShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop
import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56 word_add_zero)

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- 8 bridge lemmas: loopN2UnifiedPostV5NoX1 + frame_atoms → fullDivN2DenormPreV5
-- + fullDivN2FrameNoX1V5 + scratchMem + x1
-- ============================================================================

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FFF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 false false false sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 false false false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 false false false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 false false false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2Max at hp
  delta r2MMTN2V5 r1MMTN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_false] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FFT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 false false true sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 false false true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 false false true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 false false true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2MMTN2V5 r1MMTN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FTF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 false true false sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 false true false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 false true false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 false true false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2Max at hp
  delta r2MTTN2V5 r1MTTN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_FTT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 false true true sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 false true true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 false true true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 false true true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2MTTN2V5 r1MTTN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TFF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 true false false sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 true false false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 true false false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 true false false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2Max at hp
  delta r2CCCN2V5 r1TMMN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TFT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 true false true sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 true false true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 true false true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 true false true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2CCCN2V5 r1TMMN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TTF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 true true false sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 true true false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 true true false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 true true false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2Max at hp
  delta r2CCCN2V5 r1CCCN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_TTT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV5NoX1 true true true sp base
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
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (fullDivN2DenormPreV5 true true true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 true true true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 true true true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV5NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2CCCN2V5 r1CCCN2V5 at hp
  delta fullDivN2DenormPreV5 fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
    fullDivN2ScratchMemV5 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V5 fullDivN2R1V5 fullDivN2R0V5 fullDivN2C3V5
    iterN2V5 at hp ⊢
  simp (config := { decide := true }) only [ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

end EvmAsm.Evm64
