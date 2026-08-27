/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopCallablePost

  Bridge lemmas `loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_*` (8 cases)
  plus the combined `evm_div_n2_stack_pre_to_unified_post_v4_noNop` theorem.
  Mirrors `FullPathN3V4.lean:374-640` and `N3V4StackPre.lean:496-619` for n=2.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4Families
public import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop
public import EvmAsm.Evm64.DivMod.Spec.Dispatcher

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56 word_add_zero)

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- 8 bridge lemmas: loopN2UnifiedPostV4NoX1 + frame_atoms → fullDivN2DenormPreV4
-- + fullDivN2FrameNoX1V4 + scratchMem + x1
-- ============================================================================

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FFF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 false false false sp base
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
    (fullDivN2DenormPreV4 false false false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 false false false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 false false false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2Max at hp
  delta r2MMMN2V4 r1MMMN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FFT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 false false true sp base
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
    (fullDivN2DenormPreV4 false false true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 false false true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 false false true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2MMTN2V4 r1MMTN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FTF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 false true false sp base
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
    (fullDivN2DenormPreV4 false true false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 false true false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 false true false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2Max at hp
  delta r2MTMN2V4 r1MTMN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FTT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 false true true sp base
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
    (fullDivN2DenormPreV4 false true true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 false true true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 false true true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2MTTN2V4 r1MTTN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TFF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 true false false sp base
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
    (fullDivN2DenormPreV4 true false false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 true false false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 true false false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2Max at hp
  delta r2CCCN2V4 r1TMMN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TFT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 true false true sp base
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
    (fullDivN2DenormPreV4 true false true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 true false true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 true false true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2CCCN2V4 r1TMTN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TTF
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 true true false sp base
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
    (fullDivN2DenormPreV4 true true false sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 true true false sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 true true false a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2Max at hp
  delta r2CCCN2V4 r1CCCN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_false, ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

theorem loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TTT
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0
      scratchMem raVal : Word)
    (h : PartialState)
    (hp :
      ((loopN2UnifiedPostV4NoX1 true true true sp base
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
    (fullDivN2DenormPreV4 true true true sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V4 true true true sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV4 true true true a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal)) h := by
  delta loopN2UnifiedPostV4NoX1 loopIterPostN2CallScratchNoX1 at hp
  delta r2CCCN2V4 r1CCCN2V4 at hp
  delta fullDivN2DenormPreV4 fullDivN2FrameNoX1V4 fullDivN2ScratchNoX1V4
    fullDivN2ScratchMemV4 fullDivN2Shift fullDivN2AntiShift fullDivN2NormV
    fullDivN2NormU fullDivN2R2V4 fullDivN2R1V4 fullDivN2R0V4 fullDivN2C3V4
    iterN2V4 at hp ⊢
  simp (config := { decide := true }) only [ite_true] at hp ⊢
  rw [loopExitPostN2_j0_eq] at hp
  simp (config := { decide := true }) only
    [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
     se12_32, se12_40, se12_48, se12_56] at hp ⊢
  sep_perm hp

-- ============================================================================
-- Combined stack-pre → unified-post theorem (mirrors N3V4StackPre.lean:496)
-- ============================================================================

/-- Compose the n=2 v4 stack preloop+loop path through denormalization to the
    v4 final no-`x1` post, preserving the exact caller `x1`.

    Legacy compatibility surface: this still consumes the raw normalized
    `Carry2NzAll` package. Final/public v4 n=2 stack work should use
    `evm_div_n2_stack_pre_to_unified_post_v4_noNop_selectedCarry`. -/
theorem evm_div_n2_stack_pre_to_unified_post_v4_noNop (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 =
      BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false =>
        BitVec.ult (iterN2Max
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1)
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
          (0 : Word) (0 : Word)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1)
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | true, false =>
        BitVec.ult (iterN2Max
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
                (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                  (b.getLimbN 2) (b.getLimbN 3)).2.1)
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
                (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                  (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
                (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                  (b.getLimbN 2) (b.getLimbN 3)).2.1)
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (0 : Word) (0 : Word)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1)
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
              (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
              (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).2.1)
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1
            (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.2
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
            (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
            (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1
          (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hcarry2 : Carry2NzAll
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 672) + (2 + 23 + 10))
      base (base + nopOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN2UnifiedPostNoX1V4 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hA0 := fullDivN2_preloop_loop_unified_exact_x1_scratch_v4_noNop
    bltu_2 bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz' hb3z hb2z hb1nz hshift_nz halign hbltu_2
    (by cases bltu_2 <;> simpa using hbltu_1)
    (by cases bltu_2 <;> cases bltu_1 <;> simpa using hbltu_0) hcarry2
  have hA : cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 672)
      base (base + denormOff) (divCode_noNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      ((loopN2UnifiedPostV4NoX1 bltu_2 bltu_1 bltu_0 sp base
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.2.1
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.2.2.1
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.2.2.2
        (0 : Word) (0 : Word)
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).2.1
        (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 1)).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
        ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult (b.getLimbN 1)).1))) := by
    refine cpsTripleWithin_weaken ?_ (fun _ hq => hq) hA0
    intro _ hp
    rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
    rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
        evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
        divScratchValues_unfold] at hp
    rw [word_add_zero]
    xperm_hyp hp
  have hshift_nz' : fullDivN2Shift (b.getLimbN 1) ≠ 0 := by
    delta fullDivN2Shift
    exact hshift_nz
  have hBNoNop := evm_div_n2_denorm_epilogue_bundled_spec_noNop_v4Final_exact_x1_frame
    bltu_2 bltu_1 bltu_0 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal hshift_nz'
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FFF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FFT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FTF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_FTT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TFF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TFT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TTF
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp
      · exact loopN2UnifiedPostV4NoX1_to_fullDivN2DenormPreV4_frame_TTT
          sp base (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          retMem dMem dloMem scratchUn0 scratchMem raVal h hp)
    hA hBNoNop
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => hq)
    hFull

end EvmAsm.Evm64
