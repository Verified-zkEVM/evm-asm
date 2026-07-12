/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Families

  N2 V5 iteration family: R0V5/R1V5/R2V5/C3V5/DenormPreV5/etc.
  Mirrors FullPathN3V4.lean (lines 141-275) for n=2.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopPreloopFullShared
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- V5 iteration intermediates
-- ============================================================================

@[irreducible]
def iterN2V5 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then
    iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[irreducible]
def fullDivN2R2V5 (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  iterN2V5 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)

@[irreducible]
def fullDivN2R1V5 (bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2V5 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2 u.2.1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

@[irreducible]
def fullDivN2R0V5 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2V5 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

@[irreducible]
def fullDivN2C3V5 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

-- ============================================================================
-- V5 denorm pre/post
-- ============================================================================

@[irreducible]
def fullDivN2DenormPreV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN2Shift b1
  let v := fullDivN2NormV b0 b1 b2 b3
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) **
   (.x10 ↦ᵣ fullDivN2C3V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
   ((sp + signExtend12 3992) ↦ₘ shift) **
   ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
   ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
   ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
   ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
   ((sp + signExtend12 4088) ↦ₘ r0.1) **
   ((sp + signExtend12 4080) ↦ₘ r1.1) **
   ((sp + signExtend12 4072) ↦ₘ r2.1) **
   ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v.1) **
   ((sp + signExtend12 40) ↦ₘ v.2.1) **
   ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
   ((sp + signExtend12 56) ↦ₘ v.2.2.2))

@[irreducible]
def fullDivN2DenormPostV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN2Shift b1
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
    r0.1 r1.1 r2.1 (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift)

-- ============================================================================
-- V5 scratch, frame, unified post
-- ============================================================================

@[irreducible]
def fullDivN2ScratchMemV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let scratch2 := if bltu_2 then
      divKTrialCallV5ScratchOut u.2.2.2.2 u.2.2.2.1 v.2.1 scratchMem
    else scratchMem
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let scratch1 := if bltu_1 then
      divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v.2.1 scratch2
    else scratch2
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v.2.1 scratch1
  else scratch1

@[irreducible]
def fullDivN2ScratchNoX1V5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word) :
    Assertion :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let scratchRet2 := if bltu_2 then (base + div128CallRetOff) else retMem
  let scratchD2 := if bltu_2 then v.2.1 else dMem
  let scratchDLo2 := if bltu_2 then divKTrialCallV5DLo v.2.1 else dloMem
  let scratchUn02 := if bltu_2 then divKTrialCallV5Un0 u.2.2.2.1 else scratchUn0
  let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else scratchRet2
  let scratchD1 := if bltu_1 then v.2.1 else scratchD2
  let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo v.2.1 else scratchDLo2
  let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 r2.2.1 else scratchUn02
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then v.2.1 else scratchD1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo v.2.1 else scratchDLo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.1 else scratchUn01))

@[irreducible]
def fullDivN2FrameNoX1V5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word) :
    Assertion :=
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  fullDivN2ScratchNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0

@[irreducible]
def fullDivN2UnifiedPostNoX1V5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word) :
    Assertion :=
  fullDivN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 **
  ((sp + signExtend12 3936) ↦ₘ
    fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)

-- ============================================================================
-- _unfold lemmas for the @[irreducible] V5 assertion bundles
-- ============================================================================

theorem fullDivN2DenormPostV5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    fullDivN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    (let shift := fullDivN2Shift b1
     let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
     let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
     let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
     denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
       r0.1 r1.1 r2.1 (0 : Word) **
     ((sp + signExtend12 3992) ↦ₘ shift)) := by
  delta fullDivN2DenormPostV5; rfl

theorem fullDivN2ScratchNoX1V5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word} :
    fullDivN2ScratchNoX1V5 bltu_2 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 =
    (let v := fullDivN2NormV b0 b1 b2 b3
     let u := fullDivN2NormU a0 a1 a2 a3 b1
     let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
     let scratchRet2 := if bltu_2 then (base + div128CallRetOff) else retMem
     let scratchD2 := if bltu_2 then v.2.1 else dMem
     let scratchDLo2 := if bltu_2 then divKTrialCallV5DLo v.2.1 else dloMem
     let scratchUn02 := if bltu_2 then divKTrialCallV5Un0 u.2.2.2.1 else scratchUn0
     let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else scratchRet2
     let scratchD1 := if bltu_1 then v.2.1 else scratchD2
     let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo v.2.1 else scratchDLo2
     let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 r2.2.1 else scratchUn02
     let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
     (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
     (sp + signExtend12 3960 ↦ₘ (if bltu_0 then v.2.1 else scratchD1)) **
     (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo v.2.1 else scratchDLo1)) **
     (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.1 else scratchUn01))) := by
  delta fullDivN2ScratchNoX1V5; rfl

theorem fullDivN2FrameNoX1V5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word} :
    fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 =
    (let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
     let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
     let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     fullDivN2ScratchNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0) := by
  delta fullDivN2FrameNoX1V5; rfl

theorem fullDivN2UnifiedPostNoX1V5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word} :
    fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem =
    (fullDivN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) := by
  delta fullDivN2UnifiedPostNoX1V5; rfl

-- (`fullDivN2QuotientWordV5` lives in `Spec/N2V5QuotientWord.lean`, which imports
-- this file for the `fullDivN2R{0,1,2}V5` digit results.)

-- ============================================================================
-- V5 denorm epilogue
-- ============================================================================

theorem evm_div_n2_denorm_epilogue_bundled_spec_noNop_v5Final
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : fullDivN2Shift b1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff) (divCode_noNop_v5 base)
      (fullDivN2DenormPreV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3)
      (fullDivN2DenormPostV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := fullDivN2Shift b1
  let v := fullDivN2NormV b0 b1 b2 b3
  let r2 := fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let c3 := fullDivN2C3V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  have h := evm_div_preamble_denorm_epilogue_spec_v5_noNop sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 shift
    r0.2.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 r0.1 r1.1 r2.1 (0 : Word)
    v.1 v.2.1 v.2.2.1 v.2.2.2 hshift_nz
  exact cpsTripleWithin_weaken
    (fun h hp => by
      subst shift; subst v; subst r2; subst r1; subst r0; subst c3
      delta fullDivN2DenormPreV5 at hp
      simp only [se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by
      subst shift; subst r2; subst r1; subst r0
      delta fullDivN2DenormPostV5
      xperm_hyp hq)
    h

theorem evm_div_n2_denorm_epilogue_bundled_spec_noNop_v5Final_exact_x1_frame
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hshift_nz : fullDivN2Shift b1 ≠ 0) :
    cpsTripleWithin (2 + 23 + 10) (base + denormOff) (base + nopOff)
      (divCode_noNop_v5 base)
      (fullDivN2DenormPreV5 bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
         retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ
         fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
       (.x1 ↦ᵣ raVal))
      (fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal)) := by
  have hDenorm := evm_div_n2_denorm_epilogue_bundled_spec_noNop_v5Final
    bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFramed := cpsTripleWithin_frameR
    (fullDivN2FrameNoX1V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
       retMem dMem dloMem scratchUn0 **
     ((sp + signExtend12 3936) ↦ₘ
       fullDivN2ScratchMemV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) **
     (.x1 ↦ᵣ raVal))
    (by
      delta fullDivN2FrameNoX1V5 fullDivN2ScratchNoX1V5
      pcFree) hDenorm
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta fullDivN2UnifiedPostNoX1V5
      xperm_hyp hq)
    hFramed

end EvmAsm.Evm64
