/- Shared declaration home for the n=2 V5 families, shape bounds, and max-carry facts. -/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopPreloopFullShared
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base
import EvmAsm.Evm64.EvmWordArith.DivN4RemainderLt
import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindow
import EvmAsm.Evm64.EvmWordArith.DivN2MaxOverestimate
import EvmAsm.Evm64.DivMod.Spec.N2V5TrialOverestimate
import EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryBorrowN2
import EvmAsm.Evm64.DivMod.Spec.N2V5ThreeStep
import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge
import EvmAsm.Evm64.EvmWordArith.DivN2NormVStructure
import EvmAsm.Evm64.DivMod.Spec.N2V5C3LeOne

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


open EvmWord EvmAsm.Rv64

/-- **v5 n=2 per-digit remainder bound (call path).** For a normalized 2-limb
    divisor (`v1 ≥ 2^63`) in the call regime (`u2 < v1`), the `iterN2V5 true`
    iteration leaves a remainder `< val256 v`.  Assembled from the abstract
    `iterWithDoubleAddback_remainder_lt_of_plus_two` with the trial bracket
    (#7347 lower, #7349 upper) and the `v3 = 0` borrow-carry fact. -/
theorem iterN2V5_true_remainder_lt
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    EvmWord.val256
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 <
    EvmWord.val256 v0 v1 0 0 := by
  have hrw : iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5; rw [if_pos rfl]
  rw [hrw]
  have hv_pos : 0 < val256 v0 v1 0 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    simp only [EvmWord.val256, h0]; omega
  have hq_over := n2_window_div_le_val256_div_plus_two_v5 v0 v1 u0 u1 u2 hv1 hcall
  have hge := n2_window_val256_div_le_trial_v5 v0 v1 u0 u1 u2 hv1 hcall
  have hq_ge : val256 u0 u1 u2 0 + (0 : Word).toNat * 2^256 <
      ((divKTrialCallV5QHat u2 u1 v1).toNat + 1) * val256 v0 v1 0 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h0, Nat.zero_mul, Nat.add_zero]
    exact (Nat.div_lt_iff_lt_mul hv_pos).mp (by omega)
  have hc3 : BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro h0
    rw [h0] at hb
    exact absurd hb (by decide)
  exact iterWithDoubleAddback_remainder_lt_of_plus_two
    (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0 0 hbnz hc3 hq_over hq_ge

/-- The n=2 divisor value is a 2-limb number, hence `< 2^128`. -/
theorem n2_val256_v_lt_pow128 (v0 v1 : Word) : val256 v0 v1 0 0 < 2^128 := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have := v0.isLt; have := v1.isLt
  simp only [EvmWord.val256, h0]; omega

/-- **v5 n=2 per-digit remainder collapse.** Since the remainder is `< val256 v
    < 2^128`, its two high limbs and the overflow cell are zero — so its `val256`
    occupies only the low two limbs.  Lets the per-digit conservation reduce to
    the 2-limb step form consumed by `fullDivN2V5_three_step_nat`. -/
theorem iterN2V5_true_remainder_collapse
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1 = 0 ∧
    (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 = 0 ∧
    (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2 = 0 := by
  have hlt := iterN2V5_true_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hcall
  have hv128 := n2_val256_v_lt_pow128 v0 v1
  set out := iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 with hout
  have key : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 < 2^128 := by omega
  have hr2 := out.2.2.2.1.isLt
  have hr3 := out.2.2.2.2.1.isLt
  refine ⟨?_, ?_, ?_⟩
  · have : out.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.2.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)

/-- **v5 n=2 per-digit conservation from shape (no `Carry2Nz`).** The call-path
    iteration preserves value: `val256 window = q·val256 v + val256(remainder) +
    overflow·2^256`, with `q` the output quotient digit.  Discharged purely from
    the trial bracket via `iterWithDoubleAddback_val256_conservation_of_branch_bounds`
    — needs NO `isAddbackCarry2Nz` hypothesis (the q-magnitude side conditions
    come from `q_pos_of_mulsub_borrow` / `q_ge_two_of_mulsub_borrow_and_addback_carry_zero`).
    This is the cleaner replacement for the `…_of_carry2`-based conservations. -/
theorem iterN2V5_true_conservation_from_shape
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    val256 u0 u1 u2 0 =
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        val256
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 := by
  have hrw : iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5; rw [if_pos rfl]
  rw [hrw]
  set q := divKTrialCallV5QHat u2 u1 v1 with hq
  have hq_over := n2_window_div_le_val256_div_plus_two_v5 v0 v1 u0 u1 u2 hv1 hcall
  have hc3 : BitVec.ult (0 : Word) (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro h0; rw [h0] at hb; exact absurd hb (by decide)
  have hconv := iterWithDoubleAddback_val256_conservation_of_branch_bounds
    q v0 v1 0 0 u0 u1 u2 0 0 hbnz hq_over hc3
    (fun hb _ => q_pos_of_mulsub_borrow q v0 v1 0 0 u0 u1 u2 0 (hc3 hb))
    (fun hb hcz => q_ge_two_of_mulsub_borrow_and_addback_carry_zero
      q v0 v1 0 0 u0 u1 u2 0 (hc3 hb) hcz)
  have h0 : (0 : Word).toNat = 0 := rfl
  simpa [h0] using hconv

/-- **Combined clean 2-limb Euclidean step for the v5 n=2 call path.** From
    shape, `val256 window = q·val256 v + R` with `R = rem0 + 2^64·rem1 <
    val256 v` the collapsed 2-limb remainder.  Merges
    `iterN2V5_true_conservation_from_shape` with `iterN2V5_true_remainder_collapse`
    + `iterN2V5_true_remainder_lt` — exactly the per-digit step form fed to
    `fullDivN2V5_three_step_nat` (#7344) to assemble `fullDivN2MulSubEqV5`. -/
theorem iterN2V5_true_step
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    val256 u0 u1 u2 0 =
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        ((iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat) ∧
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat <
        val256 v0 v1 0 0 := by
  obtain ⟨hc2, hc3, hco⟩ := iterN2V5_true_remainder_collapse v0 v1 u0 u1 u2 hbnz hv1 hcall
  have hconv := iterN2V5_true_conservation_from_shape v0 v1 u0 u1 u2 hbnz hv1 hcall
  have hlt := iterN2V5_true_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hcall
  set out := iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 with hout
  have h0 : (0 : Word).toNat = 0 := rfl
  have hcollapse : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 =
      out.2.1.toNat + 2^64 * out.2.2.1.toNat := by
    rw [hc2, hc3]; simp only [EvmWord.val256, h0]; ring
  constructor
  · rw [hconv, hcollapse, hco, h0]; ring
  · rw [hcollapse] at hlt; rw [hco, h0] at hlt; simpa using hlt

/-! ### Max branch (`bltu = false`)

The max path (`u2 ≥ v1`, trial `= 2^64-1`) mirrors the call path, with the
overestimate from `max_trial_local_overestimate_n2_of_not_ult` and the
no-underestimate `hq_ge` from the window-validity invariant
`val256 window < 2^64·val256 v` (since the max trial `+1 = 2^64`). -/

/-- **v5 n=2 per-digit remainder bound (max path).** -/
theorem iterN2V5_false_remainder_lt
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0) :
    EvmWord.val256 (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 <
    EvmWord.val256 v0 v1 0 0 := by
  have hrw : iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (signExtend12 4095) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5 iterN2Max; simp only [Bool.false_eq_true, if_false]
  rw [hrw]
  set q : Word := signExtend12 4095 with hq
  have hq_over := max_trial_local_overestimate_n2_of_not_ult v0 v1 u0 u1 u2 hv1 hbltu
  have hqsucc : q.toNat + 1 = 2^64 := by rw [hq, signExtend12_4095_toNat]; omega
  have hq_ge : val256 u0 u1 u2 0 + (0 : Word).toNat * 2^256 < (q.toNat + 1) * val256 v0 v1 0 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h0, hqsucc, Nat.zero_mul, Nat.add_zero]; exact hvalid
  have hc3 : BitVec.ult (0 : Word) (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb; apply mulsubN4_c3_eq_one_v3_zero; intro hz; rw [hz] at hb; exact absurd hb (by decide)
  exact iterWithDoubleAddback_remainder_lt_of_plus_two q v0 v1 0 0 u0 u1 u2 0 0 hbnz hc3 hq_over hq_ge

/-- **v5 n=2 per-digit conservation (max path).** -/
theorem iterN2V5_false_conservation
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1) :
    val256 u0 u1 u2 0 =
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        val256 (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1
          (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1
          (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
          (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 := by
  have hrw : iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (signExtend12 4095) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5 iterN2Max; simp only [Bool.false_eq_true, if_false]
  rw [hrw]
  set q : Word := signExtend12 4095 with hq
  have hq_over := max_trial_local_overestimate_n2_of_not_ult v0 v1 u0 u1 u2 hv1 hbltu
  have hq1 : 1 ≤ q.toNat := by rw [hq, signExtend12_4095_toNat]; omega
  have hq2 : 2 ≤ q.toNat := by rw [hq, signExtend12_4095_toNat]; omega
  have hc3 : BitVec.ult (0 : Word) (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb; apply mulsubN4_c3_eq_one_v3_zero; intro hz; rw [hz] at hb; exact absurd hb (by decide)
  have hconv := iterWithDoubleAddback_val256_conservation_of_branch_bounds
    q v0 v1 0 0 u0 u1 u2 0 0 hbnz hq_over hc3 (fun _ _ => hq1) (fun _ _ => hq2)
  have h0 : (0 : Word).toNat = 0 := rfl
  simpa [h0] using hconv

/-- **v5 n=2 per-digit remainder collapse (max path).** -/
theorem iterN2V5_false_remainder_collapse
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0) :
    (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1 = 0 ∧
    (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 = 0 ∧
    (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2 = 0 := by
  have hlt := iterN2V5_false_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hbltu hvalid
  have hv128 := n2_val256_v_lt_pow128 v0 v1
  set out := iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 with hout
  have key : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 < 2^128 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have : out.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.2.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)

/-- **Combined clean 2-limb Euclidean step for the v5 n=2 max path.** -/
theorem iterN2V5_false_step
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0) :
    val256 u0 u1 u2 0 =
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        ((iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat) ∧
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat <
        val256 v0 v1 0 0 := by
  obtain ⟨hc2, hc3, hco⟩ := iterN2V5_false_remainder_collapse v0 v1 u0 u1 u2 hbnz hv1 hbltu hvalid
  have hconv := iterN2V5_false_conservation v0 v1 u0 u1 u2 hbnz hv1 hbltu
  have hlt := iterN2V5_false_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hbltu hvalid
  set out := iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 with hout
  have h0 : (0 : Word).toNat = 0 := rfl
  have hcollapse : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 =
      out.2.1.toNat + 2^64 * out.2.2.1.toNat := by
    rw [hc2, hc3]; simp only [EvmWord.val256, h0]; ring
  constructor
  · rw [hconv, hcollapse, hco, h0]; ring
  · rw [hcollapse] at hlt; rw [hco, h0] at hlt; simpa using hlt

/-- **Unified per-digit step (both branches).** For any `bltu` correctly
    reflecting the comparison `u2 < v1`, with the window-validity invariant
    `val256 window < 2^64·val256 v`, the digit produces the clean 2-limb
    Euclidean step `val256 window = q·val256 v + R` with `R < val256 v`.
    Dispatches to `iterN2V5_true_step` (call) or `iterN2V5_false_step` (max).
    One lemma per digit for the cross-digit `fullDivN2MulSubEqV5` assembly. -/
theorem iterN2V5_step (bltu : Bool) (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0)
    (hcall : bltu = true → BitVec.ult u2 v1 = true)
    (hmax : bltu = false → ¬ BitVec.ult u2 v1) :
    val256 u0 u1 u2 0 =
      (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        ((iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat) ∧
      (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat <
        val256 v0 v1 0 0 := by
  cases bltu with
  | true =>
    have hu : u2.toNat < v1.toNat := by
      have := hcall rfl; rw [BitVec.ult] at this; exact of_decide_eq_true this
    exact iterN2V5_true_step v0 v1 u0 u1 u2 hbnz hv1 hu
  | false =>
    exact iterN2V5_false_step v0 v1 u0 u1 u2 hbnz hv1 (hmax rfl) hvalid

/-- **n=2 normalized dividend value (with overflow) = original scaled.** The
    CLZ-of-`b1` normalization of the dividend satisfies
    `val256 normU + overflow·2^256 = val256 a · 2^shift`.  n=2 analog of
    `fullDivN1NormU_val256_eq_scaled`. -/
theorem fullDivN2NormU_val256_eq_scaled
    (a0 a1 a2 a3 b1 : Word) (hshift_nz : (clzResult b1).1 ≠ 0) :
    EvmWord.val256
      (fullDivN2NormU a0 a1 a2 a3 b1).1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 +
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat * 2^256 =
    EvmWord.val256 a0 a1 a2 a3 * 2^(fullDivN2Shift b1).toNat := by
  unfold fullDivN2NormU fullDivN2AntiShift
  dsimp only
  unfold fullDivN2Shift
  have h_shift_pos : 1 ≤ (clzResult b1).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b1).1.toNat with h | h
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b1).1.toNat % 64 = (clzResult b1).1.toNat :=
    Nat.mod_eq_of_lt (by have := clzResult_fst_toNat_le b1; omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos (clzResult_fst_toNat_le b1)]
  exact EvmWord.val256_normalize_general h_shift_pos (by omega) a0 a1 a2 a3

/-- **n=2 normalized divisor value = original scaled (from 2-limb shape).** For a
    2-limb divisor (`b2 = b3 = 0`), the CLZ-of-`b1` normalization satisfies
    `val256 normV = val256 b · 2^shift`.  n=2 analog of
    `fullDivN1NormV_val256_eq_scaled_of_shape`. -/
theorem fullDivN2NormV_val256_eq_scaled_of_shape
    (b0 b1 b2 b3 : Word) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b1).1 ≠ 0) :
    EvmWord.val256
      (fullDivN2NormV b0 b1 b2 b3).1
      (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.2 =
    EvmWord.val256 b0 b1 b2 b3 * 2^(fullDivN2Shift b1).toNat := by
  subst b2; subst b3
  unfold fullDivN2NormV fullDivN2AntiShift
  dsimp only
  unfold fullDivN2Shift
  have h_shift_pos : 1 ≤ (clzResult b1).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b1).1.toNat with h | h
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b1).1.toNat % 64 = (clzResult b1).1.toNat :=
    Nat.mod_eq_of_lt (by have := clzResult_fst_toNat_le b1; omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos (clzResult_fst_toNat_le b1)]
  exact EvmWord.val256_normalize h_shift_pos (by omega) b0 b1 0 0 (by simp)

/-- **First-digit (R2) step over the normalized window.** Rewrites
    `fullDivN2R2V5` to expose `iterN2V5` over the 2-limb `normV` (using the
    shift≠0 shape lemmas) and applies the unified per-digit step
    `iterN2V5_step`.  Gives the clean 2-limb Euclidean step
    `val256(nu2,nu3,nu4,0) = q2·val256 normV + R2r` with `R2r < val256 normV`,
    from window-validity + the `bltu_2` path match.  First link of the
    cross-digit telescope for `fullDivN2QuotientWordV5_eq_div_of_shape`. -/
theorem fullDivN2R2V5_step_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hvalid : val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0
        < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0)
    (hcall : bltu_2 = true →
      BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hmax : bltu_2 = false →
      ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 =
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 +
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2^64 * (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) ∧
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2^64 * (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat <
        val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 := by
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  have hmsb := fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz
  have hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : (fullDivN2NormV b0 b1 b2 b3).2.1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hmsb; simp at hmsb
  have hrw : fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN2V5 bltu_2 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0 := by
    unfold fullDivN2R2V5; dsimp only; rw [hv2, hv3]
  rw [hrw]
  exact iterN2V5_step bltu_2 _ _ _ _ _ hbnz hmsb hvalid hcall hmax


/-- Next-window validity: if the previous 2-limb remainder is `< V`, the next
    digit's window `val256(nu, r0, r1, 0)` is `< 2^64·V`.  Propagates the
    window-validity invariant across digits. -/
theorem n2_next_window_lt (nu r0 r1 : Word) (V : Nat)
    (h : r0.toNat + 2^64 * r1.toNat < V) :
    val256 nu r0 r1 0 < 2^64 * V := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have hnu := nu.isLt
  have hexp : val256 nu r0 r1 0 = nu.toNat + 2^64 * (r0.toNat + 2^64 * r1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  rw [hexp]
  calc nu.toNat + 2^64 * (r0.toNat + 2^64 * r1.toNat)
      < 2^64 + 2^64 * (r0.toNat + 2^64 * r1.toNat) := by omega
    _ = 2^64 * ((r0.toNat + 2^64 * r1.toNat) + 1) := by ring
    _ ≤ 2^64 * V := Nat.mul_le_mul_left _ h

/-- **fullDivN2R1V5 step over the normalized window** (chained on the previous
    remainder). -/
theorem fullDivN2R1V5_step_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hpc2 : (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0) (hpc3 : (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hvalid : val256 ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0
        < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0)
    (hcall : bltu_1 = true → BitVec.ult ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hmax : bltu_1 = false → ¬ BitVec.ult ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1) :
    val256 ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0 =
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 +
        ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64 * (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) ∧
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64 * (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat <
        val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 := by
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  have hmsb := fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz
  have hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : (fullDivN2NormV b0 b1 b2 b3).2.1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hmsb; simp at hmsb
  have hrw : (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) =
      iterN2V5 bltu_1 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0 0 := by
    unfold fullDivN2R1V5; dsimp only; rw [hv2, hv3, hpc2, hpc3]
  rw [hrw]
  exact iterN2V5_step bltu_1 _ _ _ _ _ hbnz hmsb hvalid hcall hmax

/-- **fullDivN2R0V5 step over the normalized window** (chained on the previous
    remainder). -/
theorem fullDivN2R0V5_step_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hpc2 : (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0) (hpc3 : (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hvalid : val256 ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0
        < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0)
    (hcall : bltu_0 = true → BitVec.ult ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hmax : bltu_0 = false → ¬ BitVec.ult ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1) :
    val256 ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0 =
      (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 +
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64 * (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) ∧
      (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64 * (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat <
        val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 := by
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  have hmsb := fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz
  have hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : (fullDivN2NormV b0 b1 b2 b3).2.1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hmsb; simp at hmsb
  have hrw : (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) =
      iterN2V5 bltu_0 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0 0 := by
    unfold fullDivN2R0V5; dsimp only; rw [hv2, hv3, hpc2, hpc3]
  rw [hrw]
  exact iterN2V5_step bltu_0 _ _ _ _ _ hbnz hmsb hvalid hcall hmax



/-- Unified per-digit remainder collapse (both branches). -/
theorem iterN2V5_collapse (bltu : Bool) (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0)
    (hcall : bltu = true → BitVec.ult u2 v1 = true)
    (hmax : bltu = false → ¬ BitVec.ult u2 v1) :
    (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1 = 0 ∧
    (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 = 0 ∧
    (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2 = 0 := by
  cases bltu with
  | true =>
    have hu : u2.toNat < v1.toNat := by
      have := hcall rfl; rw [BitVec.ult] at this; exact of_decide_eq_true this
    exact iterN2V5_true_remainder_collapse v0 v1 u0 u1 u2 hbnz hv1 hu
  | false =>
    exact iterN2V5_false_remainder_collapse v0 v1 u0 u1 u2 hbnz hv1 (hmax rfl) hvalid

/-- fullDivN2R2V5_collapse_of_shape (collapse over the normalized window). -/
theorem fullDivN2R2V5_collapse_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hvalid : val256 ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.1) ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1) ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2) 0
        < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0)
    (hcall : bltu_2 = true → BitVec.ult ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2) (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hmax : bltu_2 = false → ¬ BitVec.ult ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2) (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0 ∧ (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  have hmsb := fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz
  have hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : (fullDivN2NormV b0 b1 b2 b3).2.1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hmsb; simp at hmsb
  have hrw : (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3) =
      iterN2V5 bltu_2 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.1) ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1) ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2) 0 0 := by
    unfold fullDivN2R2V5; dsimp only; rw [hv2, hv3]
  rw [hrw]
  exact iterN2V5_collapse bltu_2 _ _ _ _ _ hbnz hmsb hvalid hcall hmax |>.imp id (·.1)

/-- fullDivN2R1V5_collapse_of_shape (collapse over the normalized window). -/
theorem fullDivN2R1V5_collapse_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hpc2 : (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0) (hpc3 : (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hvalid : val256 ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0
        < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0)
    (hcall : bltu_1 = true → BitVec.ult ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hmax : bltu_1 = false → ¬ BitVec.ult ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0 ∧ (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  have hmsb := fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz
  have hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : (fullDivN2NormV b0 b1 b2 b3).2.1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hmsb; simp at hmsb
  have hrw : (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) =
      iterN2V5 bltu_1 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0 0 := by
    unfold fullDivN2R1V5; dsimp only; rw [hv2, hv3, hpc2, hpc3]
  rw [hrw]
  exact iterN2V5_collapse bltu_1 _ _ _ _ _ hbnz hmsb hvalid hcall hmax |>.imp id (·.1)

/-- fullDivN2R0V5_collapse_of_shape (collapse over the normalized window). -/
theorem fullDivN2R0V5_collapse_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hpc2 : (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0) (hpc3 : (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hvalid : val256 ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0
        < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0)
    (hcall : bltu_0 = true → BitVec.ult ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hmax : bltu_0 = false → ¬ BitVec.ult ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0 ∧ (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  have hmsb := fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz
  have hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : (fullDivN2NormV b0 b1 b2 b3).2.1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hmsb; simp at hmsb
  have hrw : (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) =
      iterN2V5 bltu_0 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) 0 0 := by
    unfold fullDivN2R0V5; dsimp only; rw [hv2, hv3, hpc2, hpc3]
  rw [hrw]
  exact iterN2V5_collapse bltu_0 _ _ _ _ _ hbnz hmsb hvalid hcall hmax |>.imp id (·.1)

/-- The n=2 divisor value is at least `2^64` (its top limb `b1` is nonzero). -/
theorem n2_val256_b_ge_pow64 (b0 b1 : Word) (hb1 : b1 ≠ 0) : 2^64 ≤ val256 b0 b1 0 0 := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hb1n : b1.toNat ≠ 0 := by intro h; exact hb1 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  simp only [EvmWord.val256, h0]; omega

/-- Pure-`Nat` core of the first-window validity: from the scaled-dividend
    identity and the divisor bound, the top 3-limb window is `< 2^64·(B·S)`. -/
theorem first_window_core (n0 n1 n2 n3 n4 A B S : Nat)
    (hU : n0 + 2^64*n1 + 2^128*n2 + 2^192*n3 + 2^256*n4 = A*S)
    (hA : A < 2^256) (hB : 2^64 ≤ B) (hSpos : 0 < S) :
    n2 + 2^64*n3 + 2^128*n4 < 2^64*(B*S) := by
  have hW2le : 2^128*(n2+2^64*n3+2^128*n4) ≤ A*S := by nlinarith [hU]
  have hAB : A*S < 2^192*(B*S) := by nlinarith [hA, hB, hSpos]
  have hchain : 2^128*(n2+2^64*n3+2^128*n4) < 2^128*(2^64*(B*S)) := by nlinarith [hW2le, hAB]
  exact Nat.lt_of_mul_lt_mul_left hchain

/-- **First-window validity (digit R2).** The top 3-limb normalized window is
    `< 2^64·val256 normV` — the `hvalid` hypothesis of the R2 step.  Follows from
    the scaling bridge (`val256 normU + nu4·2^256 = val256 a·2^s`), the dividend
    bound `val256 a < 2^256`, and the divisor bound `val256 b ≥ 2^64`. -/
theorem fullDivN2_first_window_valid (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0) :
    val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0
      < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hscaleU := fullDivN2NormU_val256_eq_scaled a0 a1 a2 a3 b1 hshift_nz
  have hscaleV := fullDivN2NormV_val256_eq_scaled_of_shape b0 b1 b2 b3 hb2z hb3z hshift_nz
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  rw [hv2, hv3] at hscaleV
  have hA := val256_bound a0 a1 a2 a3
  have hB : 2^64 ≤ val256 b0 b1 b2 b3 := by
    subst b2; subst b3; exact n2_val256_b_ge_pow64 b0 b1 hb1nz
  have hSpos : 0 < 2^(fullDivN2Shift b1).toNat := by positivity
  have hU : (fullDivN2NormU a0 a1 a2 a3 b1).1.toNat
      + 2^64*(fullDivN2NormU a0 a1 a2 a3 b1).2.1.toNat
      + 2^128*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.1.toNat
      + 2^192*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1.toNat
      + 2^256*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat
      = val256 a0 a1 a2 a3 * 2^(fullDivN2Shift b1).toNat := by
    rw [← hscaleU]; simp only [EvmWord.val256]; ring
  have hWexp : val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0
      = (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1.toNat
        + 2^64*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1.toNat
        + 2^128*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat := by
    simp only [EvmWord.val256, h0]; ring
  rw [hWexp, hscaleV]
  exact first_window_core _ _ _ _ _ _ _ _ hU hA hB hSpos

/-- **v5 n=2 accumulated quotient correctness (shift≠0).** The three v5 n=2
    quotient digits combine to exactly `val256 a / val256 b`.  Telescopes the
    three per-digit steps (R2/R1/R0) — chained via the window-validity invariant
    and collapse facts — through `fullDivN2V5_three_step_nat` into the normalized
    Euclidean equation, then `div_quotient_of_normalized` + the scaling bridges
    recover the original quotient.  The `bltu` arguments must match the per-digit
    `u2 < v1` comparisons (supplied here as hypotheses; discharged from the path
    conditions `isTrialN2V5_j*` at the loop level).  This is the corrected
    shift-aware route replacing the mis-stated `fullDivN2MulSubEqV5`. -/
theorem fullDivN2_acc_quot_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2^128
      + (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2^64
      + (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
      = val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hfwv := fullDivN2_first_window_valid a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z hshift_nz hb1nz
  have hR2 := fullDivN2R2V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR2c := fullDivN2R2V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR1valid := n2_next_window_lt (fullDivN2NormU a0 a1 a2 a3 b1).2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 _ hR2.2
  have hR1 := fullDivN2R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 hb2z hb3z hshift_nz hb1nz hR2c.1 hR2c.2 hR1valid hc1 hm1
  have hR1c := fullDivN2R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 hb2z hb3z hshift_nz hb1nz hR2c.1 hR2c.2 hR1valid hc1 hm1
  have hR0valid := n2_next_window_lt (fullDivN2NormU a0 a1 a2 a3 b1).1
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 _ hR1.2
  have hR0 := fullDivN2R0V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz hR1c.1 hR1c.2 hR0valid hc0 hm0
  have hscaleU := fullDivN2NormU_val256_eq_scaled a0 a1 a2 a3 b1 hshift_nz
  have hscaleV := fullDivN2NormV_val256_eq_scaled_of_shape b0 b1 b2 b3 hb2z hb3z hshift_nz
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  rw [hv2, hv3] at hscaleV
  have hw2 : val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0
      = (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1.toNat + 2^64*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1.toNat + 2^128*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat := by
    simp only [EvmWord.val256, h0]; ring
  have hw1 : val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 0
      = (fullDivN2NormU a0 a1 a2 a3 b1).2.1.toNat + 2^64*((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64*(fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  have hw0 : val256 (fullDivN2NormU a0 a1 a2 a3 b1).1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 0
      = (fullDivN2NormU a0 a1 a2 a3 b1).1.toNat + 2^64*((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64*(fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  rw [hw2] at hR2; rw [hw1] at hR1; rw [hw0] at hR0
  have hfirst : val256 a0 a1 a2 a3 * 2^(fullDivN2Shift b1).toNat =
      (fullDivN2NormU a0 a1 a2 a3 b1).1.toNat + 2^64 * (fullDivN2NormU a0 a1 a2 a3 b1).2.1.toNat
        + 2^128 * ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.1.toNat + 2^64*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1.toNat + 2^128*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat) := by
    rw [← hscaleU]; simp only [EvmWord.val256]; ring
  have htele := fullDivN2V5_three_step_nat hfirst hR2.1 hR1.1 hR0.1
  rw [hscaleV] at htele
  have hlt : (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64*(fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat < val256 b0 b1 b2 b3 * 2^(fullDivN2Shift b1).toNat := by
    rw [← hscaleV]; exact hR0.2
  have hfin := div_quotient_of_normalized htele hlt
  linarith [hfin]

/-- **v5 n=2 normalized Euclidean equation (shift≠0).** The shared core consumed
    by BOTH the DIV quotient correctness and the MOD remainder correctness (and
    the loop): `val256 a · 2^s = Q · (val256 b · 2^s) + R0r` with `R0r < val256 b
    · 2^s`, where `Q` is the accumulated quotient and `R0r` the final collapsed
    2-limb remainder.  Same per-digit telescope as `fullDivN2_acc_quot_eq_div_of_shape`,
    stopping at the Euclidean equation (before `div_quotient_of_normalized`). -/
theorem fullDivN2_normalized_euclidean_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (val256 a0 a1 a2 a3 * 2^(fullDivN2Shift b1).toNat =
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2^128
          + (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2^64
          + (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
          * (val256 b0 b1 b2 b3 * 2^(fullDivN2Shift b1).toNat)
          + ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
            + 2^64*(fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat)) ∧
    ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
        + 2^64*(fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
      < val256 b0 b1 b2 b3 * 2^(fullDivN2Shift b1).toNat) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hfwv := fullDivN2_first_window_valid a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z hshift_nz hb1nz
  have hR2 := fullDivN2R2V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR2c := fullDivN2R2V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR1valid := n2_next_window_lt (fullDivN2NormU a0 a1 a2 a3 b1).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 _ hR2.2
  have hR1 := fullDivN2R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 hb2z hb3z hshift_nz hb1nz hR2c.1 hR2c.2 hR1valid hc1 hm1
  have hR1c := fullDivN2R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 hb2z hb3z hshift_nz hb1nz hR2c.1 hR2c.2 hR1valid hc1 hm1
  have hR0valid := n2_next_window_lt (fullDivN2NormU a0 a1 a2 a3 b1).1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 _ hR1.2
  have hR0 := fullDivN2R0V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz hR1c.1 hR1c.2 hR0valid hc0 hm0
  have hscaleU := fullDivN2NormU_val256_eq_scaled a0 a1 a2 a3 b1 hshift_nz
  have hscaleV := fullDivN2NormV_val256_eq_scaled_of_shape b0 b1 b2 b3 hb2z hb3z hshift_nz
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  rw [hv2, hv3] at hscaleV
  have hw2 : val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0
      = (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1.toNat + 2^64*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1.toNat + 2^128*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat := by
    simp only [EvmWord.val256, h0]; ring
  have hw1 : val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 0
      = (fullDivN2NormU a0 a1 a2 a3 b1).2.1.toNat + 2^64*((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64*(fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  have hw0 : val256 (fullDivN2NormU a0 a1 a2 a3 b1).1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 0
      = (fullDivN2NormU a0 a1 a2 a3 b1).1.toNat + 2^64*((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat + 2^64*(fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  rw [hw2] at hR2; rw [hw1] at hR1; rw [hw0] at hR0
  have hfirst : val256 a0 a1 a2 a3 * 2^(fullDivN2Shift b1).toNat =
      (fullDivN2NormU a0 a1 a2 a3 b1).1.toNat + 2^64 * (fullDivN2NormU a0 a1 a2 a3 b1).2.1.toNat
        + 2^128 * ((fullDivN2NormU a0 a1 a2 a3 b1).2.2.1.toNat + 2^64*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1.toNat + 2^128*(fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat) := by
    rw [← hscaleU]; simp only [EvmWord.val256]; ring
  have htele := fullDivN2V5_three_step_nat hfirst hR2.1 hR1.1 hR0.1
  rw [hscaleV] at htele
  refine ⟨htele, ?_⟩
  rw [← hscaleV]; exact hR0.2

/-- For the n=2 (two-limb) divisor, `2 * val256 v0 v1 0 0 < 2^256`. -/
theorem n2_two_val256_v_lt_pow256 (v0 v1 : Word) :
    2 * val256 v0 v1 0 0 < 2 ^ 256 := by
  have h := n2_val256_v_lt_pow128 v0 v1
  have he : (2 : Nat) ^ 256 = 2 * (2 ^ 128 * 2 ^ 127) := by norm_num
  rw [he]
  have hp : 0 < (2 : Nat) ^ 127 := by positivity
  calc 2 * val256 v0 v1 0 0 < 2 * 2 ^ 128 := by omega
    _ ≤ 2 * (2 ^ 128 * 2 ^ 127) := by
        have : (2 : Nat) ^ 128 ≤ 2 ^ 128 * 2 ^ 127 := Nat.le_mul_of_pos_right _ hp
        omega

/-- `callAddbackCarry2NzV5` on a `v2=v3=0`, `u3=0` window, from the call regime,
    the normalized top divisor limb, and the runtime borrow. -/
theorem callAddbackCarry2NzV5_of_borrow_of_call_shape
    (v0 v1 u0 u1 u2 uTop : Word)
    (hv1_norm : v1.toNat ≥ 2 ^ 63)
    (hcall : u2.toNat < v1.toNat)
    (hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0) = true) :
    callAddbackCarry2NzV5 v0 v1 0 0 u0 u1 u2 0 uTop := by
  have hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hv1z : v1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hv1z] at hv1_norm
    simp at hv1_norm
  exact callAddbackCarry2NzV5_of_borrow_n2 v0 v1 0 0 u0 u1 u2 0 uTop hbnz
    (divKTrialCallV5QHat_le_window_div_plus_two_of_call u0 u1 u2 v0 v1 hv1_norm hcall)
    (n2_two_val256_v_lt_pow256 v0 v1) hborrow


open EvmWord EvmAsm.Rv64

/-- `isAddbackCarry2NzN2Max` on a `v2=v3=0`, `u3=0` window, from the max regime,
    the normalized top divisor limb, and the runtime borrow. -/
theorem isAddbackCarry2NzN2Max_of_borrow_of_max_shape
    (v0 v1 u0 u1 u2 uTop : Word)
    (hv1_norm : v1.toNat ≥ 2 ^ 63)
    (hbltu : ¬ BitVec.ult u2 v1)
    (hborrow : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0) = true) :
    isAddbackCarry2NzN2Max v0 v1 0 0 u0 u1 u2 0 uTop := by
  unfold isAddbackCarry2NzN2Max
  have hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hv1z : v1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hv1z] at hv1_norm
    simp at hv1_norm
  have hq_over : (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 0 / val256 v0 v1 0 0 + 2 :=
    max_trial_local_overestimate_n2_of_not_ult v0 v1 u0 u1 u2 hv1_norm hbltu
  have hle1 := mulsubN4_c3_le_one_of_plus_two_of_v_lt hbnz hq_over
    (n2_two_val256_v_lt_pow256 v0 v1)
  have hne0 : (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 ≠ 0 := by
    intro h0
    unfold mulsubN4_c3 at hborrow
    rw [h0] at hborrow
    have : ¬ BitVec.ult uTop (0 : Word) := by rw [BitVec.ult_eq_decide]; simp
    exact this hborrow
  have hne0' :
      (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2.toNat ≠ 0 := by
    intro hz
    exact hne0 (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
  have hc3eq : (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    apply BitVec.eq_of_toNat_eq
    show (mulsubN4 (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0).2.2.2.2.toNat = 1
    omega
  exact isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
    (signExtend12 4095 : Word) v0 v1 0 0 u0 u1 u2 0 uTop hbnz hq_over (fun _ => hc3eq)

end EvmAsm.Evm64
