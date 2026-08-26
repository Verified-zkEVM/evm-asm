/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormDefs

  The n=3 v5 denormalization-epilogue assertion families: `fullDivN3DenormPreV5`,
  `fullDivN3DenormPostV5`, `fullDivN3ScratchNoX1V5`, `fullDivN3ScratchMemV5`,
  `fullDivN3FrameNoX1V5`, and the bundled `fullDivN3UnifiedPostNoX1V5`.  Faithful
  v5 mirrors of the v4 families (`FullPathN3V4.lean` :210–302), over the v5 capped
  trial-division quotient/remainder accessors (`fullDivN3R1V5`/`R0V5`/`C3V5`) and
  the v5 trial scratch helpers (`divKTrialCallV5DLo`/`Un0`/`ScratchOut`).  These are
  the post-state defs the n=3 v5 denorm epilogue and post-bridge (bead 9.3.3.6 →
  9.3.3.4) build on.  Bead `evm-asm-wbc4i.9.3.3.6`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnified
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Families

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 v5 denorm precondition: call-path arithmetic matches the v5 callable trial
    qhat.  v5 mirror of `fullDivN3DenormPreV4`. -/
@[irreducible]
def fullDivN3DenormPreV5 (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let v := fullDivN3NormV b0 b1 b2 b3
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) **
   (.x10 ↦ᵣ fullDivN3C3V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
   ((sp + signExtend12 3992) ↦ₘ shift) **
   ((sp + signExtend12 4056) ↦ₘ r0.2.1) **
   ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
   ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) **
   ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
   ((sp + signExtend12 4088) ↦ₘ r0.1) **
   ((sp + signExtend12 4080) ↦ₘ r1.1) **
   ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
   ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
   ((sp + signExtend12 32) ↦ₘ v.1) **
   ((sp + signExtend12 40) ↦ₘ v.2.1) **
   ((sp + signExtend12 48) ↦ₘ v.2.2.1) **
   ((sp + signExtend12 56) ↦ₘ v.2.2.2))

/-- N3 v5 denorm postcondition paired with `fullDivN3DenormPreV5`. -/
@[irreducible]
def fullDivN3DenormPostV5 (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1
    r0.1 r1.1 (0 : Word) (0 : Word) **
  ((sp + signExtend12 3992) ↦ₘ shift)

/-- N3 v5 div128-call scratch cells (`x1`-free), branch-selected per digit. -/
@[irreducible]
def fullDivN3ScratchNoX1V5 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word) :
    Assertion :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else retMem
  let scratchD1 := if bltu_1 then v.2.2.1 else dMem
  let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo v.2.2.1 else dloMem
  let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 u.2.2.2.1 else scratchUn0
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then v.2.2.1 else scratchD1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo v.2.2.1 else scratchDLo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.2.1 else scratchUn01))

/-- N3 v5 final div128-call scratch memory cell value at `sp+3936`. -/
@[irreducible]
def fullDivN3ScratchMemV5 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Word :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let scratch1 := if bltu_1 then
      divKTrialCallV5ScratchOut u.2.2.2.2 u.2.2.2.1 v.2.2.1 scratchMem
    else
      scratchMem
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 v.2.2.1 scratch1
  else
    scratch1

/-- N3 v5 epilogue frame (`x1`-free) carried alongside the denorm post. -/
@[irreducible]
def fullDivN3FrameNoX1V5 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 : Word) :
    Assertion :=
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  fullDivN3ScratchNoX1V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0

/-- Bundled n=3 v5 unified post (`x1`-free): denorm post + epilogue frame + final
    div128 scratch cell.  v5 mirror of `fullDivN3UnifiedPostNoX1V4`. -/
def fullDivN3UnifiedPostNoX1V5 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  fullDivN3DenormPostV5 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN3FrameNoX1V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 **
  ((sp + signExtend12 3936) ↦ₘ
    fullDivN3ScratchMemV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)

end EvmAsm.Evm64
