/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.State

  Bundled n=2 denorm precondition and preserved frame definitions.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Scratch

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def fullDivN2ScratchFinal (bltu_2 bltu_1 bltu_0 : Bool)
    (base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    N2ScratchState :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  fullDivN2Scratch0 bltu_2 bltu_1 bltu_0 base v.2.1 u.2.2.2.1 r2.2.1 r1.2.1
    retMem dMem dloMem scratch_un0

@[irreducible]
def fullDivN2DenormPre (bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN2Shift b1
  let v := fullDivN2NormV b0 b1 b2 b3
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
   (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
   (.x2 ↦ᵣ r0.2.2.2.2.1) **
   (.x10 ↦ᵣ fullDivN2C3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
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
def fullDivN2Frame (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    Assertion :=
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let scratch := fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ n2ScratchRet scratch) **
  (sp + signExtend12 3960 ↦ₘ n2ScratchD scratch) **
  (sp + signExtend12 3952 ↦ₘ n2ScratchDLo scratch) **
  (sp + signExtend12 3944 ↦ₘ n2ScratchUn0 scratch)

theorem fullDivN2ScratchFinal_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    fullDivN2Scratch0 bltu_2 bltu_1 bltu_0 base v.2.1 u.2.2.2.1 r2.2.1 r1.2.1
      retMem dMem dloMem scratch_un0 := by
  delta fullDivN2ScratchFinal
  rfl

theorem fullDivN2DenormPre_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2DenormPre bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 =
    let shift := fullDivN2Shift b1
    let v := fullDivN2NormV b0 b1 b2 b3
    let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ sp + signExtend12 4056) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ sp + signExtend12 4088) **
     (.x2 ↦ᵣ r0.2.2.2.2.1) **
     (.x10 ↦ᵣ fullDivN2C3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) **
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
     ((sp + signExtend12 56) ↦ₘ v.2.2.2)) := by
  delta fullDivN2DenormPre
  rfl

theorem fullDivN2Frame_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Frame bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
      retMem dMem dloMem scratch_un0 =
    let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    let scratch := fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
    ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
    ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
    (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
    (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
    (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
    (sp + signExtend12 3968 ↦ₘ n2ScratchRet scratch) **
    (sp + signExtend12 3960 ↦ₘ n2ScratchD scratch) **
    (sp + signExtend12 3952 ↦ₘ n2ScratchDLo scratch) **
    (sp + signExtend12 3944 ↦ₘ n2ScratchUn0 scratch) := by
  delta fullDivN2Frame
  rfl

end EvmAsm.Evm64
