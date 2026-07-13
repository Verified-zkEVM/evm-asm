/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5FrameShift0

  The shift=0 loop-state frame for the v5 n=2 shift=0 epilogue composition: the
  cells/registers the shift=0 DIV epilogue does NOT touch, carried around it.
  Shift=0 counterpart of `fullDivN2FrameNoX1V5` (FullPathN2V5Families), with the
  three digit iterates at the RAW shift=0 inputs
    `r2 = iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0`,
    `r1 = iterN2V5 bltu_1 b0 b1 0 0 a1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1`,
    `r0 = iterN2V5 bltu_0 b0 b1 0 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1`,
  and the dividend window `(a0,a1,a2,a3)` copied verbatim (no normalization).

  The scratch dispatch (cells `sp+3968 … sp+3936`) mirrors
  `fullDivN2ScratchNoX1V5`/`fullDivN2ScratchMemV5`, but over `(b0,b1,0,0)` and the
  raw `(a2,a3,0,0,0)` digit-2 window.

  Provides the def + `_unfold` + `pcFree` the forthcoming
  `loopN2UnifiedPostV5NoX1 → shift0-epilogue-pre` bridge frames around the
  epilogue.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Shift=0 raw digit-2 iterate (`iterN2V5` over the raw divisor `(b0,b1,0,0)`
    and the digit-2 window `(a2,a3,0,0,0)`). -/
def n2Shift0R2 (bltu_2 : Bool) (a2 a3 b0 b1 : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0

/-- Shift=0 raw digit-1 iterate, threaded on `n2Shift0R2`. -/
def n2Shift0R1 (bltu_2 bltu_1 : Bool) (a1 a2 a3 b0 b1 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r2 := n2Shift0R2 bltu_2 a2 a3 b0 b1
  iterN2V5 bltu_1 b0 b1 0 0 a1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

/-- Shift=0 raw digit-0 iterate, threaded on `n2Shift0R1`. -/
def n2Shift0R0 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r1 := n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1
  iterN2V5 bltu_0 b0 b1 0 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

/-- Shift=0 digit-0 mulsub borrow `c3` (the loop-exit `x10`). -/
def n2Shift0C3 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 : Word) : Word :=
  let r1 := n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1
  (mulsubN4
      (if bltu_0 then divKTrialCallV5QHat r1.2.2.1 r1.2.1 b1 else (signExtend12 4095 : Word))
      b0 b1 0 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

/-- Shift=0 loop-state frame (analog of `fullDivN2FrameNoX1V5`), parameterized on
    the three loop-branch bits.  The cells/regs the shift=0 DIV epilogue does not
    touch. -/
@[irreducible] def fullDivN2FrameShift0V5 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Assertion :=
  let r2 := n2Shift0R2 bltu_2 a2 a3 b0 b1
  let r1 := n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1
  let r0 := n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1
  -- scratch dispatch (mirror of fullDivN2ScratchMemV5 / fullDivN2ScratchNoX1V5)
  let scratch2 := if bltu_2 then divKTrialCallV5ScratchOut 0 a3 b1 scratchMem else scratchMem
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 b1 scratch2 else scratch2
  let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 b1 scratch1 else scratch1
  let scratchRet2 := if bltu_2 then (base + div128CallRetOff) else retMem
  let scratchD2 := if bltu_2 then b1 else dMem
  let scratchDLo2 := if bltu_2 then divKTrialCallV5DLo b1 else dloMem
  let scratchUn02 := if bltu_2 then divKTrialCallV5Un0 a3 else scratchUn0
  let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else scratchRet2
  let scratchD1 := if bltu_1 then b1 else scratchD2
  let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b1 else scratchDLo2
  let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 r2.2.1 else scratchUn02
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
  ((sp + signExtend12 4056) ↦ₘ r0.2.1) ** ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
  ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b1 else scratchD1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b1 else scratchDLo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.1 else scratchUn01)) **
  (sp + signExtend12 3936 ↦ₘ scratchMemF) **
  (.x1 ↦ᵣ raVal)

theorem fullDivN2FrameShift0V5_unfold {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    fullDivN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
      retMem dMem dloMem scratchUn0 scratchMem raVal =
    (let r2 := n2Shift0R2 bltu_2 a2 a3 b0 b1
     let r1 := n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1
     let r0 := n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1
     let scratch2 := if bltu_2 then divKTrialCallV5ScratchOut 0 a3 b1 scratchMem else scratchMem
     let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 b1 scratch2 else scratch2
     let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 b1 scratch1 else scratch1
     let scratchRet2 := if bltu_2 then (base + div128CallRetOff) else retMem
     let scratchD2 := if bltu_2 then b1 else dMem
     let scratchDLo2 := if bltu_2 then divKTrialCallV5DLo b1 else dloMem
     let scratchUn02 := if bltu_2 then divKTrialCallV5Un0 a3 else scratchUn0
     let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else scratchRet2
     let scratchD1 := if bltu_1 then b1 else scratchD2
     let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b1 else scratchDLo2
     let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 r2.2.1 else scratchUn02
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ r0.2.1) ** ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
     ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
     (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b1 else scratchD1)) **
     (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b1 else scratchDLo1)) **
     (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.1 else scratchUn01)) **
     (sp + signExtend12 3936 ↦ₘ scratchMemF) **
     (.x1 ↦ᵣ raVal)) := by
  delta fullDivN2FrameShift0V5; rfl

theorem fullDivN2FrameShift0V5_pcFree {bltu_2 bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    (fullDivN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
      retMem dMem dloMem scratchUn0 scratchMem raVal).pcFree := by
  rw [fullDivN2FrameShift0V5_unfold]
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;>
    simp only [Bool.false_eq_true, if_true, if_false] <;> pcFree

end EvmAsm.Evm64
