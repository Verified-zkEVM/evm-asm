/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FrameShift0

  The shift=0 loop-state frame for the v5 n=3 shift=0 epilogue composition: the
  cells/registers the shift=0 DIV epilogue does NOT touch, carried around it.
  Shift=0 counterpart of `fullDivN3FrameNoX1V5` (FullPathN3V5NoNopDenormDefs), with
  the two digit iterates at the RAW shift=0 inputs
    `r1 = iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0`,
    `r0 = iterN3V5 bltu_0 b0 b1 b2 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1`,
  and the dividend window `(a0,a1,a2,a3)` copied verbatim (no normalization).
  n=3 analog of `FullPathN2V5FrameShift0`.  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Families
public import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Shift=0 raw digit-1 (high) iterate (`iterN3V5` over the raw divisor `(b0,b1,b2,0)`
    and the digit-1 window `(a1,a2,a3,0,0)`). -/
def n3Shift0R1 (bltu_1 : Bool) (a1 a2 a3 b0 b1 b2 : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0

/-- Shift=0 raw digit-0 (low) iterate, threaded on `n3Shift0R1`. -/
def n3Shift0R0 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let r1 := n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2
  iterN3V5 bltu_0 b0 b1 b2 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

/-- Shift=0 digit-0 mulsub borrow `c3` (the loop-exit `x10`). -/
def n3Shift0C3 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 : Word) : Word :=
  let r1 := n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2
  (mulsubN4
      (if bltu_0 then divKTrialCallV5QHat r1.2.2.2.1 r1.2.2.1 b2 else (signExtend12 4095 : Word))
      b0 b1 b2 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2

/-- Shift=0 loop-state frame (analog of `fullDivN3FrameNoX1V5`), parameterized on
    the two loop-branch bits.  The cells/regs the shift=0 DIV epilogue does not
    touch. -/
@[irreducible] def fullDivN3FrameShift0V5 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Assertion :=
  let r1 := n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2
  let r0 := n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2
  let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem
  let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 b2 scratch1 else scratch1
  let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else retMem
  let scratchD1 := if bltu_1 then b2 else dMem
  let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b2 else dloMem
  let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 a3 else scratchUn0
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
  ((sp + signExtend12 4056) ↦ₘ r0.2.1) ** ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
  ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
  (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b2 else scratchD1)) **
  (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b2 else scratchDLo1)) **
  (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.2.1 else scratchUn01)) **
  (sp + signExtend12 3936 ↦ₘ scratchMemF) **
  (.x1 ↦ᵣ raVal)

theorem fullDivN3FrameShift0V5_unfold {bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    fullDivN3FrameShift0V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
      retMem dMem dloMem scratchUn0 scratchMem raVal =
    (let r1 := n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2
     let r0 := n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2
     let scratch1 := if bltu_1 then divKTrialCallV5ScratchOut 0 a3 b2 scratchMem else scratchMem
     let scratchMemF := if bltu_0 then divKTrialCallV5ScratchOut r1.2.2.2.1 r1.2.2.1 b2 scratch1 else scratch1
     let scratchRet1 := if bltu_1 then (base + div128CallRetOff) else retMem
     let scratchD1 := if bltu_1 then b2 else dMem
     let scratchDLo1 := if bltu_1 then divKTrialCallV5DLo b2 else dloMem
     let scratchUn01 := if bltu_1 then divKTrialCallV5Un0 a3 else scratchUn0
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ r0.2.1) ** ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
     ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
     ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (if bltu_0 then (base + div128CallRetOff) else scratchRet1)) **
     (sp + signExtend12 3960 ↦ₘ (if bltu_0 then b2 else scratchD1)) **
     (sp + signExtend12 3952 ↦ₘ (if bltu_0 then divKTrialCallV5DLo b2 else scratchDLo1)) **
     (sp + signExtend12 3944 ↦ₘ (if bltu_0 then divKTrialCallV5Un0 r1.2.2.1 else scratchUn01)) **
     (sp + signExtend12 3936 ↦ₘ scratchMemF) **
     (.x1 ↦ᵣ raVal)) := by
  delta fullDivN3FrameShift0V5; rfl

theorem fullDivN3FrameShift0V5_pcFree {bltu_1 bltu_0 : Bool}
    {sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word} :
    (fullDivN3FrameShift0V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
      retMem dMem dloMem scratchUn0 scratchMem raVal).pcFree := by
  rw [fullDivN3FrameShift0V5_unfold]
  cases bltu_1 <;> cases bltu_0 <;>
    simp only [Bool.false_eq_true, if_true, if_false] <;> pcFree

end EvmAsm.Evm64
