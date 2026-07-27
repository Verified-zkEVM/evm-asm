/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FrameShift0

  The shift=0 loop-state frame for the v5 n=1 shift=0 epilogue composition: the
  cells/registers the shift=0 DIV epilogue does NOT touch, carried around it.
  Shift=0 counterpart of `fullDivN1FrameV5` (FullPathN1V5Full), with the four
  digit iterates at the shift=0 inputs
    `R3 = iterN1Call_v5 b0 0 0 0 a3 0 0 0 0`, `R2 = fullN1S2 …`,
    `R1 = fullN1S1 …`, `R0 = fullN1S0 …`,
  and the dividend window `(a0,a1,a2,a3)` copied verbatim (no normalization).

  Provides the def + `_unfold` + `pcFree` the forthcoming
  `loopN1UnifiedPostV5 → shift0-epilogue-pre` bridge frames around the epilogue.
  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop
import EvmAsm.Evm64.DivMod.LoopIterN1.N1V5IterChainShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Shift=0 loop-state frame (analog of `fullDivN1FrameV5`). -/
@[irreducible] def fullDivN1FrameShift0V5 (sp base a0 a1 a2 a3 b0 scratchMem : Word) : Assertion :=
  let R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0
  let R2 := fullN1S2 b0 0 0 0 a3 0 0 0 0 a2
  let R1 := fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1
  let R0 := fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
  ((sp + signExtend12 4056) ↦ₘ R0.2.1) ** ((sp + signExtend12 4048) ↦ₘ R0.2.2.1) **
  ((sp + signExtend12 4040) ↦ₘ R0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ R0.2.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b0) **
  ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b0) **
  ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a0) **
  ((sp + signExtend12 3936) ↦ₘ
    divKTrialCallV5ScratchOut R1.2.1 a0 b0
      (divKTrialCallV5ScratchOut R2.2.1 a1 b0
        (divKTrialCallV5ScratchOut R3.2.1 a2 b0
          (divKTrialCallV5ScratchOut 0 a3 b0 scratchMem)))) **
  regOwn .x1

theorem fullDivN1FrameShift0V5_unfold {sp base a0 a1 a2 a3 b0 scratchMem : Word} :
    fullDivN1FrameShift0V5 sp base a0 a1 a2 a3 b0 scratchMem =
    (let R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0
     let R2 := fullN1S2 b0 0 0 0 a3 0 0 0 0 a2
     let R1 := fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1
     let R0 := fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0
     (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ R0.2.1) ** ((sp + signExtend12 4048) ↦ₘ R0.2.2.1) **
  ((sp + signExtend12 4040) ↦ₘ R0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ R0.2.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
     ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
     ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ b0) **
     ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo b0) **
     ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 a0) **
     ((sp + signExtend12 3936) ↦ₘ
       divKTrialCallV5ScratchOut R1.2.1 a0 b0
         (divKTrialCallV5ScratchOut R2.2.1 a1 b0
           (divKTrialCallV5ScratchOut R3.2.1 a2 b0
             (divKTrialCallV5ScratchOut 0 a3 b0 scratchMem)))) **
     regOwn .x1) := by
  delta fullDivN1FrameShift0V5; rfl

theorem fullDivN1FrameShift0V5_pcFree {sp base a0 a1 a2 a3 b0 scratchMem : Word} :
    (fullDivN1FrameShift0V5 sp base a0 a1 a2 a3 b0 scratchMem).pcFree := by
  rw [fullDivN1FrameShift0V5_unfold]; pcFree

end EvmAsm.Evm64
