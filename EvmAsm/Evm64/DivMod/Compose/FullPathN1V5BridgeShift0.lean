/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5BridgeShift0

  The v5 n=1 shift=0 epilogue bridge: the loop result at denormOff
  (`loopN1UnifiedPostV5` at the shift=0 inputs, plus the a-cells and shift cell)
  reduces to the shift=0 DIV-epilogue precondition plus the untouched loop-state
  frame `fullDivN1FrameShift0V5`.  Shift=0 counterpart of
  `loopN1UnifiedPostV5_to_denormPreV5`.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FrameShift0
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5ToDenormShift0
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full
meta import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5FrameShift0
meta import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5ToDenormShift0
meta import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full

@[expose] public section

namespace EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

attribute [local irreducible] EvmWord.val256 div128Quot_v5 iterWithDoubleAddback mulsubN4 clzResult

theorem loopN1UnifiedPostV5_shift0_to_epiloguePre
    (sp base a0 a1 a2 a3 b0 scratchMem : Word) (h : PartialState)
    (hp : (loopN1UnifiedPostV5 sp base b0 0 0 0 a3 0 0 0 0 a2 a1 a0 scratchMem **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1)) h) :
    (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (sp + signExtend12 4056)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (sp + signExtend12 4088)) **
       (.x2 ↦ᵣ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1) **
       (.x10 ↦ᵣ (mulsubN4
            (div128Quot_v5 (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 a0 b0)
            b0 0 0 0 a0
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
            (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1).2.2.2.2) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b0).1) **
       ((sp + signExtend12 4088) ↦ₘ (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1) **
       ((sp + signExtend12 4080) ↦ₘ (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1) **
       ((sp + signExtend12 4072) ↦ₘ (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1) **
       ((sp + signExtend12 4064) ↦ₘ (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) **
     fullDivN1FrameShift0V5 sp base a0 a1 a2 a3 b0 scratchMem) h := by
  rw [fullDivN1FrameShift0V5_unfold]
  delta loopN1UnifiedPostV5 loopN1Iter210PostV5 loopN1Iter10PostV5 loopIterPostN1V5
    loopIterPostN1CallV5 at hp
  dsimp only [] at hp
  rw [loopExitPostN1_j0_eq] at hp
  rw [← iterN1Call_v5_unfoldU'] at hp
  delta fullN1S0 fullN1S1 fullN1S2
  dsimp only []
  simp only [n1_ub3_off4064, n1_qa3, n2_ub2_off4064, n2_qa2,
      n3_ub1_off4064, n3_qa1, iterN1V5_true, if_true,
      se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp ⊢
  set R3 := iterN1Call_v5 b0 0 0 0 a3 0 0 0 0 with hR3
  set R2 := iterN1Call_v5 b0 0 0 0 a2 R3.2.1 R3.2.2.1 R3.2.2.2.1 R3.2.2.2.2.1 with hR2
  set R1 := iterN1Call_v5 b0 0 0 0 a1 R2.2.1 R2.2.2.1 R2.2.2.2.1 R2.2.2.2.2.1 with hR1
  set R0 := iterN1Call_v5 b0 0 0 0 a0 R1.2.1 R1.2.2.1 R1.2.2.2.1 R1.2.2.2.2.1 with hR0
  xperm_chunked hp

end EvmAsm.Evm64
