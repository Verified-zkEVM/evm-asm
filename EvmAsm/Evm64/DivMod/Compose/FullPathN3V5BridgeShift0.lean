/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5BridgeShift0

  The v5 n=3 shift=0 epilogue bridge: the loop result at `denormOff`
  (`loopN3UnifiedPostV5NoX1` at the raw shift=0 inputs `(b0,b1,b2,0)` /
  `(a1,a2,a3,0,0)/a0`, plus the a-cells and shift cell) reduces to the shift=0
  DIV-epilogue precondition (the pre of `evm_div_shift0_epilogue_spec_v5_noNop`)
  plus the untouched loop-state frame `fullDivN3FrameShift0V5`.  n=3 / 2-digit
  counterpart of `loopN2UnifiedPostV5NoX1_shift0_to_epiloguePre`.
  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FrameShift0
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnified

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Shift=0 epilogue bridge: loop post (raw inputs) + a-cells + shift cell ⊢
    shift=0 DIV-epilogue pre + `fullDivN3FrameShift0V5`. -/
theorem loopN3UnifiedPostV5NoX1_shift0_to_epiloguePre
    (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (h : PartialState)
    (hp : ((loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
              b0 b1 b2 0 a1 a2 a3 0 0 a0
              retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
            (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
             ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
             ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) h) :
    (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (sp + signExtend12 4056)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (sp + signExtend12 4088)) **
       (.x2 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
       (.x10 ↦ᵣ n3Shift0C3 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
       ((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
       ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ (0 : Word))) **
     fullDivN3FrameShift0V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
       retMem dMem dloMem scratchUn0 scratchMem raVal) h := by
  cases bltu_1 <;> cases bltu_0 <;>
    [ (delta loopN3UnifiedPostV5NoX1 loopIterPostN3Max at hp) ;
      (delta loopN3UnifiedPostV5NoX1 loopIterPostN3CallScratchNoX1 at hp) ;
      (delta loopN3UnifiedPostV5NoX1 loopIterPostN3Max at hp) ;
      (delta loopN3UnifiedPostV5NoX1 loopIterPostN3CallScratchNoX1 at hp) ] <;>
  · simp (config := { decide := true }) only [] at hp
    rw [loopExitPostN3_j0_eq] at hp
    delta n3Shift0R0 n3Shift0R1 n3Shift0C3 fullDivN3FrameShift0V5
    simp only [iterN3V5_false_eq_max, iterN3V5_true_eq]
    simp (config := { decide := true }) only
      [ite_true, ite_false, n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56] at hp ⊢
    xperm_hyp hp

end EvmAsm.Evm64
