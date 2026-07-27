/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5BridgeShift0

  The v5 n=2 shift=0 epilogue bridge: the loop result at `denormOff`
  (`loopN2UnifiedPostV5NoX1` at the raw shift=0 inputs `(b0,b1,0,0)` /
  `(a2,a3,0,0,0)`, plus `x1`, the a-cells, and the shift cell) reduces to the
  shift=0 DIV-epilogue precondition (the 16-atom pre of
  `evm_div_shift0_epilogue_spec_v5_noNop`) plus the untouched loop-state frame
  `fullDivN2FrameShift0V5`.  Shift=0 / 3-digit / Bool-parameterized counterpart
  of n1's `loopN1UnifiedPostV5_shift0_to_epiloguePre` and of the shift≠0 bridges
  `loopN2UnifiedPostV5NoX1_to_fullDivN2DenormPreV5_frame_*`.  Bead
  `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5FrameShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopDispatchShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

attribute [local irreducible] EvmWord.val256 div128Quot_v5 iterWithDoubleAddback
  mulsubN4 clzResult

/-- Per-case shift=0 bridge tactic: `delta`-unfold the loop post arm + goal
    helpers (syntactic — keeps the deep call terms opaque), resolve the branch
    `ite`s, normalize the j=0 loop-exit addresses, then permute. -/
local macro "n2s0_bridge_case " hp:ident " | " lip:ident ", " r2:ident ", " r1:ident : tactic =>
  `(tactic|
    (delta loopN2UnifiedPostV5NoX1 $lip $r2 $r1 at $hp:ident
     delta n2Shift0R0 n2Shift0R1 n2Shift0R2 n2Shift0C3 fullDivN2FrameShift0V5 iterN2V5
     simp (config := { decide := true }) only [ite_true, ite_false] at $hp:ident ⊢
     rw [loopExitPostN2_j0_eq] at $hp:ident
     simp (config := { decide := true }) only
       [n2_ub2_off4064, n2_qa2, n3_ub1_off4064, n3_qa1,
        se12_32, se12_40, se12_48, se12_56] at $hp:ident ⊢
     sep_perm $hp))

set_option linter.unusedSimpArgs false in
/-- Shift=0 epilogue bridge: loop post (raw inputs) + a-cells + shift cell ⊢
    shift=0 DIV-epilogue pre + `fullDivN2FrameShift0V5`. -/
theorem loopN2UnifiedPostV5NoX1_shift0_to_epiloguePre
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (h : PartialState)
    (hp : ((loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
              b0 b1 0 0 a2 a3 0 0 0 a1 a0
              retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
            (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
             ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
             ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
             ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) :
    (((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (sp + signExtend12 4056)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (sp + signExtend12 4088)) **
       (.x2 ↦ᵣ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).2.2.2.2.1) **
       (.x10 ↦ᵣ n2Shift0C3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1) **
       ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1) **
       ((sp + signExtend12 4088) ↦ₘ (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1) **
       ((sp + signExtend12 4080) ↦ₘ (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1) **
       ((sp + signExtend12 4072) ↦ₘ (n2Shift0R2 bltu_2 a2 a3 b0 b1).1) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) **
     fullDivN2FrameShift0V5 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
       retMem dMem dloMem scratchUn0 scratchMem raVal) h := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
  · n2s0_bridge_case hp | loopIterPostN2Max, r2MMTN2V5, r1MMTN2V5                  -- f f f
  · n2s0_bridge_case hp | loopIterPostN2CallScratchNoX1, r2MMTN2V5, r1MMTN2V5      -- f f t
  · n2s0_bridge_case hp | loopIterPostN2Max, r2MTTN2V5, r1MTTN2V5                  -- f t f
  · n2s0_bridge_case hp | loopIterPostN2CallScratchNoX1, r2MTTN2V5, r1MTTN2V5      -- f t t
  · n2s0_bridge_case hp | loopIterPostN2Max, r2CCCN2V5, r1TMMN2V5                  -- t f f
  · n2s0_bridge_case hp | loopIterPostN2CallScratchNoX1, r2CCCN2V5, r1TMMN2V5      -- t f t
  · n2s0_bridge_case hp | loopIterPostN2Max, r2CCCN2V5, r1CCCN2V5                  -- t t f
  · n2s0_bridge_case hp | loopIterPostN2CallScratchNoX1, r2CCCN2V5, r1CCCN2V5      -- t t t

end EvmAsm.Evm64
