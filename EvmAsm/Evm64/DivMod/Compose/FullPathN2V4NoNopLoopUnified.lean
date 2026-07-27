/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopLoopUnified

  Unified 8-case v4/no-NOP loop dispatcher for n=2, plus preloop bridge.
  Defines `loopN2UnifiedPostV4NoX1` (8 cases via bltu_2 × bltu_1 × bltu_0)
  and proves `divK_loop_n2_unified_from_source_exact_loopIterScratch_v4_noNop`
  by dispatching to the 8 per-case source theorems.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopCallCallCall
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopCallCallMax
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopMaxMaxMax
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopTMT
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopTMM
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopMTT
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopMTM
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopMMT
import EvmAsm.Evm64.DivMod.Compose.FullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Branches
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Bridge
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.BridgeFalse
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.BridgeTrue
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Full
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Scratch
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.State

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Unified n=2 v4/no-NOP loop postcondition.  Mirrors `loopN2UnifiedPost` but
    exposes the v4 div128 scratch cells explicitly and keeps the caller-owned
    `x1` outside the post.  Dispatches on all 8 (bltu_2, bltu_1, bltu_0)
    combinations of the three loop iterations. -/
@[irreducible]
def loopN2UnifiedPostV4NoX1 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  match bltu_2, bltu_1, bltu_0 with
  | true, true, true => -- CCC: all call
    let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, true, false => -- CCM: call-call-max
    let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 r2.2.1)) **
      (sp + signExtend12 3936 ↦ₘ scratch1)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, false, true => -- TMT: call-max-call
    let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1TMTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratch2
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, false, false => -- TMM: call-max-max
    let r2 := r2CCCN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1TMMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 u1)) **
      (sp + signExtend12 3936 ↦ₘ scratch2)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, true, true => -- MTT: max-call-call
    let r2 := r2MTTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MTTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, true, false => -- MTM: max-call-max
    let r2 := r2MTMN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MTMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 r2.2.1)) **
      (sp + signExtend12 3936 ↦ₘ scratch1)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, false, true => -- MMT: max-max-call
    let r2 := r2MMTN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MMTN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch0 := divKTrialCallV4ScratchOut r1.2.2.1 r1.2.1 v1 scratchMem
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV4QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, false, false => -- MMM: all max
    let r2 := r2MMMN2V4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MMMN2V4 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      (sp + signExtend12 3944 ↦ₘ scratchUn0) **
      (sp + signExtend12 3936 ↦ₘ scratchMem)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))

/-- Branch-selected n=2 v4 loop iteration, local to the lower loop layer.

    This duplicates the branch shape of `iterN2V4` without importing the
    higher full-path family module, which depends on this lower loop module. -/
def loopN2IterSelectedV4 (bltu : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then
    iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp] theorem loopN2IterSelectedV4_false
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV4 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  rfl

@[simp] theorem loopN2IterSelectedV4_true
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV4 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [loopN2IterSelectedV4]

/-- Selected per-iteration carry facts for the normalized n=2 loop source.

    This is the compose-layer replacement shape for `Carry2NzAll`: it carries
    only the facts selected by the actual branch booleans and names the
    intermediate states through `loopN2IterSelectedV4`.  Downstream
    loop/preloop wrappers can consume this without exposing the false
    universal carry package. -/
@[irreducible]
def loopN2SelectedCarryV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := loopN2IterSelectedV4 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := loopN2IterSelectedV4 bltu_1 v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  (if bltu_2 then
    loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
      u0 u1 u2 u3 uTop
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3
      u0 u1 u2 u3 uTop) ∧
  (if bltu_1 then
    loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) ∧
  (if bltu_0 then
    loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)

/-- First selected n=2 normalized-loop carry component, for `j=2`. -/
theorem loopN2SelectedCarryV4_j2
    (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hcarry : loopN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    if bltu_2 then
      loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0 u1 u2 u3 uTop
    else
      isAddbackCarry2NzN2Max v0 v1 v2 v3
        u0 u1 u2 u3 uTop := by
  rw [loopN2SelectedCarryV4] at hcarry
  exact hcarry.1

/-- Second selected n=2 normalized-loop carry component, for `j=1`. -/
theorem loopN2SelectedCarryV4_j1
    (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hcarry : loopN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    let r2 := loopN2IterSelectedV4 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    if bltu_1 then
      loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    else
      isAddbackCarry2NzN2Max v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 := by
  rw [loopN2SelectedCarryV4] at hcarry
  exact hcarry.2.1

/-- Third selected n=2 normalized-loop carry component, for `j=0`. -/
theorem loopN2SelectedCarryV4_j0
    (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hcarry : loopN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    let r2 := loopN2IterSelectedV4 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := loopN2IterSelectedV4 bltu_1 v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    if bltu_0 then
      loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    else
      isAddbackCarry2NzN2Max v0 v1 v2 v3
        u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  rw [loopN2SelectedCarryV4] at hcarry
  exact hcarry.2.2

/-- Build the n=2 max-max-max source conditions from selected carry evidence. -/
theorem loopN2MaxMaxMaxSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 false false false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxMaxMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2MaxMaxMaxSourceConds_unfold]
  simp only [loopN2IterSelectedV4_false, r2MMMN2V4_eq, r1MMMN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Build the n=2 max-max-call source conditions from selected carry evidence. -/
theorem loopN2MaxMaxCallSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 false false true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxMaxCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2MaxMaxCallSourceConds_unfold]
  simp only [loopN2IterSelectedV4_false, r2MMTN2V4_eq, r1MMTN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Build the n=2 max-call-max source conditions from selected carry evidence. -/
theorem loopN2MaxCallMaxSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 false true false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxCallMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2MaxCallMaxSourceConds_unfold]
  simp only [loopN2IterSelectedV4_false, loopN2IterSelectedV4_true,
    r2MTMN2V4_eq, r1MTMN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Build the n=2 max-call-call source conditions from selected carry evidence. -/
theorem loopN2MaxCallCallSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 false true true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxCallCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2MaxCallCallSourceConds_unfold]
  simp only [loopN2IterSelectedV4_false, loopN2IterSelectedV4_true,
    r2MTTN2V4_eq, r1MTTN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Build the n=2 call-max-max source conditions from selected carry evidence. -/
theorem loopN2CallMaxMaxSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 true false false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallMaxMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2CallMaxMaxSourceConds_unfold]
  simp only [loopN2IterSelectedV4_true, loopN2IterSelectedV4_false,
    r2CCCN2V4_eq, r1TMMN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Build the n=2 call-max-call source conditions from selected carry evidence. -/
theorem loopN2CallMaxCallSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 true false true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallMaxCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2CallMaxCallSourceConds_unfold]
  simp only [loopN2IterSelectedV4_true, loopN2IterSelectedV4_false,
    r2CCCN2V4_eq, r1TMTN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Build the n=2 call-call-max source conditions from selected carry evidence. -/
theorem loopN2CallCallMaxSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 true true false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallCallMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2CallCallMaxSourceConds_unfold]
  simp only [loopN2IterSelectedV4_true, r2CCCN2V4_eq, r1CCCN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Build the n=2 call-call-call source conditions from selected carry evidence. -/
theorem loopN2CallCallCallSourceConds_of_selectedCarryV4
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV4 true true true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallCallCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV4] at hcarry
  rw [loopN2CallCallCallSourceConds_unfold]
  simp only [loopN2IterSelectedV4_true, r2CCCN2V4_eq, r1CCCN2V4_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- Unified n=2 v4 no-NOP loop source theorem, dispatching to the 8 per-case
    proofs via `bltu_2 × bltu_1 × bltu_0`.  Preserves caller-owned exact `x1`.
    The 672-step bound accommodates the worst-case (all-call) path; lighter paths
    use `cpsTripleWithin_mono_nSteps` to fit.

    Legacy compatibility surface: this still consumes the raw `Carry2NzAll`
    package. New v4 n=2 work should use the selected-carry sibling in
    `FullPathN2V4NoNopLoopSelected`. -/
theorem divK_loop_n2_unified_from_source_exact_loopIterScratch_v4_noNop
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false => BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1
      | true =>
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 672 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV4NoX1 bltu_2 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
  · -- FFF = MMM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds : loopN2MaxMaxMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2MaxMaxMaxSourceConds_unfold]; simp only [r2MMMN2V4_eq, r1MMMN2V4_eq]
      refine ⟨hb2, ?_, hb1, ?_, hb0, ?_⟩
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0Orig0
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxMaxMaxSourceFinalPostNoX1_unfold, r2MMMN2V4_eq, r1MMMN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MMMN2V4_eq, r1MMMN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_max_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem hconds)
  · -- FFT = MMT
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds : loopN2MaxMaxCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2MaxMaxCallSourceConds_unfold]; simp only [r2MMTN2V4_eq, r1MMTN2V4_eq]
      refine ⟨hb2, hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop, hb1,
              hcarry2 (signExtend12 4095) u0Orig1 _ _ _ _, hb0, ?_⟩
      unfold loopBodyN2CallAddbackCarry2NzV4
      exact hcarry2 (divKTrialCallV4QHat _ _ v1) u0Orig0 _ _ _ _
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxMaxCallSourceFinalPostNoX1_unfold, r2MMTN2V4_eq, r1MMTN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MMTN2V4_eq, r1MMTN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_max_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTF = MTM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : ¬BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds : loopN2MaxCallMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2MaxCallMaxSourceConds_unfold]; simp only [r2MTMN2V4_eq, r1MTMN2V4_eq]
      refine ⟨hb2, ?_, hb1, ?_, hb0, ?_⟩
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0Orig0
          (iterWithDoubleAddback
            (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
          (iterWithDoubleAddback
            (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
          (iterWithDoubleAddback
            (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
          (iterWithDoubleAddback
            (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxCallMaxSourceFinalPostNoX1_unfold, r2MTMN2V4_eq, r1MTMN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MTMN2V4_eq, r1MTMN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_call_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTT = MTT
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds : loopN2MaxCallCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2MaxCallCallSourceConds_unfold]; simp only [r2MTTN2V4_eq, r1MTTN2V4_eq]
      refine ⟨hb2, hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop, hb1, ?_, hb0, ?_⟩
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat _ _ v1) u0Orig1 _ _ _ _
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat _ _ v1) u0Orig0 _ _ _ _
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2MaxCallCallSourceFinalPostNoX1_unfold, r2MTTN2V4_eq, r1MTTN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2MTTN2V4_eq, r1MTTN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_max_call_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFF = TMM
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds : loopN2CallMaxMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2CallMaxMaxSourceConds_unfold]; simp only [r2CCCN2V4_eq, r1TMMN2V4_eq]
      refine ⟨hb2, ?_, hb1, ?_, hb0, ?_⟩
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat u2 u1 v1) u0 u1 u2 u3 uTop
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0Orig0
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallMaxMaxSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1TMMN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1TMMN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_max_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFT = TMT
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds : loopN2CallMaxCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2CallMaxCallSourceConds_unfold]; simp only [r2CCCN2V4_eq, r1TMTN2V4_eq]
      refine ⟨hb2, ?_, hb1, hcarry2 (signExtend12 4095) u0Orig1 _ _ _ _, hb0, ?_⟩
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat u2 u1 v1) u0 u1 u2 u3 uTop
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat _ _ v1) u0Orig0 _ _ _ _
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallMaxCallSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1TMTN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1TMTN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_max_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTF = CCM
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : ¬BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds : loopN2CallCallMaxSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2CallCallMaxSourceConds_unfold]; simp only [r2CCCN2V4_eq, r1CCCN2V4_eq]
      refine ⟨hb2, ?_, hb1, ?_, hb0, ?_⟩
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat u2 u1 v1) u0 u1 u2 u3 uTop
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          u0Orig1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
      · unfold isAddbackCarry2NzN2Max
        exact hcarry2 (signExtend12 4095) u0Orig0
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
          (iterWithDoubleAddback
            (divKTrialCallV4QHat
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
              (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
            v0 v1 v2 v3 u0Orig1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallCallMaxSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1CCCN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1CCCN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_call_max_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTT = CCC
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm ▸ rfl
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 :=
      hbltu_1.symm ▸ rfl
    have hb0 : BitVec.ult (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds : loopN2CallCallCallSourceConds v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 := by
      rw [loopN2CallCallCallSourceConds_unfold]; simp only [r2CCCN2V4_eq, r1CCCN2V4_eq]
      refine ⟨hb2, ?_, hb1, ?_, hb0, ?_⟩
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat u2 u1 v1) u0 u1 u2 u3 uTop
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat _ _ v1) u0Orig1 _ _ _ _
      · unfold loopBodyN2CallAddbackCarry2NzV4
        exact hcarry2 (divKTrialCallV4QHat _ _ v1) u0Orig0 _ _ _ _
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
                      simp only [loopN2CallCallCallSourceFinalPostNoX1_unfold, r2CCCN2V4_eq, r1CCCN2V4_eq] at hp;
                      unfold loopN2UnifiedPostV4NoX1;
                      simp only [r2CCCN2V4_eq, r1CCCN2V4_eq];
                      xperm_hyp hp)
      (divK_loop_n2_call_call_call_from_source_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)

/-- Instantiate the v4/no-NOP n=2 unified loop with explicit normalized values.
    Separates loop application from preloop composition for heartbeat budgeting.
    Parameters match `evm_div_n2_loop_unified_inst_noNop` plus `scratchMem` and `raVal`.

    Legacy compatibility surface: this still consumes the raw `Carry2NzAll`
    package. New v4 n=2 work should use the selected-carry sibling. -/
theorem evm_div_n2_loop_unified_inst_noNop_exact_x1_v4
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift v0' v1' v2' v3' u0S u1S u2S u3S u4_s : Word)
    (v10_val v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u4_s v1')
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false => BitVec.ult (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1'
      | true =>
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
          v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1 v1')
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterN2Max v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, false =>
        BitVec.ult (iterN2Max v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1'
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
            (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
              v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1 v1')
          v0' v1' v2' v3' u1S
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV4QHat u4_s u3S v1')
            v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)).2.2.2.2.1).2.2.1 v1')
    (hcarry2 : Carry2NzAll v0' v1' v2' v3') :
    cpsTripleWithin 672 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jMem (2 : Word) shift u0S v10_val v11Old antiShift
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word)
        u1S u0S (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV4NoX1 bltu_2 bltu_1 bltu_0 sp base
        v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
        retMem dMem dloMem scratch_un0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;>
  (simp only at hbltu_0 hbltu_1 hbltu_2;
   exact divK_loop_n2_unified_from_source_exact_loopIterScratch_v4_noNop
     _ _ _ sp base
     jMem (2 : Word) shift u0S v10_val v11Old antiShift
     v0' v1' v2' v3' u2S u3S u4_s (0 : Word) (0 : Word) u1S u0S
     (0 : Word) (0 : Word) (0 : Word) raVal
     retMem dMem dloMem scratch_un0 scratchMem
     halign hbltu_2 hbltu_1 hbltu_0 hcarry2)

/-- Handoff from the n=2 preloop postcondition to the v4 no-`x1` loop source,
    preserving caller-owned `x1` and the v4 div128 scratch cell. -/
theorem loopSetupPost_to_loopN2PreWithScratchV4NoX1_framed
    (sp : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v11Old : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    ∀ h,
      (loopSetupPost sp (2 : Word) (clzResult b1).1 a0 a1 a2 a3 b0 b1 b2 b3 **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) h →
      (((loopN2PreWithScratchV4NoX1 sp
        jMem (2 : Word) (fullDivN2Shift b1)
        (fullDivN2NormU a0 a1 a2 a3 b1).1
        (a0 >>> ((fullDivN2AntiShift b1).toNat % 64)) v11Old (fullDivN2AntiShift b1)
        (fullDivN2NormV b0 b1 b2 b3).1
        (fullDivN2NormV b0 b1 b2 b3).2.1
        (fullDivN2NormV b0 b1 b2 b3).2.2.1
        (fullDivN2NormV b0 b1 b2 b3).2.2.2
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
        (0 : Word)
        (0 : Word)
        (fullDivN2NormU a0 a1 a2 a3 b1).2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).1
        (0 : Word) (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h) := by
  intro h hp
  delta loopN2PreWithScratchV4NoX1 loopN2PreWithScratchNoX1 loopN2Pre at ⊢
  delta loopSetupPost fullDivN2NormV fullDivN2NormU fullDivN2Shift fullDivN2AntiShift at hp ⊢
  simp only [x1_val_n2] at hp
  simp only [n2_ub2_off0, n2_ub2_off4088, n2_ub2_off4080,
             n2_ub2_off4072, n2_ub2_off4064,
             n3_ub1_off0, n3_ub0_off0,
             n2_qa2, n3_qa1, n3_qa0,
             se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
