/-
  Shared declaration home for the n=2 v5/no-NOP loop dispatch and unified post.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboMMM
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCC
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCM

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

open EvmAsm.Rv64

/-- Branch-selected n=2 v5 loop iteration. -/
def loopN2IterSelectedV5 (bltu : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then
    iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else
    iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp] theorem loopN2IterSelectedV5_false
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV5 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopN2IterSelectedV5; simp

@[simp] theorem loopN2IterSelectedV5_true
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopN2IterSelectedV5; simp

/-- Selected-carry bundle for the n=2 v5 loop: the three carry facts picked out
    by the actual `bltu_2 × bltu_1 × bltu_0` path (call digits use the v5 direct
    double-addback carry2, max digits use `isAddbackCarry2NzN2Max`). -/
def loopN2SelectedCarryV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := loopN2IterSelectedV5 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := loopN2IterSelectedV5 bltu_1 v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  (if bltu_2 then
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) ∧
  (if bltu_1 then
    callAddbackCarry2NzV5 v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3
      u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) ∧
  (if bltu_0 then
    callAddbackCarry2NzV5 v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)

theorem loopN2SelectedCarryV5_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) :
    loopN2SelectedCarryV5 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 =
    (let r2 := loopN2IterSelectedV5 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
     let r1 := loopN2IterSelectedV5 bltu_1 v0 v1 v2 v3
       u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
     (if bltu_2 then
       callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      else
       isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) ∧
     (if bltu_1 then
       callAddbackCarry2NzV5 v0 v1 v2 v3
         u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
      else
       isAddbackCarry2NzN2Max v0 v1 v2 v3
         u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) ∧
     (if bltu_0 then
       callAddbackCarry2NzV5 v0 v1 v2 v3
         u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      else
       isAddbackCarry2NzN2Max v0 v1 v2 v3
         u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)) := by
  delta loopN2SelectedCarryV5; rfl

open EvmAsm.Rv64

/-- ccc (TTT). -/
theorem loopN2CallCallCallSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true true true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallCallCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallCallCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, r2CCCN2V5_eq, r1CCCN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- ccm (TTF). -/
theorem loopN2CallCallMaxSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true true false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallCallMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallCallMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, r2CCCN2V5_eq, r1CCCN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- cmc (TFT). -/
theorem loopN2CallMaxCallSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true false true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallMaxCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallMaxCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false,
    r2CCCN2V5_eq, r1TMMN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- cmm (TFF). -/
theorem loopN2CallMaxMaxSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true false false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallMaxMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallMaxMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false,
    r2CCCN2V5_eq, r1TMMN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mcc (FTT). -/
theorem loopN2MaxCallCallSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 false true true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxCallCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxCallCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, loopN2IterSelectedV5_true,
    r2MTTN2V5_eq, r1MTTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mcm (FTF). -/
theorem loopN2MaxCallMaxSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 false true false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxCallMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxCallMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, loopN2IterSelectedV5_true,
    r2MTTN2V5_eq, r1MTTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mmc (FFT). -/
theorem loopN2MaxMaxCallSourceConds_of_selectedCarryV5
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
    (hcarry : loopN2SelectedCarryV5 false false true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxMaxCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxMaxCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, r2MMTN2V5_eq, r1MMTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mmm (FFF). -/
theorem loopN2MaxMaxMaxSourceConds_of_selectedCarryV5
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
    (hcarry : loopN2SelectedCarryV5 false false false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxMaxMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxMaxMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, r2MMTN2V5_eq, r1MMTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

open EvmAsm.Rv64

/-- Unified n=2 v5 loop postcondition, selected by the bltu path. -/
def loopN2UnifiedPostV5NoX1 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  match bltu_2, bltu_1, bltu_0 with
  | true, true, true =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, true, false =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 r2.2.1)) **
      (sp + signExtend12 3936 ↦ₘ scratch1)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, false, true =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1TMMN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch2
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, false, false =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1TMMN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 u1)) **
      (sp + signExtend12 3936 ↦ₘ scratch2)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, true, true =>
    let r2 := r2MTTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MTTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, true, false =>
    let r2 := r2MTTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MTTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 r2.2.1)) **
      (sp + signExtend12 3936 ↦ₘ scratch1)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, false, true =>
    let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratchMem
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, false, false =>
    let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      (sp + signExtend12 3944 ↦ₘ scratchUn0) **
      (sp + signExtend12 3936 ↦ₘ scratchMem)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))

open EvmAsm.Rv64

/-- Selected-carry unified n=2 v5 loop source theorem. -/
theorem divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
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
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
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
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    cpsTripleWithin 702 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
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
    have hconds := loopN2MaxMaxMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxMaxMaxSourceFinalPostNoX1V5_unfold, r2MMTN2V5_eq, r1MMTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MMTN2V5_eq, r1MMTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_max_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem hconds)
  · -- FFT = MMC
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2MaxMaxCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxMaxCallSourceFinalPostNoX1V5_unfold, r2MMTN2V5_eq, r1MMTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MMTN2V5_eq, r1MMTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_max_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTF = MCM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : ¬BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2MaxCallMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxCallMaxSourceFinalPostNoX1V5_unfold, r2MTTN2V5_eq, r1MTTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MTTN2V5_eq, r1MTTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_call_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTT = MCC
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2MaxCallCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxCallCallSourceFinalPostNoX1V5_unfold, r2MTTN2V5_eq, r1MTTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MTTN2V5_eq, r1MTTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_call_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFF = TMM (call-max-max)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2CallMaxMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallMaxMaxSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1TMMN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1TMMN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_max_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFT = TMT (call-max-call)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2CallMaxCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallMaxCallSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1TMMN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1TMMN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_max_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTF = CCM (call-call-max)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : ¬BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2CallCallMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallCallMaxSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1CCCN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1CCCN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_call_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTT = CCC (all call)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
              v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2CallCallCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallCallCallSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1CCCN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1CCCN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_call_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)

end EvmAsm.Evm64
