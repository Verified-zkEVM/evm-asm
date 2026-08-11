/-
  Branch arm: path remaining + ADD path cursor (#11799).

  At `branchEntryPc` (idx 54) after kind=0 dispatch:
    BEQ x22, x19  → value path if path exhausted
    ADD x5, x18, x22  → path cursor (first hop: x22=0 from kindCallFrame)

  Path x18/x19 concrete from kind-post preserve.
  x22/x23/x24 live in `kindCallFrame` inside `dispatchAmb`.
-/

import EvmAsm.Codegen.Programs.MptWalkKindDispatch
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec

private theorem branch_value_beq_target :
    pc 54 + signExtend13 (228 : BitVec 13) = pc 111 := by
  unfold pc walkB signExtend13; decide

/-- Non-focus for BEQ x22,x19. Matches `dispatchState` atoms minus x22/x19. -/
private def pathBeqFrame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr valOutPtr valOutLen : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  walkSavedFrame newSp ws **
  (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW)

private theorem pathBeqFrame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr valOutPtr valOutLen : Word) :
    (pathBeqFrame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathPtr valOutPtr valOutLen).pcFree := by
  unfold pathBeqFrame kindSavedRegTail walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact pcFree_frameSlotsSaved _ _ _ | apply pcFree_sepConj

/-! Path remaining: BEQ x22,x19 ntaken when pathPos(0) ≠ pathLen. -/
set_option maxRecDepth 8000 in
theorem branch_path_remaining
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (hne : (0 : Word) ≠ pathLenW) :
    cpsTripleWithin 1 (pc 54) (pc 55) fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 0 countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen)
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 0 countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen) := by
  have hbeq := beq_spec_gen_within .x22 .x19 (228 : BitVec 13)
    (0 : Word) pathLenW (pc 54)
  rw [show pc 54 + 4 = pc 55 from pc_succ 54, branch_value_beq_target] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (walkMem (pc 54) 54 (.BEQ .x22 .x19 (228 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) (by rfl)) hbeq
  have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hne ((sepConj_pure_right _).1 hQ).2)
  have hF := pathBeqFrame_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr valOutPtr valOutLen
  have hntF := cpsTripleWithin_frameR
    (pathBeqFrame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW pathPtr valOutPtr valOutLen)
    hF hnt
  refine cpsTripleWithin_weaken ?_ ?_ hntF
  · intro h hp
    -- Goal: (x22↦0 ** x19↦pathLen ** pathBeqFrame)
    -- From: dispatchStateOwnX5
    simp only [dispatchStateOwnX5, dispatchState, dispatchTemps, dispatchAmb,
      kindCallFrame, pathBeqFrame, kindSavedRegTail, kindPayload] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateOwnX5, dispatchState, dispatchTemps, dispatchAmb,
      kindCallFrame, pathBeqFrame, kindSavedRegTail, kindPayload] at hq ⊢
    xperm_chunked hq

/-- Frame for ADD (everything except x5/x18/x22). -/
private def pathAddFrame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathLenW valOutPtr valOutLen : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x19 ↦ᵣ pathLenW) ** (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  walkSavedFrame newSp ws **
  (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW)

private theorem pathAddFrame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathLenW valOutPtr valOutLen : Word) :
    (pathAddFrame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathLenW valOutPtr valOutLen).pcFree := by
  unfold pathAddFrame kindSavedRegTail walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact pcFree_frameSlotsSaved _ _ _ | apply pcFree_sepConj

/-! ADD x5 = pathPtr + 0. Pre has regOwn x5; peel via of_forall. -/
set_option maxRecDepth 8000 in
theorem branch_path_add
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word) :
    cpsTripleWithin 1 (pc 55) (pc 56) fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 0 countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 0 countW offW lenW
        (pathPtr + (0 : Word)) pathPtr pathLenW valOutPtr valOutLen) := by
  let F := pathAddFrame newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathLenW valOutPtr valOutLen
  have hF : F.pcFree :=
    pathAddFrame_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW pathLenW valOutPtr valOutLen
  -- ADD pre: (rs1↦v1 ** rs2↦v2 ** rd↦vOld) = (x18 ** x22 ** x5)
  have hcore : ∀ v5,
      cpsTripleWithin 1 (pc 55) (pc 56) fullCode
        (((.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5)) ** F)
        (((.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ (pathPtr + (0 : Word)))) ** F) := by
    intro v5
    have hadd := add_spec_gen_within .x5 .x18 .x22 pathPtr (0 : Word) v5 (pc 55)
      (by decide)
    have hadde := cpsTripleWithin_extend_code
      (walkMem (pc 55) 55 (.ADD .x5 .x18 .x22)
        (by decide) (by unfold pc walkB; decide) (by rfl)) hadd
    rw [pc_succ 55] at hadde
    have hFr := cpsTripleWithin_frameR F hF hadde
    refine cpsTripleWithin_weaken ?_ ?_ hFr
    · intro h hp; xperm_chunked hp
    · intro h hq; xperm_chunked hq
  -- of_forall wants (P ** r↦) with r rightmost
  have hpeel :
      cpsTripleWithin 1 (pc 55) (pc 56) fullCode
        ((((.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ (0 : Word))) ** F) ** regOwn .x5)
        (((.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ (pathPtr + (0 : Word)))) ** F) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) ?_
    intro v5
    refine cpsTripleWithin_weaken ?_ ?_ (hcore v5)
    · intro h hp; xperm_chunked hp
    · intro h hq; exact hq
  refine cpsTripleWithin_weaken ?_ ?_ hpeel
  · intro h hp
    simp only [dispatchStateOwnX5, dispatchState, dispatchTemps, dispatchAmb,
      kindCallFrame, F, pathAddFrame, kindSavedRegTail, kindPayload] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateX5, dispatchState, dispatchTemps, dispatchAmb,
      kindCallFrame, F, pathAddFrame, kindSavedRegTail, kindPayload] at hq ⊢
    xperm_chunked hq

/-! ## Path LBU nibble (idx 56)

    After ADD, x5 = pathPtr + 0. LBU x6, 0(x5) loads pathBytes[0].
    Path ambient is framed through (not in dispatchState — walk ABI). -/

/-- Post-ADD state plus path bytes. -/
def branchAfterAdd (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) : Assertion :=
  dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen 0 countW offW lenW
    (pathPtr + (0 : Word)) pathPtr pathLenW valOutPtr valOutLen **
  bytesRegion pathPtr pathBytes

/-- After LBU: x6 = nibble byte, path intact. -/
def branchAfterLbu (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibble : BitVec 8) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  (.x6 ↦ᵣ nibble.zeroExtend 64) **
  regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  dispatchAmb newSp ws ks nodeBase nodeLenW **
  bytesRegion pathPtr pathBytes

/-- Frame for LBU (everything except x5/x6 + path region). -/
private def pathLbuFrame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  walkSavedFrame newSp ws **
  (.x22 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW)

private theorem pathLbuFrame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word) :
    (pathLbuFrame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathPtr pathLenW valOutPtr valOutLen).pcFree := by
  unfold pathLbuFrame kindSavedRegTail walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact pcFree_frameSlotsSaved _ _ _ | apply pcFree_sepConj

private theorem pathPtr_add_zero (pathPtr : Word) :
    pathPtr + (0 : Word) = pathPtr + BitVec.ofNat 64 0 := by
  simp [BitVec.ofNat]

/-! LBU path nibble at first hop (pathPos = 0). -/
set_option maxRecDepth 8000 in
theorem branch_path_lbu
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8))
    (hpathAlign : pathPtr.toNat % 8 = 0)
    (hpath0 : 0 < pathBytes.length)
    (hover : pathPtr.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess (pathPtr + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 1 (pc 56) (pc 57) fullCode
      (branchAfterAdd newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes)
      (branchAfterLbu newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes
        (pathBytes[0]'hpath0)) := by
  let F := pathLbuFrame newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
  have hF : F.pcFree :=
    pathLbuFrame_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
  -- Peel own x6 for LBU dest
  have hcore : ∀ v6,
      cpsTripleWithin 1 (pc 56) (pc 57) fullCode
        (((.x5 ↦ᵣ (pathPtr + BitVec.ofNat 64 0)) ** (.x6 ↦ᵣ v6) **
          bytesRegion pathPtr pathBytes) ** F)
        (((.x5 ↦ᵣ (pathPtr + BitVec.ofNat 64 0)) **
          (.x6 ↦ᵣ ((pathBytes[0]'hpath0).zeroExtend 64)) **
          bytesRegion pathPtr pathBytes) ** F) := by
    intro v6
    have hlbu := bytesRegion_lbu_within .x6 .x5 pathPtr v6 (pc 56) pathBytes 0
      (by decide) hpathAlign hpath0 hover hvalid
    have hlbue := cpsTripleWithin_extend_code
      (walkMem (pc 56) 56 (.LBU .x6 .x5 (0 : BitVec 12))
        (by decide) (by unfold pc walkB; decide) (by rfl)) hlbu
    rw [pc_succ 56] at hlbue
    have hFr := cpsTripleWithin_frameR F hF hlbue
    refine cpsTripleWithin_weaken ?_ ?_ hFr
    · intro h hp; xperm_chunked hp
    · intro h hq; xperm_chunked hq
  have hpeel :
      cpsTripleWithin 1 (pc 56) (pc 57) fullCode
        (((.x5 ↦ᵣ (pathPtr + BitVec.ofNat 64 0)) ** bytesRegion pathPtr pathBytes ** F) **
          regOwn .x6)
        (((.x5 ↦ᵣ (pathPtr + BitVec.ofNat 64 0)) **
          (.x6 ↦ᵣ ((pathBytes[0]'hpath0).zeroExtend 64)) **
          bytesRegion pathPtr pathBytes) ** F) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6) ?_
    intro v6
    refine cpsTripleWithin_weaken ?_ ?_ (hcore v6)
    · intro h hp; xperm_chunked hp
    · intro h hq; exact hq
  -- Bridge pathPtr+0 ↔ pathPtr+ofNat 0
  have hptr : pathPtr + (0 : Word) = pathPtr + BitVec.ofNat 64 0 := pathPtr_add_zero pathPtr
  refine cpsTripleWithin_weaken ?_ ?_ hpeel
  · intro h hp
    simp only [branchAfterAdd, dispatchStateX5, dispatchState, dispatchTemps,
      dispatchAmb, kindCallFrame, F, pathLbuFrame, kindSavedRegTail, kindPayload] at hp ⊢
    rw [hptr] at hp
    xperm_chunked hp
  · intro h hq
    simp only [branchAfterLbu, dispatchAmb, kindCallFrame, F, pathLbuFrame,
      kindSavedRegTail, kindPayload] at hq ⊢
    rw [← hptr] at hq
    xperm_chunked hq

/-! ## Nth-child setup MVs (idx 57-59)

    MV x10,x23; MV x11,x24; MV x12,x6  → ABI for rlp_list_nth_item. -/

/-- After three MVs: a0=node, a1=len, a2=nibbleW. -/
def branchNthSetup (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ nibbleW) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  (.x6 ↦ᵣ nibbleW) **
  regOwn .x7 **
  regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  dispatchAmb newSp ws ks nodeBase nodeLenW **
  bytesRegion pathPtr pathBytes

/-- Non-focus for MV x10,x23 (omits x10+x23). -/
private def mv10Frame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  (.x6 ↦ᵣ nibbleW) **
  regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  walkSavedFrame newSp ws **
  (.x22 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ nodeLenW) **
  bytesRegion pathPtr pathBytes

private theorem mv10Frame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) :
    (mv10Frame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW).pcFree := by
  unfold mv10Frame kindSavedRegTail walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact pcFree_frameSlotsSaved _ _ _ | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-- Non-focus for MV x11,x24 (omits x11+x24; x10 already nodeBase). -/
private def mv11Frame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ nodeBase) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  (.x6 ↦ᵣ nibbleW) **
  regOwn .x7 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  walkSavedFrame newSp ws **
  (.x22 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ nodeBase) **
  bytesRegion pathPtr pathBytes

private theorem mv11Frame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) :
    (mv11Frame newSp ws ks nodeBase bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW).pcFree := by
  unfold mv11Frame kindSavedRegTail walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact pcFree_frameSlotsSaved _ _ _ | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-- Non-focus for MV x12,x6 (omits x12+x6; x10/x11 set). -/
private def mv12Frame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  regOwn .x7 **
  regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  walkSavedFrame newSp ws **
  (.x22 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) **
  bytesRegion pathPtr pathBytes

private theorem mv12Frame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) :
    (mv12Frame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW
      pathPtr pathLenW valOutPtr valOutLen pathBytes).pcFree := by
  unfold mv12Frame kindSavedRegTail walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact pcFree_frameSlotsSaved _ _ _ | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-! Mid-state after MV x10 only. -/
private def afterMv10 (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ nodeBase) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  (.x6 ↦ᵣ nibbleW) **
  regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  dispatchAmb newSp ws ks nodeBase nodeLenW **
  bytesRegion pathPtr pathBytes

/-! Mid-state after MV x10+x11. -/
private def afterMv11 (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (pathPtr + (0 : Word))) **
  (.x6 ↦ᵣ nibbleW) **
  regOwn .x7 **
  regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) **
  (.x20 ↦ᵣ valOutPtr) ** (.x21 ↦ᵣ valOutLen) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    0 countW offW lenW **
  dispatchAmb newSp ws ks nodeBase nodeLenW **
  bytesRegion pathPtr pathBytes

set_option maxRecDepth 8000 in
theorem branch_nth_mv10
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibble : BitVec 8) :
    cpsTripleWithin 1 (pc 57) (pc 58) fullCode
      (branchAfterLbu newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibble)
      (afterMv10 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes
        (nibble.zeroExtend 64)) := by
  let nibbleW := nibble.zeroExtend 64
  let F := mv10Frame newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
    pathBytes nibbleW
  have hF : F.pcFree :=
    mv10Frame_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
      pathBytes nibbleW
  have hmv := mv_spec_gen_within .x10 .x23 nodeBase (BitVec.ofNat 64 0) (pc 57)
    (by decide)
  have hmve := cpsTripleWithin_extend_code
    (walkMem (pc 57) 57 (.MV .x10 .x23)
      (by decide) (by unfold pc walkB; decide) (by rfl)) hmv
  rw [pc_succ 57] at hmve
  have hFr := cpsTripleWithin_frameR F hF hmve
  refine cpsTripleWithin_weaken ?_ ?_ hFr
  · intro h hp
    simp only [branchAfterLbu, dispatchAmb, kindCallFrame, F, mv10Frame,
      kindSavedRegTail, kindPayload] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [afterMv10, dispatchAmb, kindCallFrame, F, mv10Frame,
      kindSavedRegTail, kindPayload] at hq ⊢
    xperm_chunked hq

set_option maxRecDepth 8000 in
theorem branch_nth_mv11
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) :
    cpsTripleWithin 1 (pc 58) (pc 59) fullCode
      (afterMv10 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW)
      (afterMv11 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW) := by
  let F := mv11Frame newSp ws ks nodeBase bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
    pathBytes nibbleW
  have hF : F.pcFree :=
    mv11Frame_pcFree newSp ws ks nodeBase bytes listLen
      oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
      pathBytes nibbleW
  -- peel own x11
  have hcore : ∀ v11,
      cpsTripleWithin 1 (pc 58) (pc 59) fullCode
        (((.x11 ↦ᵣ v11) ** (.x24 ↦ᵣ nodeLenW)) ** F)
        (((.x11 ↦ᵣ nodeLenW) ** (.x24 ↦ᵣ nodeLenW)) ** F) := by
    intro v11
    have hmv := mv_spec_gen_within .x11 .x24 nodeLenW v11 (pc 58) (by decide)
    have hmve := cpsTripleWithin_extend_code
      (walkMem (pc 58) 58 (.MV .x11 .x24)
        (by decide) (by unfold pc walkB; decide) (by rfl)) hmv
    rw [pc_succ 58] at hmve
    have hFr := cpsTripleWithin_frameR F hF hmve
    refine cpsTripleWithin_weaken ?_ ?_ hFr
    · intro h hp; xperm_chunked hp
    · intro h hq; xperm_chunked hq
  have hpeel :
      cpsTripleWithin 1 (pc 58) (pc 59) fullCode
        (((.x24 ↦ᵣ nodeLenW) ** F) ** regOwn .x11)
        (((.x11 ↦ᵣ nodeLenW) ** (.x24 ↦ᵣ nodeLenW)) ** F) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11) ?_
    intro v11
    refine cpsTripleWithin_weaken ?_ ?_ (hcore v11)
    · intro h hp; xperm_chunked hp
    · intro h hq; exact hq
  refine cpsTripleWithin_weaken ?_ ?_ hpeel
  · intro h hp
    simp only [afterMv10, dispatchAmb, kindCallFrame, F, mv11Frame,
      kindSavedRegTail, kindPayload] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [afterMv11, dispatchAmb, kindCallFrame, F, mv11Frame,
      kindSavedRegTail, kindPayload] at hq ⊢
    xperm_chunked hq

set_option maxRecDepth 8000 in
theorem branch_nth_mv12
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8)) (nibbleW : Word) :
    cpsTripleWithin 1 (pc 59) (pc 60) fullCode
      (afterMv11 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW)
      (branchNthSetup newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes nibbleW) := by
  let F := mv12Frame newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
    pathBytes
  have hF : F.pcFree :=
    mv12Frame_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
      pathBytes
  have hcore : ∀ v12,
      cpsTripleWithin 1 (pc 59) (pc 60) fullCode
        (((.x12 ↦ᵣ v12) ** (.x6 ↦ᵣ nibbleW)) ** F)
        (((.x12 ↦ᵣ nibbleW) ** (.x6 ↦ᵣ nibbleW)) ** F) := by
    intro v12
    have hmv := mv_spec_gen_within .x12 .x6 nibbleW v12 (pc 59) (by decide)
    have hmve := cpsTripleWithin_extend_code
      (walkMem (pc 59) 59 (.MV .x12 .x6)
        (by decide) (by unfold pc walkB; decide) (by rfl)) hmv
    rw [pc_succ 59] at hmve
    have hFr := cpsTripleWithin_frameR F hF hmve
    refine cpsTripleWithin_weaken ?_ ?_ hFr
    · intro h hp; xperm_chunked hp
    · intro h hq; xperm_chunked hq
  have hpeel :
      cpsTripleWithin 1 (pc 59) (pc 60) fullCode
        (((.x6 ↦ᵣ nibbleW) ** F) ** regOwn .x12)
        (((.x12 ↦ᵣ nibbleW) ** (.x6 ↦ᵣ nibbleW)) ** F) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12) ?_
    intro v12
    refine cpsTripleWithin_weaken ?_ ?_ (hcore v12)
    · intro h hp; xperm_chunked hp
    · intro h hq; exact hq
  refine cpsTripleWithin_weaken ?_ ?_ hpeel
  · intro h hp
    simp only [afterMv11, dispatchAmb, kindCallFrame, F, mv12Frame,
      kindSavedRegTail, kindPayload] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [branchNthSetup, dispatchAmb, kindCallFrame, F, mv12Frame,
      kindSavedRegTail, kindPayload] at hq ⊢
    xperm_chunked hq

/-! Compose LBU + 3 MVs → nth ABI setup. -/
set_option maxRecDepth 8000 in
theorem branch_to_nth_setup
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW : Word)
    (pathPtr pathLenW valOutPtr valOutLen : Word)
    (pathBytes : List (BitVec 8))
    (hpathAlign : pathPtr.toNat % 8 = 0)
    (hpath0 : 0 < pathBytes.length)
    (hover : pathPtr.toNat + 0 < 2 ^ 64)
    (hvalid : isValidByteAccess (pathPtr + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin 4 (pc 56) (pc 60) fullCode
      (branchAfterAdd newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes)
      (branchNthSetup newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen countW offW lenW
        pathPtr pathLenW valOutPtr valOutLen pathBytes
        ((pathBytes[0]'hpath0).zeroExtend 64)) := by
  have h0 := branch_path_lbu newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
    pathBytes hpathAlign hpath0 hover hvalid
  have h1 := branch_nth_mv10 newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
    pathBytes (pathBytes[0]'hpath0)
  have h2 := branch_nth_mv11 newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
    pathBytes ((pathBytes[0]'hpath0).zeroExtend 64)
  have h3 := branch_nth_mv12 newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen countW offW lenW pathPtr pathLenW valOutPtr valOutLen
    pathBytes ((pathBytes[0]'hpath0).zeroExtend 64)
  have c01 := cpsTripleWithin_seq_same_cr h0 h1
  have c02 := cpsTripleWithin_seq_same_cr c01 h2
  exact cpsTripleWithin_seq_same_cr c02 h3

end EvmAsm.Codegen.MptWalkSpec
