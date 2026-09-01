/-
  Kind dispatch after `mpt_node_kind` returns into `mpt_walk` (#11799).

  After kind callWithin (milestone 1) returns at walk+192 (idx 48):
    BEQ a0, zero, +24  → branch entry idx 54  (kind 0)
    LI  t0, 1
    BEQ a0, t0, +300   → ext entry    idx 125 (kind 1)
    LI  t0, 2
    BEQ a0, t0, +672   → leaf entry   idx 220 (kind 2)
    JAL zero, +988     → fail entry   idx 300 (else)

  This file lands the four arm-entry triples. Kind post PRESERVES x18..x21
  (path ptr/len) as concrete values for hop arms.

  The first callWithin is at prog index 47 (`GuestAddrs.mpt_walk + 188`):
  `mpt_node_kind_spec_within` (#11964, `.proven`) starts at the kind JAL with
  ABI already set (`x10/x11` = node pointer/length).  The root
  `witness_lookup_by_hash` remains a SEPARATE residual; this module does not
  claim it.  The call adapter factors saved `ra` out of `regsAt kindFrame` so
  `callWithin_spec` does not duplicate x1, and the kind post preserves the path
  registers x18..x21 as concrete values for the hop arms.
-/

import EvmAsm.Codegen.Programs.MptWalkMachine
import EvmAsm.Codegen.Programs.MptNodeKindWrap
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec

private abbrev walkProg : List Instr := mptWalk_prog

theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = walkB + BitVec.ofNat 64 (4 * k))
    (hk : k < walkProg.length)
    (hins : walkProg[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i :=
  walkMem A k ins hk hA hins

private theorem kind_jal_target :
    kindCallPc + signExtend21 (jalOff GuestAddrs.mpt_node_kind
      (GuestAddrs.mpt_walk + 188)) = kindB := by
  unfold kindCallPc pc walkB kindB
  decide

private theorem kind_ret_even :
    ((kindCallPc + 4) &&& ~~~(1 : Word)) = kindCallPc + 4 := by
  unfold kindCallPc pc walkB; decide

/-- Fuel: 1 JAL + kind whole-routine. -/
def kindCallFuel (listLen : Nat) : Nat :=
  1 + (1 + kindFrame.length + bodyFuel listLen + kindFrame.length + 1 + 1)

/-- Kind frame regs without ra (x8, x9 only). -/
def kindSavedRegTail (ks : KindSaved) : Assertion :=
  (.x8 ↦ᵣ ks.s0) ** (.x9 ↦ᵣ ks.s1)

theorem regsAt_kindFrame_factor (ks : KindSaved) :
    regsAt kindFrame (kindSavedVals ks) =
      ((.x1 ↦ᵣ ks.ra) ** kindSavedRegTail ks) := by
  simp only [regsAt_kindFrame, kindSavedRegTail]

/-- Call entry rest: kind footprint without outer x1. -/
def kindCallEntryRest (newSp : Word) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsOwn kindFrame (newSp + signExtend12 (-32 : BitVec 12)) **
  kindCallerPre (newSp + signExtend12 (-32 : BitVec 12)) nodeBase nodeLenW
    bytes oldCount oldOff oldLen v12 v13 v14 v18 v19 v20 v21

/-- Call return: kind post without outer x1. Path x18..x21 preserved. -/
def kindCallReturnRest (newSp : Word) (ks : KindSaved)
    (nodeBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen v18 v19 v20 v21 : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  kindCallerPost (newSp + signExtend12 (-32 : BitVec 12)) nodeBase bytes
    listLen oldCount oldOff oldLen v18 v19 v20 v21

theorem kindCallEntryRest_pcFree (newSp : Word) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word) :
    (kindCallEntryRest newSp ks nodeBase nodeLenW bytes oldCount oldOff oldLen
      v12 v13 v14 v18 v19 v20 v21).pcFree := by
  unfold kindCallEntryRest kindSavedRegTail kindCallerPre countAmbient
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
    | exact bytesRegion_pcFree _ _ | exact pcFree_pure
    | apply pcFree_sepConj

/-- Walk-only state framed through the kind call. -/
def kindCallFrame (newSp : Word) (ws : WalkSaved)
    (nodeBase nodeLenW : Word) : Assertion :=
  walkSavedFrame newSp ws **
  (.x22 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW)

theorem kindCallFrame_pcFree (newSp : Word) (ws : WalkSaved)
    (nodeBase nodeLenW : Word) :
    (kindCallFrame newSp ws nodeBase nodeLenW).pcFree := by
  unfold kindCallFrame walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | apply pcFree_sepConj

/-! Milestone 1: `mpt_node_kind` callWithin at walk+188. -/
set_option maxRecDepth 8000 in
theorem mpt_walk_kind_callWithin
    (newSp : Word) (ws : WalkSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat)
    (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word)
    (raVal : Word)
    (hlistLenW : nodeLenW = BitVec.ofNat 64 listLen)
    (halign : nodeBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : nodeBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (nodeBase + BitVec.ofNat 64 k) = true)
    (hpath : PathByteOk bytes nodeBase listLen oldOff oldLen) :
    let ks : KindSaved := { ra := kindCallPc + 4, s0 := ws.s0, s1 := ws.s1 }
    cpsTripleWithin (kindCallFuel listLen) kindCallPc (kindCallPc + 4) fullCode
      (((.x1 ↦ᵣ raVal) **
        kindCallEntryRest newSp ks nodeBase nodeLenW bytes oldCount oldOff oldLen
          v12 v13 v14 v18 v19 v20 v21) **
        kindCallFrame newSp ws nodeBase nodeLenW)
      (((.x1 ↦ᵣ (kindCallPc + 4)) **
        kindCallReturnRest newSp ks nodeBase bytes listLen oldCount oldOff oldLen
          v18 v19 v20 v21) **
        kindCallFrame newSp ws nodeBase nodeLenW) := by
  intro ks
  have hcallee0 := mpt_node_kind_spec_within newSp (kindCallPc + 4)
    nodeBase nodeLenW ks bytes listLen oldCount oldOff oldLen
    v12 v13 v14 v18 v19 v20 v21
    (by rfl) kind_ret_even hlistLenW halign hslack hover hvalid hpath
  have hcallee := cpsTripleWithin_extend_code kindCalleeMem hcallee0
  -- Factor ra out of regsAt → callEntryRest / callReturnRest
  have hcallee' :
      cpsTripleWithin
        (1 + kindFrame.length + bodyFuel listLen + kindFrame.length + 1 + 1)
        kindB (kindCallPc + 4) fullCode
        (((.x1 ↦ᵣ (kindCallPc + 4)) **
          kindCallEntryRest newSp ks nodeBase nodeLenW bytes oldCount oldOff oldLen
            v12 v13 v14 v18 v19 v20 v21))
        (((.x1 ↦ᵣ (kindCallPc + 4)) **
          kindCallReturnRest newSp ks nodeBase bytes listLen oldCount oldOff oldLen
            v18 v19 v20 v21)) := by
    refine cpsTripleWithin_weaken ?_ ?_ hcallee
    · -- hpre: P' → P  (new entryRest ⇒ old regsAt form)
      intro h hp
      -- hp: x1 ** kindCallEntryRest; goal: x2 ** regsAt ** frame ** caller
      simp only [kindCallEntryRest, kindSavedRegTail] at hp
      -- hp: x1 ** x2 ** x8 ** x9 ** frame ** caller
      rw [regsAt_kindFrame_factor]
      -- goal: x2 ** (x1 ** tail) ** frame ** caller
      simp only [ks, kindSavedRegTail]
      xperm_hyp hp
    · -- hpost: Q → Q'  (old regsAt form ⇒ new returnRest)
      intro h hq
      -- hq: x2 ** regsAt ** frameSaved ** callerPost
      -- goal: x1 ** kindCallReturnRest
      simp only [kindCallReturnRest, kindSavedRegTail]
      rw [regsAt_kindFrame_factor] at hq
      simp only [ks, kindSavedRegTail] at hq
      xperm_hyp hq
  have hcall := callWithin_spec kindCallPc kindB raVal
    (jalOff GuestAddrs.mpt_node_kind (GuestAddrs.mpt_walk + 188))
    (1 + kindFrame.length + bodyFuel listLen + kindFrame.length + 1 + 1)
    kind_jal_target
    (mem_at 47
      (.JAL .x1 (jalOff GuestAddrs.mpt_node_kind (GuestAddrs.mpt_walk + 188)))
      kindCallPc (by unfold kindCallPc pc walkB; decide) (by decide) (by rfl))
    (kindCallEntryRest_pcFree newSp ks nodeBase nodeLenW bytes oldCount oldOff oldLen
      v12 v13 v14 v18 v19 v20 v21)
    hcallee'
  have hframed := cpsTripleWithin_frameR
    (kindCallFrame newSp ws nodeBase nodeLenW)
    (kindCallFrame_pcFree newSp ws nodeBase nodeLenW) hcall
  exact cpsTripleWithin_mono_nSteps (by unfold kindCallFuel; omega) hframed

def branchEntryPc : Word := pc 54
def extEntryPc : Word := pc 125
def leafEntryPc : Word := pc 220
def failEntryPc : Word := pc 300

private theorem branch_beq_target :
    pc 48 + signExtend13 (24 : BitVec 13) = branchEntryPc := by
  unfold pc walkB branchEntryPc signExtend13; decide

private theorem ext_beq_target :
    pc 50 + signExtend13 (300 : BitVec 13) = extEntryPc := by
  unfold pc walkB extEntryPc signExtend13; decide

private theorem leaf_beq_target :
    pc 52 + signExtend13 (672 : BitVec 13) = leafEntryPc := by
  unfold pc walkB leafEntryPc signExtend13; decide

private theorem fail_jal_target :
    pc 53 + signExtend21 (988 : BitVec 21) = failEntryPc := by
  unfold pc walkB failEntryPc signExtend21; decide

/-- Kind BSS + stack + pure Result. -/
def kindPayload (newSp nodeBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW : Word) : Assertion :=
  bytesRegion nodeBase bytes **
  (MnkCount ↦ₘ countW) ** (MnkPathOff ↦ₘ offW) ** (MnkPathLen ↦ₘ lenW) **
  stackFree newSp 8 **
  ⌜MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind⌝

theorem kindPayload_pcFree (newSp nodeBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW : Word) :
    (kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
      kind countW offW lenW).pcFree := by
  unfold kindPayload
  repeat' first
    | exact pcFree_memIs | exact pcFree_stackFree _ _
    | exact bytesRegion_pcFree _ _ | exact pcFree_pure | apply pcFree_sepConj

/-- Walk ambient through dispatch. -/
def dispatchAmb (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) **
  kindSavedRegTail ks **
  frameSlotsSaved kindFrame (newSp + signExtend12 (-32 : BitVec 12))
    (kindSavedVals ks) **
  kindCallFrame newSp ws nodeBase nodeLenW

theorem dispatchAmb_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) :
    (dispatchAmb newSp ws ks nodeBase nodeLenW).pcFree := by
  unfold dispatchAmb kindSavedRegTail kindCallFrame walkSavedFrame
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_frameSlotsSaved _ _ _ | apply pcFree_sepConj

/-- Dead temps owned after kind (x5 may be concrete after LI).
    Path x18..x21 PRESERVED concrete. -/
def dispatchTemps (x5part : Assertion) (v18 v19 v20 v21 : Word) : Assertion :=
  x5part **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem dispatchTemps_pcFree (x5part : Assertion) (hx5 : x5part.pcFree)
    (v18 v19 v20 v21 : Word) :
    (dispatchTemps x5part v18 v19 v20 v21).pcFree := by
  unfold dispatchTemps
  repeat' first
    | exact hx5 | exact pcFree_regOwn | exact pcFree_regIs | apply pcFree_sepConj

/-- Full dispatch state. -/
def dispatchState (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW : Word)
    (x5part : Assertion) (v18 v19 v20 v21 : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  (.x10 ↦ᵣ BitVec.ofNat 64 kind) ** (.x0 ↦ᵣ (0 : Word)) **
  dispatchTemps x5part v18 v19 v20 v21 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    kind countW offW lenW **
  dispatchAmb newSp ws ks nodeBase nodeLenW

def dispatchStateOwnX5 (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word) : Assertion :=
  dispatchState newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen kind countW offW lenW (regOwn .x5) v18 v19 v20 v21

def dispatchStateX5 (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW x5v v18 v19 v20 v21 : Word) : Assertion :=
  dispatchState newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen kind countW offW lenW (.x5 ↦ᵣ x5v) v18 v19 v20 v21

/-- Non-focus frame for BEQ x10,x0 (keeps own x5). -/
private def beq0Frame (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word) : Assertion :=
  (.x1 ↦ᵣ (kindCallPc + 4)) **
  dispatchTemps (regOwn .x5) v18 v19 v20 v21 **
  kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
    kind countW offW lenW **
  dispatchAmb newSp ws ks nodeBase nodeLenW

private theorem beq0Frame_pcFree (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word) :
    (beq0Frame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21).pcFree := by
  unfold beq0Frame
  have ht := dispatchTemps_pcFree (regOwn .x5) pcFree_regOwn v18 v19 v20 v21
  repeat' first
    | exact pcFree_regIs | exact ht
    | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
    | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj

/-! ## Branch: kind = 0, BEQ taken → branchEntryPc (1 step) -/

set_option maxRecDepth 8000 in
theorem kind_dispatch_branch
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW v18 v19 v20 v21 : Word)
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen 0) :
    cpsTripleWithin 1 (pc 48) branchEntryPc fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 0 countW offW lenW v18 v19 v20 v21)
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 0 countW offW lenW v18 v19 v20 v21) := by
  have hbeq := beq_spec_gen_within .x10 .x0 (24 : BitVec 13)
    (BitVec.ofNat 64 0) (0 : Word) (pc 48)
  rw [branch_beq_target, show pc 48 + 4 = pc 49 from pc_succ 48] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (mem_at 48 (.BEQ .x10 .x0 (24 : BitVec 13)) (pc 48)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hbeq
  have htk := cpsBranchWithin_takenStripPure2 hbeqe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hF := beq0Frame_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen 0 countW offW lenW v18 v19 v20 v21
  have htkF := cpsTripleWithin_frameR
    (beq0Frame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen 0 countW offW lenW v18 v19 v20 v21) hF htk
  refine cpsTripleWithin_weaken ?_ ?_ htkF
  · intro h hp
    simp only [dispatchStateOwnX5, dispatchState, beq0Frame, dispatchTemps] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateOwnX5, dispatchState, beq0Frame, dispatchTemps] at hq ⊢
    xperm_chunked hq

/-! ## Shared: BEQ x10,x0 ntaken when kind ≠ 0 -/

set_option maxRecDepth 8000 in
theorem kind_dispatch_beq0_ntaken
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word)
    (hne0 : BitVec.ofNat 64 kind ≠ (0 : Word))
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind) :
    cpsTripleWithin 1 (pc 48) (pc 49) fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21)
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21) := by
  have hbeq := beq_spec_gen_within .x10 .x0 (24 : BitVec 13)
    (BitVec.ofNat 64 kind) (0 : Word) (pc 48)
  rw [branch_beq_target, show pc 48 + 4 = pc 49 from pc_succ 48] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (mem_at 48 (.BEQ .x10 .x0 (24 : BitVec 13)) (pc 48)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hbeq
  have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hne0 ((sepConj_pure_right _).1 hQ).2)
  have hF := beq0Frame_pcFree newSp ws ks nodeBase nodeLenW bytes listLen
    oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21
  have hntF := cpsTripleWithin_frameR
    (beq0Frame newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21) hF hnt
  refine cpsTripleWithin_weaken ?_ ?_ hntF
  · intro h hp
    simp only [dispatchStateOwnX5, dispatchState, beq0Frame, dispatchTemps] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateOwnX5, dispatchState, beq0Frame, dispatchTemps] at hq ⊢
    xperm_chunked hq

/-! ## Concrete LI helpers -/

set_option maxRecDepth 8000 in
theorem kind_dispatch_li1_at_49
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word)
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind) :
    cpsTripleWithin 1 (pc 49) (pc 50) fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (1 : Word) v18 v19 v20 v21) := by
  let P : Assertion :=
    (.x1 ↦ᵣ (kindCallPc + 4)) **
    (.x10 ↦ᵣ BitVec.ofNat 64 kind) ** (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
      kind countW offW lenW **
    dispatchAmb newSp ws ks nodeBase nodeLenW
  have hP : P.pcFree := by
    unfold P
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
      | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj
  have hbody : ∀ vOld,
      cpsTripleWithin 1 (pc 49) (pc 50) fullCode
        (P ** (.x5 ↦ᵣ vOld)) (P ** (.x5 ↦ᵣ (1 : Word))) := by
    intro vOld
    have hli := li_spec_gen_within .x5 vOld (1 : Word) (pc 49) (by decide)
    have hlic := cpsTripleWithin_extend_code
      (mem_at 49 (.LI .x5 (1 : Word)) (pc 49)
        (by unfold pc walkB; decide) (by decide) (by rfl)) hli
    rw [pc_succ 49] at hlic
    have hfr := cpsTripleWithin_frameR P hP hlic
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hfr
  have hown := cpsTripleWithin_of_forall_regIs_to_regOwn hbody
  refine cpsTripleWithin_weaken ?_ ?_ hown
  · intro h hp
    simp only [dispatchStateOwnX5, dispatchState, dispatchTemps, P] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateX5, dispatchState, dispatchTemps, P] at hq ⊢
    xperm_chunked hq

set_option maxRecDepth 8000 in
theorem kind_dispatch_li2_at_51
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word)
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind) :
    cpsTripleWithin 1 (pc 51) (pc 52) fullCode
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (1 : Word) v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (2 : Word) v18 v19 v20 v21) := by
  let F : Assertion :=
    (.x1 ↦ᵣ (kindCallPc + 4)) **
    (.x10 ↦ᵣ BitVec.ofNat 64 kind) ** (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
      kind countW offW lenW **
    dispatchAmb newSp ws ks nodeBase nodeLenW
  have hF : F.pcFree := by
    unfold F
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
      | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj
  have hli := li_spec_gen_within .x5 (1 : Word) (2 : Word) (pc 51) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (mem_at 51 (.LI .x5 (2 : Word)) (pc 51)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hli
  rw [pc_succ 51] at hlic
  have hfr := cpsTripleWithin_frameR F hF hlic
  refine cpsTripleWithin_weaken ?_ ?_ hfr
  · intro h hp
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hq ⊢
    xperm_chunked hq

/-! ## BEQ x10,x5 taken/ntaken at pc 50 (off 300) and pc 52 (off 672) -/

set_option maxRecDepth 8000 in
theorem kind_dispatch_beq_ext_taken
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW v18 v19 v20 v21 : Word)
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen 1) :
    cpsTripleWithin 1 (pc 50) extEntryPc fullCode
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 1 countW offW lenW (1 : Word) v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 1 countW offW lenW (1 : Word) v18 v19 v20 v21) := by
  have hbeq := beq_spec_gen_within .x10 .x5 (300 : BitVec 13)
    (BitVec.ofNat 64 1) (1 : Word) (pc 50)
  rw [ext_beq_target, show pc 50 + 4 = pc 51 from pc_succ 50] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (mem_at 50 (.BEQ .x10 .x5 (300 : BitVec 13)) (pc 50)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hbeq
  have htk := cpsBranchWithin_takenStripPure2 hbeqe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  let F : Assertion :=
    (.x1 ↦ᵣ (kindCallPc + 4)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
      1 countW offW lenW **
    dispatchAmb newSp ws ks nodeBase nodeLenW
  have hF : F.pcFree := by
    unfold F
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
      | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj
  have htkF := cpsTripleWithin_frameR F hF htk
  refine cpsTripleWithin_weaken ?_ ?_ htkF
  · intro h hp
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hq ⊢
    xperm_chunked hq

set_option maxRecDepth 8000 in
theorem kind_dispatch_beq_ext_ntaken
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word)
    (hne1 : BitVec.ofNat 64 kind ≠ (1 : Word))
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind) :
    cpsTripleWithin 1 (pc 50) (pc 51) fullCode
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (1 : Word) v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (1 : Word) v18 v19 v20 v21) := by
  have hbeq := beq_spec_gen_within .x10 .x5 (300 : BitVec 13)
    (BitVec.ofNat 64 kind) (1 : Word) (pc 50)
  rw [ext_beq_target, show pc 50 + 4 = pc 51 from pc_succ 50] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (mem_at 50 (.BEQ .x10 .x5 (300 : BitVec 13)) (pc 50)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hbeq
  have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hne1 ((sepConj_pure_right _).1 hQ).2)
  let F : Assertion :=
    (.x1 ↦ᵣ (kindCallPc + 4)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
      kind countW offW lenW **
    dispatchAmb newSp ws ks nodeBase nodeLenW
  have hF : F.pcFree := by
    unfold F
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
      | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj
  have hntF := cpsTripleWithin_frameR F hF hnt
  refine cpsTripleWithin_weaken ?_ ?_ hntF
  · intro h hp
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hq ⊢
    xperm_chunked hq

set_option maxRecDepth 8000 in
theorem kind_dispatch_beq_leaf_taken
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW v18 v19 v20 v21 : Word)
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen 2) :
    cpsTripleWithin 1 (pc 52) leafEntryPc fullCode
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 2 countW offW lenW (2 : Word) v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 2 countW offW lenW (2 : Word) v18 v19 v20 v21) := by
  have hbeq := beq_spec_gen_within .x10 .x5 (672 : BitVec 13)
    (BitVec.ofNat 64 2) (2 : Word) (pc 52)
  rw [leaf_beq_target, show pc 52 + 4 = pc 53 from pc_succ 52] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (mem_at 52 (.BEQ .x10 .x5 (672 : BitVec 13)) (pc 52)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hbeq
  have htk := cpsBranchWithin_takenStripPure2 hbeqe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  let F : Assertion :=
    (.x1 ↦ᵣ (kindCallPc + 4)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
      2 countW offW lenW **
    dispatchAmb newSp ws ks nodeBase nodeLenW
  have hF : F.pcFree := by
    unfold F
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
      | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj
  have htkF := cpsTripleWithin_frameR F hF htk
  refine cpsTripleWithin_weaken ?_ ?_ htkF
  · intro h hp
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hq ⊢
    xperm_chunked hq

set_option maxRecDepth 8000 in
theorem kind_dispatch_beq_leaf_ntaken
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word)
    (hne2 : BitVec.ofNat 64 kind ≠ (2 : Word))
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind) :
    cpsTripleWithin 1 (pc 52) (pc 53) fullCode
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (2 : Word) v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (2 : Word) v18 v19 v20 v21) := by
  have hbeq := beq_spec_gen_within .x10 .x5 (672 : BitVec 13)
    (BitVec.ofNat 64 kind) (2 : Word) (pc 52)
  rw [leaf_beq_target, show pc 52 + 4 = pc 53 from pc_succ 52] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (mem_at 52 (.BEQ .x10 .x5 (672 : BitVec 13)) (pc 52)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hbeq
  have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hne2 ((sepConj_pure_right _).1 hQ).2)
  let F : Assertion :=
    (.x1 ↦ᵣ (kindCallPc + 4)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    kindPayload newSp nodeBase bytes listLen oldCount oldOff oldLen
      kind countW offW lenW **
    dispatchAmb newSp ws ks nodeBase nodeLenW
  have hF : F.pcFree := by
    unfold F
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
      | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj
  have hntF := cpsTripleWithin_frameR F hF hnt
  refine cpsTripleWithin_weaken ?_ ?_ hntF
  · intro h hp
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hp ⊢
    xperm_chunked hp
  · intro h hq
    simp only [dispatchStateX5, dispatchState, dispatchTemps, F] at hq ⊢
    xperm_chunked hq

/-! ## JAL fail at pc 53 -/

set_option maxRecDepth 8000 in
theorem kind_dispatch_jal_fail
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word)
    (_hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind) :
    cpsTripleWithin 1 (pc 53) failEntryPc fullCode
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (2 : Word) v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (2 : Word) v18 v19 v20 v21) := by
  have hjal := jal_x0_spec_gen_within (988 : BitVec 21) (pc 53)
  rw [fail_jal_target] at hjal
  have hjalc := cpsTripleWithin_extend_code
    (mem_at 53 (.JAL .x0 (988 : BitVec 21)) (pc 53)
      (by unfold pc walkB; decide) (by decide) (by rfl)) hjal
  let F : Assertion :=
    dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
      oldCount oldOff oldLen kind countW offW lenW (2 : Word) v18 v19 v20 v21
  have hF : F.pcFree := by
    unfold F dispatchStateX5 dispatchState dispatchTemps
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | exact kindPayload_pcFree _ _ _ _ _ _ _ _ _ _ _
      | exact dispatchAmb_pcFree _ _ _ _ _ | apply pcFree_sepConj
  have hfr := cpsTripleWithin_frameR F hF hjalc
  -- emp ** F → F
  exact cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hfr

/-! ## Composed arm paths -/

/-! Ext: beq0 ntaken + li1 + beq ext taken (3 steps). -/
set_option maxRecDepth 8000 in
theorem kind_dispatch_ext
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW v18 v19 v20 v21 : Word)
    (hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen 1) :
    cpsTripleWithin 3 (pc 48) extEntryPc fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 1 countW offW lenW v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 1 countW offW lenW (1 : Word) v18 v19 v20 v21) := by
  have hne0 : BitVec.ofNat 64 1 ≠ (0 : Word) := by decide
  have c0 := kind_dispatch_beq0_ntaken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen 1 countW offW lenW v18 v19 v20 v21 hne0 hres
  have c1 := kind_dispatch_li1_at_49 newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen 1 countW offW lenW v18 v19 v20 v21 hres
  have c2 := kind_dispatch_beq_ext_taken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen countW offW lenW v18 v19 v20 v21 hres
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c0 c1
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c01 c2
  exact cpsTripleWithin_mono_nSteps (by omega) c012

/-! Leaf: beq0 nt + li1 + beq ext nt + li2 + beq leaf tk (5 steps). -/
set_option maxRecDepth 8000 in
theorem kind_dispatch_leaf
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (countW offW lenW v18 v19 v20 v21 : Word)
    (hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen 2) :
    cpsTripleWithin 5 (pc 48) leafEntryPc fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 2 countW offW lenW v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen 2 countW offW lenW (2 : Word) v18 v19 v20 v21) := by
  have hne0 : BitVec.ofNat 64 2 ≠ (0 : Word) := by decide
  have hne1 : BitVec.ofNat 64 2 ≠ (1 : Word) := by decide
  have c0 := kind_dispatch_beq0_ntaken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen 2 countW offW lenW v18 v19 v20 v21 hne0 hres
  have c1 := kind_dispatch_li1_at_49 newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen 2 countW offW lenW v18 v19 v20 v21 hres
  have c2 := kind_dispatch_beq_ext_ntaken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen 2 countW offW lenW v18 v19 v20 v21 hne1 hres
  have c3 := kind_dispatch_li2_at_51 newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen 2 countW offW lenW v18 v19 v20 v21 hres
  have c4 := kind_dispatch_beq_leaf_taken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen countW offW lenW v18 v19 v20 v21 hres
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c0 c1
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c01 c2
  have c0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c012 c3
  have c01234 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c0123 c4
  exact cpsTripleWithin_mono_nSteps (by omega) c01234

/-! Fail: full fall-through to JAL fail (6 steps). -/
set_option maxRecDepth 8000 in
theorem kind_dispatch_fail
    (newSp : Word) (ws : WalkSaved) (ks : KindSaved)
    (nodeBase nodeLenW : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen : Word)
    (kind : Nat) (countW offW lenW v18 v19 v20 v21 : Word)
    (hne0 : BitVec.ofNat 64 kind ≠ (0 : Word))
    (hne1 : BitVec.ofNat 64 kind ≠ (1 : Word))
    (hne2 : BitVec.ofNat 64 kind ≠ (2 : Word))
    (hres : MptNodeKindResult bytes nodeBase listLen oldCount oldOff oldLen kind) :
    cpsTripleWithin 6 (pc 48) failEntryPc fullCode
      (dispatchStateOwnX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21)
      (dispatchStateX5 newSp ws ks nodeBase nodeLenW bytes listLen
        oldCount oldOff oldLen kind countW offW lenW (2 : Word) v18 v19 v20 v21) := by
  have c0 := kind_dispatch_beq0_ntaken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21 hne0 hres
  have c1 := kind_dispatch_li1_at_49 newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21 hres
  have c2 := kind_dispatch_beq_ext_ntaken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21 hne1 hres
  have c3 := kind_dispatch_li2_at_51 newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21 hres
  have c4 := kind_dispatch_beq_leaf_ntaken newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21 hne2 hres
  have c5 := kind_dispatch_jal_fail newSp ws ks nodeBase nodeLenW bytes
    listLen oldCount oldOff oldLen kind countW offW lenW v18 v19 v20 v21 hres
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c0 c1
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c01 c2
  have c0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c012 c3
  have c01234 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c0123 c4
  have c012345 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c01234 c5
  exact cpsTripleWithin_mono_nSteps (by omega) c012345

end EvmAsm.Codegen.MptWalkSpec
