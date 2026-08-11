/-
  First `mpt_node_kind` callWithin from `mpt_walk` (#11799 milestone 1).

  Call site: prog idx 47 = `GuestAddrs.mpt_walk + 188`.
  Callee: `mpt_node_kind_spec_within` (#11964, `.proven`).
  Root `witness_lookup_by_hash` is SEPARATE residual — this lemma starts
  at the kind JAL with ABI already set (x10/x11 = node ptr/len).

  Pattern mirrors `RlpListCountItemsCallSAsm`: factor saved `ra` out of
  `regsAt kindFrame` so `callWithin_spec` does not duplicate x1.

  Kind post PRESERVES x18..x21 as concrete values (path ptr/len for hop
  arms). Guest restores them via count/nth save/restore.
-/

import EvmAsm.Codegen.Programs.MptWalkMachine
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

end EvmAsm.Codegen.MptWalkSpec
