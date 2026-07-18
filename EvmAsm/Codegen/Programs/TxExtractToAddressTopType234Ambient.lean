/-
  Ambient dual of type234 AfterSave → WalkNext0JalPc.
  Split bases: x8=loadPtr, bytesRegion regionBase/bs.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextArgs
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeBranch
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInitAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopType234

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

def type234StartFrameAmbient (loadPtr regionBase lenW typeW innerW
    cursor endPtr : Word) (bs : List (BitVec 8)) : Assertion :=
  afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
      cursor endPtr bs **
    (.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))

private theorem type234StartFrameAmbient_pcFree
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
      cursor endPtr bs).pcFree := by
  unfold type234StartFrameAmbient afterSaveFrameTyAmbient; pcf

set_option maxRecDepth 8000 in
theorem extractTypeBranchType234_framed_ambient
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8))
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor Type234Start extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** (.x0 ↦ᵣ (0 : Word)))
      (fun t0Old => ?_))
  have h := extractTypeBranchType234 typeW t0Old hne0 hne1
  have hF := cpsTripleWithin_frameR
    (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
      cursor endPtr bs)
    (by unfold afterSaveFrameTyAmbient; pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractType234LoadArgs_framed_ambient
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) Type234Start WalkNext0JalPc extractLinkedCode
      (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
        cursor endPtr bs)
      (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
        cursor endPtr bs) := by
  have h := extractType234LoadArgs cursor endPtr cursor endPtr
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion regionBase bs **
      (.x12 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [type234StartFrameAmbient, afterSaveFrameTyAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [type234StartFrameAmbient, afterSaveFrameTyAmbient] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractType234ToWalkNext0_ambient
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8))
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1) :
    cpsTripleWithin ((1 + (1 + (1 + 1))) + (1 + 1))
      AfterSaveCursor WalkNext0JalPc extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
        cursor endPtr bs) := by
  have hb := extractTypeBranchType234_framed_ambient loadPtr regionBase
    lenW typeW innerW cursor endPtr bs hne0 hne1
  have hl := extractType234LoadArgs_framed_ambient loadPtr regionBase
    lenW typeW innerW cursor endPtr bs
  have hseq := cpsTripleWithin_seq_same_cr hb hl
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [type234StartFrameAmbient] at hq ⊢
    exact hq) hseq

#print axioms extractType234ToWalkNext0_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
