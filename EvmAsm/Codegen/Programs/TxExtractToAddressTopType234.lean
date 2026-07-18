/-
  Extract mid: type234 branch + load a0/a1 from s5/s6
  AfterSaveCursor → WalkNext0JalPc under afterSaveFrameTy ambient.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextArgs
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeBranch

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

/-- Ambient after type234 branch at Type234Start (x5 = 1 after LI). -/
def type234StartFrame (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
    (.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))

private theorem type234StartFrame_pcFree
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    (type234StartFrame txBase lenW typeW innerW cursor endPtr txBytes).pcFree := by
  unfold type234StartFrame afterSaveFrameTy; pcf

set_option maxRecDepth 8000 in
/-- Frame `mv a0,s5; mv a1,s6` under type234 start ambient.
    a0/a1 already hold cursor/end after save, so MVs are identity. -/
theorem extractType234LoadArgs_framed
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) Type234Start WalkNext0JalPc extractLinkedCode
      (type234StartFrame txBase lenW typeW innerW cursor endPtr txBytes)
      (type234StartFrame txBase lenW typeW innerW cursor endPtr txBytes) := by
  -- Leaf atoms: x21,x22,x10,x11 (all cursor/end)
  have h := extractType234LoadArgs cursor endPtr cursor endPtr
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion txBase txBytes **
      (.x12 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [type234StartFrame, afterSaveFrameTy] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [type234StartFrame, afterSaveFrameTy] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- AfterSave → WalkNext0JalPc for type∉{0,1}: branch + load args. -/
theorem extractType234ToWalkNext0
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8))
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1) :
    cpsTripleWithin ((1 + (1 + (1 + 1))) + (1 + 1))
      AfterSaveCursor WalkNext0JalPc extractLinkedCode
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (type234StartFrame txBase lenW typeW innerW cursor endPtr txBytes) := by
  have hb := extractTypeBranchType234_framed txBase lenW typeW innerW
    cursor endPtr txBytes hne0 hne1
  have hl := extractType234LoadArgs_framed txBase lenW typeW innerW
    cursor endPtr txBytes
  have hseq := cpsTripleWithin_seq_same_cr hb hl
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [type234StartFrame] at hq ⊢
    exact hq) hseq

#print axioms extractType234LoadArgs_framed
#print axioms extractType234ToWalkNext0

end EvmAsm.Codegen.TxExtractToAddressSpec
