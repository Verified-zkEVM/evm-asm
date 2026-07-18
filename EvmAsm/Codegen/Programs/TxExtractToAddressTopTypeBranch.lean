/-
  Extract mid: type-branch under after-save ambient
  AfterSaveCursor (E+160) → LegacyStart / T1Start / Type234Start.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeBranch
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitOk

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

/-- Ambient after save excluding leaf atoms x5/x0/x20. -/
def afterSaveFrame (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion txBase txBytes **
    (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

/-- Frame for non-zero typeW (tea holds typeW). -/
def afterSaveFrameTy (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion txBase txBytes **
    (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

private theorem afterSaveFrame_pcFree (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    (afterSaveFrame txBase lenW innerW cursor endPtr txBytes).pcFree := by
  unfold afterSaveFrame; pcf

private theorem afterSaveFrameTy_pcFree (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes).pcFree := by
  unfold afterSaveFrameTy; pcf

set_option maxRecDepth 8000 in
/-- type=0 → LegacyStart under after-save ambient (peels x5). -/
theorem extractTypeBranchLegacy_framed
    (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) AfterSaveCursor LegacyStart extractLinkedCode
      (afterSaveFrame txBase lenW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (afterSaveFrame txBase lenW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := afterSaveFrame txBase lenW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (fun t0Old => ?_))
  have h := extractTypeBranchLegacy t0Old
  have hF := cpsTripleWithin_frameR
    (afterSaveFrame txBase lenW innerW cursor endPtr txBytes)
    (by pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- type=1 → T1Start under after-save ambient (peels x5). -/
theorem extractTypeBranchT1_framed
    (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor T1Start extractLinkedCode
      (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (fun t0Old => ?_))
  have h := extractTypeBranchT1 t0Old
  have hF := cpsTripleWithin_frameR
    (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes)
    (by pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- type∉{0,1} → Type234Start under after-save ambient (peels x5). -/
theorem extractTypeBranchType234_framed
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8))
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor Type234Start extractLinkedCode
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** (.x0 ↦ᵣ (0 : Word)))
      (fun t0Old => ?_))
  have h := extractTypeBranchType234 typeW t0Old hne0 hne1
  have hF := cpsTripleWithin_frameR
    (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes)
    (by pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractTypeBranchLegacy_framed
#print axioms extractTypeBranchT1_framed
#print axioms extractTypeBranchType234_framed

end EvmAsm.Codegen.TxExtractToAddressSpec
