/-
  Extract mid: walk_init a2=0 arm → BNE not-taken → save s5/s6
  LinkWalkInit (E+148) → AfterSaveCursor (E+160).

  Residual: reshape extractWalkInitPost 9-way → a2=0 OK arm
  under extractSuccess (StrictListPayload pure bridge).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInit

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

/-- Temps + ra + bytes after walk_init (no x0 — BNE leaf owns x0). -/
def walkInitRest (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion txBase txBytes

private theorem walkInitRest_pcFree (txBase : Word) (txBytes : List (BitVec 8)) :
    (walkInitRest txBase txBytes).pcFree := by
  unfold walkInitRest; pcf

/-- After BNE+save: cursor in s5/s6, a2 still 0. -/
def extractAfterSavePost (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  walkInitAmbient txBase lenW typeW innerW **
    walkInitRest txBase txBytes **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

set_option maxRecDepth 8000 in
/-- BNE not-taken (a2=0) framed with ambient + rest + a0/a1. -/
theorem extractWalkInitBneOk_framed
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkInit AfterWalkInitOk extractLinkedCode
      (walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := extractWalkInitBneOk
  have hF := cpsTripleWithin_frameR
    (walkInitAmbient txBase lenW typeW innerW **
      walkInitRest txBase txBytes **
        (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr))
    (by pcf) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- Save cursor framed (peels s5/s6). Leaf owns a0/a1; do not re-frame them. -/
theorem extractSaveCursor_framed
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) AfterWalkInitOk AfterSaveCursor extractLinkedCode
      (walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22)
      (walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x22)
      (P := walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21)
      (fun s6Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x21)
      (P := walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x22 ↦ᵣ s6Old))
      (fun s5Old => ?_))
  have hs := extractSaveCursor cursor endPtr s5Old s6Old
  have hF := cpsTripleWithin_frameR
    (walkInitAmbient txBase lenW typeW innerW **
      walkInitRest txBase txBytes **
        (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)))
    (by pcf) hs
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- a2=0 concrete: BNE + save → AfterSaveCursor under framed ambient. -/
theorem extractWalkInitBneSave
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22)
      (extractAfterSavePost txBase lenW typeW innerW cursor endPtr txBytes) := by
  have hbne := extractWalkInitBneOk_framed txBase lenW typeW innerW cursor endPtr txBytes
  have hbne' : cpsTripleWithin 1 LinkWalkInit AfterWalkInitOk extractLinkedCode
      (walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22)
      (walkInitAmbient txBase lenW typeW innerW **
        walkInitRest txBase txBytes **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22) := by
    have hF := cpsTripleWithin_frameR (regOwn .x21 ** regOwn .x22) (by pcf) hbne
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have hsave := extractSaveCursor_framed txBase lenW typeW innerW cursor endPtr txBytes
  have hseq := cpsTripleWithin_seq_same_cr hbne' hsave
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [extractAfterSavePost] at hq ⊢
      xperm_hyp hq) hseq

#print axioms extractWalkInitBneOk_framed
#print axioms extractSaveCursor_framed
#print axioms extractWalkInitBneSave

end EvmAsm.Codegen.TxExtractToAddressSpec
