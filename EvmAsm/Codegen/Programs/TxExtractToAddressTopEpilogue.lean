/-
  Extract mid: epilogue under extractLinkedCode + ambient frame.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressEpilogue
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn teaScratchOwn)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact bytesRegion_pcFree _ _)

set_option maxRecDepth 8000 in
/-- Success epilogue under `extractLinkedCode`. -/
theorem extractEpilogueSuccess_linked (sp0 spC : Word) (s cur : ExtractSaved)
    (a0v : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 11 EpiRestore s.ra extractLinkedCode
      ((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ spC) **
        regsAt extractFrame (extractSavedVals cur) **
        frameSlotsSaved extractFrame spC (extractSavedVals s))
      ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        frameSlotsSaved extractFrame spC (extractSavedVals s)) :=
  cpsTripleWithin_extend_code extract_mono
    (extractEpilogueSuccess sp0 spC s cur a0v hspC hret)

/-- Ambient owned across epilogue (not in leaf). -/
def epiAmbient (txBase toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) (isCreVal : Word) : Assertion :=
  bytesRegion txBase txBytes **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ isCreVal) **
    teaScratchOwn **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

private theorem epiAmbient_pcFree (txBase toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) (isCreVal : Word) :
    (epiAmbient txBase toBuf isCreationPtr txBytes isCreVal).pcFree := by
  unfold epiAmbient extractToBufOwn teaScratchOwn; pcf

set_option maxRecDepth 8000 in
/-- Success epilogue framed with RO blob + scratch owns (a0 preserved). -/
theorem extractEpilogueSuccess_framed
    (sp0 spC : Word) (s cur : ExtractSaved) (a0v : Word)
    (txBase toBuf isCreationPtr isCreVal : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 11 EpiRestore s.ra extractLinkedCode
      (epiAmbient txBase toBuf isCreationPtr txBytes isCreVal **
        (.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ spC) **
        regsAt extractFrame (extractSavedVals cur) **
        frameSlotsSaved extractFrame spC (extractSavedVals s))
      (epiAmbient txBase toBuf isCreationPtr txBytes isCreVal **
        (.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        frameSlotsSaved extractFrame spC (extractSavedVals s)) := by
  have h := extractEpilogueSuccess_linked sp0 spC s cur a0v hspC hret
  have hF := cpsTripleWithin_frameR
    (epiAmbient txBase toBuf isCreationPtr txBytes isCreVal)
    (epiAmbient_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- After epilogue: convert isCreation memIs → memOwn for Assumed post. -/
theorem epiAmbient_isCre_to_memOwn
    (txBase toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) (isCreVal : Word) :
    ∀ h, (epiAmbient txBase toBuf isCreationPtr txBytes isCreVal) h →
      (bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        memOwn isCreationPtr **
        teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  simp only [epiAmbient] at hp
  obtain ⟨h1, h2, hd, hu, hbytes,
    h3, h4, hd2, hu2, hto,
    h5, h6, hd3, hu3, his,
    hrest⟩ := hp
  exact ⟨h1, h2, hd, hu, hbytes,
    h3, h4, hd2, hu2, hto,
    h5, h6, hd3, hu3, memIs_implies_memOwn _ his, hrest⟩

#print axioms extractEpilogueSuccess_linked
#print axioms extractEpilogueSuccess_framed
#print axioms epiAmbient_isCre_to_memOwn

end EvmAsm.Codegen.TxExtractToAddressSpec
