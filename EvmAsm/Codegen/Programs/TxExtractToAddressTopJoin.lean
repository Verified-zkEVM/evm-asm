/-
  HaveField creation + stack ambient framing.
  Residual: reshape creation post → epi pre + stackFree (xperm atom count).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopHaveField
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

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

/-- Stack + spare framed across HaveField → epi. -/
def joinStackAmbient (spC : Word) (s : ExtractSaved) : Assertion :=
  (.x2 ↦ᵣ spC) **
    frameSlotsSaved extractFrame spC (extractSavedVals s) **
    extractSpareSlot spC

private theorem joinStackAmbient_pcFree (spC : Word) (s : ExtractSaved) :
    (joinStackAmbient spC s).pcFree := by
  unfold joinStackAmbient; pcf

/-- Live frame regs at HaveField for epilogue `regsAt cur`. -/
def joinCur (ra s0 s1 s2 s3 s4 s5 s6 s7 : Word) : ExtractSaved where
  ra := ra; s0 := s0; s1 := s1; s2 := s2; s3 := s3
  s4 := s4; s5 := s5; s6 := s6; s7 := s7

private theorem regsAt_joinCur (ra s0 s1 s2 s3 s4 s5 s6 s7 : Word) :
    regsAt extractFrame (extractSavedVals (joinCur ra s0 s1 s2 s3 s4 s5 s6 s7)) =
      ((.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7)) := by
  simp only [extractFrame, regsAt, extractSavedVals, joinCur, List.foldr_cons,
    List.foldr_nil, sepConj_emp_right']

set_option maxRecDepth 8000 in
/-- Creation HaveField + stack + live ra/s7 (for later epi join). -/
theorem extractHaveFieldCreation_stack
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr t2Old t0Old a0Old ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + (1 + (1 + (1 + 1))))) HaveField EpiRestore
      extractLinkedCode
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
  have h := extractHaveFieldCreation_framed txBase lenW typeW innerW toBuf
    contentPtr endPtr next isCreationPtr t2Old t0Old a0Old txBytes
  have hF := cpsTripleWithin_frameR
    (joinStackAmbient spC s ** (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7))
    (by pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractHaveFieldCreation_stack
#print axioms frameSlotsSaved_imp_stackFree10

end EvmAsm.Codegen.TxExtractToAddressSpec
