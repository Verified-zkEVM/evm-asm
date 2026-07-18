/-
  Extract front segment: prologue + pre-zero → AfterPreZero (E+72)
  under extractLinkedCode. Residual: type…HaveField…epilogue compose.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressPreZero
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn)

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

/-- Ambient framed across pre-zero (no x18/x19/x0 — leaf owns those). -/
def frontAfterPrologueAmbient (spC : Word) (s : ExtractSaved)
    (txBase txLenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
    (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (Reg.x23 ↦ᵣ s.s7) **
    frameSlotsSaved extractFrame spC (extractSavedVals s) **
    extractSpareSlot spC **
    (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) **
    (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
    (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
    (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

set_option maxRecDepth 8000 in
theorem extractPrologue_linked (sp0 spC : Word) (s : ExtractSaved)
    (txBase txLenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12)) :
    cpsTripleWithin 14 E (E + 56) extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase txLenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16)
      (prologuePost spC s txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16) :=
  cpsTripleWithin_extend_code extract_mono
    (extractPrologue sp0 spC s txBase txLenW toBuf isCreationPtr
      old5 old6 old7 old14 old15 old16 hspC)

set_option maxRecDepth 8000 in
theorem extractPreZero_linked
    (toBuf isCreationPtr : Word)
    (halign : toBuf.toNat % 8 = 0)
    (hover : toBuf.toNat + 16 < 2 ^ 64)
    (hvalid16 : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin 4 (E + 56) (E + 72) extractLinkedCode
      ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** extractToBufOwn toBuf ** memOwn isCreationPtr)
      ((.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x0 ↦ᵣ (0 : Word)) ** preZeroPost toBuf isCreationPtr) :=
  cpsTripleWithin_extend_code extract_mono
    (extractPreZero toBuf isCreationPtr halign hover hvalid16)

set_option maxRecDepth 8000 in
/-- Front: E → E+72 (prologue + pre-zero) under extractLinkedCode. -/
theorem extractFront
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase txLenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (halign : toBuf.toNat % 8 = 0)
    (hover : toBuf.toNat + 16 < 2 ^ 64)
    (hvalid16 : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin (14 + 4) E (E + 72) extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase txLenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr)
      (prologuePost spC s txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        preZeroPost toBuf isCreationPtr) := by
  have hP := extractPrologue_linked sp0 spC s txBase txLenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 hspC
  have hPF := cpsTripleWithin_frameR
    (extractToBufOwn toBuf ** memOwn isCreationPtr) (by pcf) hP
  have hP2 : cpsTripleWithin 14 E (E + 56) extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase txLenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr)
      (prologuePost spC s txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hPF
  have hZ := extractPreZero_linked toBuf isCreationPtr halign hover hvalid16
  have hZF := cpsTripleWithin_frameR
    (frontAfterPrologueAmbient spC s txBase txLenW toBuf isCreationPtr
      old5 old6 old7 old14 old15 old16) (by pcf) hZ
  have hZ2 : cpsTripleWithin 4 (E + 56) (E + 72) extractLinkedCode
      (prologuePost spC s txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr)
      (prologuePost spC s txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        preZeroPost toBuf isCreationPtr) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [prologuePost, prologueAbiRest, frontAfterPrologueAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [prologuePost, prologueAbiRest, frontAfterPrologueAmbient] at hq ⊢
      xperm_hyp hq) hZF
  exact cpsTripleWithin_seq_same_cr hP2 hZ2

#print axioms extractPrologue_linked
#print axioms extractPreZero_linked
#print axioms extractFront

end EvmAsm.Codegen.TxExtractToAddressSpec
