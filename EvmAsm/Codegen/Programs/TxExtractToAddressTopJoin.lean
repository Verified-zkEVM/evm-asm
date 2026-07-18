/-
  HaveField creation + stack ambient + epilogue join.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopHaveField
import EvmAsm.Codegen.Programs.TxExtractToAddressTopEpilogue
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

theorem regsAt_joinCur (ra s0 s1 s2 s3 s4 s5 s6 s7 : Word) :
    regsAt extractFrame (extractSavedVals (joinCur ra s0 s1 s2 s3 s4 s5 s6 s7)) =
      ((.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7)) := by
  simp only [extractFrame, regsAt, extractSavedVals, joinCur, List.foldr_cons,
    List.foldr_nil, sepConj_emp_right']

set_option maxRecDepth 8000 in
/-- Creation HaveField + stack + live ra/s7. -/
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

/-- Non-frame rest after creation (owned across epi leaf). -/
def creationEpiRest (spC : Word) (txBase toBuf isCreationPtr typeW innerW next : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  extractSpareSlot spC **
    bytesRegion txBase txBytes **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x31 ↦ᵣ (next - (0 : Word)))

private theorem creationEpiRest_pcFree (spC : Word)
    (txBase toBuf isCreationPtr typeW innerW next : Word)
    (txBytes : List (BitVec 8)) :
    (creationEpiRest spC txBase toBuf isCreationPtr typeW innerW next
      txBytes).pcFree := by
  unfold creationEpiRest; pcf

/-- Flat post after creation (no nested composite defs). -/
private def creationFlatPost (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ contentPtr) ** (.x22 ↦ᵣ endPtr) ** (Reg.x23 ↦ᵣ s7) **
    frameSlotsSaved extractFrame spC (extractSavedVals s) **
    extractSpareSlot spC **
    bytesRegion txBase txBytes **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x31 ↦ᵣ (next - (0 : Word)))

/-- Step 1: creation+stack post → flat (all atoms). -/
private theorem creation_post_to_flat
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h,
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) h →
      creationFlatPost spC s txBase lenW typeW innerW toBuf contentPtr endPtr
        next isCreationPtr ra s7 txBytes h := by
  intro h hp
  simp only [haveFieldCreAmbient, joinStackAmbient, creationFlatPost] at hp ⊢
  xperm_hyp hp

/-- Step 2: flat → epi pre ** rest. -/
private theorem creation_flat_to_epiPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h,
      creationFlatPost spC s txBase lenW typeW innerW toBuf contentPtr endPtr
        next isCreationPtr ra s7 txBytes h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame
            (extractSavedVals
              (joinCur ra txBase lenW toBuf isCreationPtr typeW contentPtr endPtr
                s7)) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        creationEpiRest spC txBase toBuf isCreationPtr typeW innerW next
          txBytes) h := by
  intro h hp
  simp only [creationFlatPost, creationEpiRest] at hp ⊢
  rw [regsAt_joinCur]
  xperm_hyp hp

/-- Reshape creation+stack post → epi pre ** rest. -/
private theorem creation_post_to_epiPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h,
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame
            (extractSavedVals
              (joinCur ra txBase lenW toBuf isCreationPtr typeW contentPtr endPtr
                s7)) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        creationEpiRest spC txBase toBuf isCreationPtr typeW innerW next
          txBytes) h := by
  intro h hp
  exact creation_flat_to_epiPre spC s txBase lenW typeW innerW toBuf contentPtr
    endPtr next isCreationPtr ra s7 txBytes h
    (creation_post_to_flat spC s txBase lenW typeW innerW toBuf contentPtr
      endPtr next isCreationPtr ra s7 txBytes h hp)

set_option maxRecDepth 8000 in
/-- Creation: HaveField → ret; a0=0; stackFree restored. -/
theorem extractHaveFieldCreation_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr t2Old t0Old a0Old ra s7 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
      HaveField s.ra extractLinkedCode
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (1 : Word)) **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ (next - (0 : Word)))) := by
  let cur :=
    joinCur ra txBase lenW toBuf isCreationPtr typeW contentPtr endPtr s7
  have hHave := extractHaveFieldCreation_stack spC s txBase lenW typeW innerW
    toBuf contentPtr endPtr next isCreationPtr t2Old t0Old a0Old ra s7 txBytes
  have hHave2 :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (creation_post_to_epiPre spC s txBase lenW typeW innerW toBuf contentPtr
        endPtr next isCreationPtr ra s7 txBytes) hHave
  -- Align let-bound cur with joinCur in post
  have hHave3 : cpsTripleWithin (1 + (1 + (1 + (1 + (1 + 1))))) HaveField EpiRestore
      extractLinkedCode
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame (extractSavedVals cur) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        creationEpiRest spC txBase toBuf isCreationPtr typeW innerW next
          txBytes) := by
    simpa [cur] using hHave2
  have hEpi := extractEpilogueSuccess_linked sp0 spC s cur (0 : Word) hspC hret
  have hEpiF :=
    cpsTripleWithin_frameR
      (creationEpiRest spC txBase toBuf isCreationPtr typeW innerW next txBytes)
      (creationEpiRest_pcFree _ _ _ _ _ _ _ _) hEpi
  have hseq := cpsTripleWithin_seq_same_cr hHave3 hEpiF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun st hq => by
      have hq1 :
          (((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            frameSlotsSaved extractFrame spC (extractSavedVals s)) **
            creationEpiRest spC txBase toBuf isCreationPtr typeW innerW next
              txBytes) st := by
        xperm_hyp hq
      simp only [creationEpiRest] at hq1
      have hq2 :
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            (frameSlotsSaved extractFrame spC (extractSavedVals s) **
              extractSpareSlot spC) **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
            extractToBufOwn toBuf **
            (isCreationPtr ↦ₘ (1 : Word)) **
            (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            (.x31 ↦ᵣ (next - (0 : Word)))) st := by
        xperm_hyp hq1
      have hsf := frameSlotsSaved_imp_stackFree10 sp0 spC s hspC
      have hq3 :=
        sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono hsf (fun _ x => x))) st hq2
      xperm_hyp hq3) hseq

set_option maxRecDepth 8000 in
/-- Copy HaveField + stack + live ra/s7. -/
theorem extractHaveFieldCopy_stack
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor contentPtr toBuf isCreationPtr
      t2Old t1Old t0Old a0Old w0 w1 w2 old16 ra s7 : Word)
    (txBytes : List (BitVec 8))
    (hcalign : contentPtr.toNat % 8 = 0)
    (hcover : contentPtr.toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess (contentPtr + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))
      HaveField EpiRestore extractLinkedCode
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) := by
  have h := extractHaveFieldCopy_framed txBase lenW typeW innerW endPtr cursor
    contentPtr toBuf isCreationPtr t2Old t1Old t0Old a0Old w0 w1 w2 old16
    txBytes hcalign hcover hcvalid htalign htover htvalid
  have hF := cpsTripleWithin_frameR
    (joinStackAmbient spC s ** (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7))
    (by pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- Non-frame rest after copy (owned across epi leaf). -/
def copyEpiRest (spC : Word)
    (txBase toBuf isCreationPtr typeW innerW contentPtr w0 w1 w2 old16 : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  extractSpareSlot spC **
    bytesRegion txBase txBytes **
    (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
    ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
      (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
    (isCreationPtr ↦ₘ (0 : Word)) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
    (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
    (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
    (.x31 ↦ᵣ contentPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16

private theorem copyEpiRest_pcFree (spC : Word)
    (txBase toBuf isCreationPtr typeW innerW contentPtr w0 w1 w2 old16 : Word)
    (txBytes : List (BitVec 8)) :
    (copyEpiRest spC txBase toBuf isCreationPtr typeW innerW contentPtr
      w0 w1 w2 old16 txBytes).pcFree := by
  unfold copyEpiRest; pcf

/-- Flat post after copy (no nested composite defs). -/
private def copyFlatPost (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor contentPtr toBuf isCreationPtr
      w0 w1 w2 old16 ra s7 : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) ** (Reg.x23 ↦ᵣ s7) **
    frameSlotsSaved extractFrame spC (extractSavedVals s) **
    extractSpareSlot spC **
    bytesRegion txBase txBytes **
    (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
    ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
      (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
    (isCreationPtr ↦ₘ (0 : Word)) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
    (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
    (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
    (.x31 ↦ᵣ contentPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16

private theorem copy_post_to_flat
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor contentPtr toBuf isCreationPtr
      w0 w1 w2 old16 ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h,
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) h →
      copyFlatPost spC s txBase lenW typeW innerW endPtr cursor contentPtr toBuf
        isCreationPtr w0 w1 w2 old16 ra s7 txBytes h := by
  intro h hp
  simp only [haveFieldCopyAmbient, joinStackAmbient, copyFlatPost] at hp ⊢
  xperm_hyp hp

private theorem copy_flat_to_epiPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor contentPtr toBuf isCreationPtr
      w0 w1 w2 old16 ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h,
      copyFlatPost spC s txBase lenW typeW innerW endPtr cursor contentPtr toBuf
        isCreationPtr w0 w1 w2 old16 ra s7 txBytes h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame
            (extractSavedVals
              (joinCur ra txBase lenW toBuf isCreationPtr typeW cursor endPtr
                s7)) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        copyEpiRest spC txBase toBuf isCreationPtr typeW innerW contentPtr
          w0 w1 w2 old16 txBytes) h := by
  intro h hp
  simp only [copyFlatPost, copyEpiRest] at hp ⊢
  rw [regsAt_joinCur]
  xperm_hyp hp

private theorem copy_post_to_epiPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor contentPtr toBuf isCreationPtr
      w0 w1 w2 old16 ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h,
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame
            (extractSavedVals
              (joinCur ra txBase lenW toBuf isCreationPtr typeW cursor endPtr
                s7)) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        copyEpiRest spC txBase toBuf isCreationPtr typeW innerW contentPtr
          w0 w1 w2 old16 txBytes) h := by
  intro h hp
  exact copy_flat_to_epiPre spC s txBase lenW typeW innerW endPtr cursor
    contentPtr toBuf isCreationPtr w0 w1 w2 old16 ra s7 txBytes h
    (copy_post_to_flat spC s txBase lenW typeW innerW endPtr cursor contentPtr
      toBuf isCreationPtr w0 w1 w2 old16 ra s7 txBytes h hp)

/-- Convert concrete toBuf dwords → extractToBufOwn for Assumed post. -/
private theorem copyToBuf_to_own
    (toBuf contentPtr w0 w1 w2 old16 : Word) :
    ∀ h,
      ((toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32))) h →
      extractToBufOwn toBuf h := by
  intro h hp
  simp only [extractToBufOwn]
  have hq :=
    sepConj_mono (memIs_implies_memOwn (v := w0))
      (sepConj_mono (memIs_implies_memOwn (v := w1))
        (memIs_implies_memOwn
          (v := replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
            (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32))))
      h hp
  exact hq

set_option maxRecDepth 8000 in
/-- Copy: HaveField → ret; a0=0; stackFree restored; toBuf owned. -/
theorem extractHaveFieldCopy_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor contentPtr toBuf isCreationPtr
      t2Old t1Old t0Old a0Old w0 w1 w2 old16 ra s7 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcalign : contentPtr.toNat % 8 = 0)
    (hcover : contentPtr.toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess (contentPtr + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin
      ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
      HaveField s.ra extractLinkedCode
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (0 : Word)) **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16) := by
  let cur :=
    joinCur ra txBase lenW toBuf isCreationPtr typeW cursor endPtr s7
  have hHave := extractHaveFieldCopy_stack spC s txBase lenW typeW innerW
    endPtr cursor contentPtr toBuf isCreationPtr t2Old t1Old t0Old a0Old
    w0 w1 w2 old16 ra s7 txBytes hcalign hcover hcvalid htalign htover htvalid
  have hHave2 :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (copy_post_to_epiPre spC s txBase lenW typeW innerW endPtr cursor
        contentPtr toBuf isCreationPtr w0 w1 w2 old16 ra s7 txBytes) hHave
  have hHave3 : cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))
      HaveField EpiRestore extractLinkedCode
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame (extractSavedVals cur) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        copyEpiRest spC txBase toBuf isCreationPtr typeW innerW contentPtr
          w0 w1 w2 old16 txBytes) := by
    simpa [cur] using hHave2
  have hEpi := extractEpilogueSuccess_linked sp0 spC s cur (0 : Word) hspC hret
  have hEpiF :=
    cpsTripleWithin_frameR
      (copyEpiRest spC txBase toBuf isCreationPtr typeW innerW contentPtr
        w0 w1 w2 old16 txBytes)
      (copyEpiRest_pcFree _ _ _ _ _ _ _ _ _ _ _ _) hEpi
  have hseq := cpsTripleWithin_seq_same_cr hHave3 hEpiF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun st hq => by
      have hq1 :
          (((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            frameSlotsSaved extractFrame spC (extractSavedVals s)) **
            copyEpiRest spC txBase toBuf isCreationPtr typeW innerW contentPtr
              w0 w1 w2 old16 txBytes) st := by
        xperm_hyp hq
      simp only [copyEpiRest] at hq1
      have hq2 :
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            (frameSlotsSaved extractFrame spC (extractSavedVals s) **
              extractSpareSlot spC) **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
            ((toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
              ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
                (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32))) **
            (isCreationPtr ↦ₘ (0 : Word)) **
            (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
            (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
            (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
            (.x31 ↦ᵣ contentPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16) st := by
        xperm_hyp hq1
      have hsf := frameSlotsSaved_imp_stackFree10 sp0 spC s hspC
      have hto := copyToBuf_to_own toBuf contentPtr w0 w1 w2 old16
      have hq3 :=
        sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono hsf
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono hto (fun _ x => x)))))) st hq2
      xperm_hyp hq3) hseq

#print axioms extractHaveFieldCreation_stack
#print axioms extractHaveFieldCreation_then_epi
#print axioms extractHaveFieldCopy_stack
#print axioms extractHaveFieldCopy_then_epi
#print axioms frameSlotsSaved_imp_stackFree10

end EvmAsm.Codegen.TxExtractToAddressSpec
