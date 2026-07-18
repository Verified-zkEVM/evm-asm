/-
  HaveField copy → epi with content owned inside bytesRegion (no contentDwords).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopHaveField
import EvmAsm.Codegen.Programs.TxExtractToAddressTopEpilogue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
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

/-- haveFieldCopyAmbient without bytesRegion (leaf owns the region). -/
def haveFieldCopyAmbientNoBytes (txBase lenW typeW innerW endPtr
    cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
    (.x11 ↦ᵣ (0 : Word))

private theorem haveFieldCopyAmbientNoBytes_pcFree
    (txBase lenW typeW innerW endPtr cursor : Word) :
    (haveFieldCopyAmbientNoBytes txBase lenW typeW innerW endPtr
      cursor).pcFree := by
  unfold haveFieldCopyAmbientNoBytes; pcf

/-- Epi rest after region copy: full bytesRegion, no content cells. -/
def copyEpiRestRegion (spC : Word)
    (txBase toBuf isCreationPtr typeW innerW contentPtr w0 w1 w2 old16 : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  extractSpareSlot spC **
    bytesRegion txBase txBytes **
    (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
    ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
      (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
    (isCreationPtr ↦ₘ (0 : Word)) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
    (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
    (.x31 ↦ᵣ contentPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16

private theorem copyEpiRestRegion_pcFree (spC : Word)
    (txBase toBuf isCreationPtr typeW innerW contentPtr w0 w1 w2 old16 : Word)
    (txBytes : List (BitVec 8)) :
    (copyEpiRestRegion spC txBase toBuf isCreationPtr typeW innerW contentPtr
      w0 w1 w2 old16 txBytes).pcFree := by
  unfold copyEpiRestRegion; pcf

private theorem copyToBuf_to_own_region
    (toBuf contentPtr w0 w1 w2 old16 : Word) :
    ∀ h,
      ((toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32))) h →
      extractToBufOwn toBuf h := by
  intro h hp
  simp only [extractToBufOwn]
  exact sepConj_mono (memIs_implies_memOwn (v := w0))
    (sepConj_mono (memIs_implies_memOwn (v := w1))
      (memIs_implies_memOwn
        (v := replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32))))
    h hp

set_option maxRecDepth 8000 in
theorem extractHaveFieldCopy_stack_region
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor toBuf isCreationPtr
      t2Old t1Old t0Old a0Old old16 ra s7 : Word)
    (txBytes : List (BitVec 8)) (q : Nat)
    (hq : 8 * q + 16 < txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hcover : txBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    let contentPtr := txBase + BitVec.ofNat 64 (8 * q)
    let w0 := (contentWordsAt txBytes q).1
    let w1 := (contentWordsAt txBytes q).2.1
    let w2 := (contentWordsAt txBytes q).2.2
    cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))
      HaveField EpiRestore extractLinkedCode
      (haveFieldCopyAmbientNoBytes txBase lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      (haveFieldCopyAmbientNoBytes txBase lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) := by
  intro contentPtr w0 w1 w2
  let R : Assertion :=
    haveFieldCopyAmbientNoBytes txBase lenW typeW innerW endPtr cursor **
      joinStackAmbient spC s **
      (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7)
  have hR : R.pcFree := by
    dsimp only [R]; pcf
  have h := extractHaveFieldCopy_region_frame txBase toBuf isCreationPtr
    t2Old t1Old t0Old a0Old old16 txBytes q R hR hq halign hcover hcvalid
    htalign htover htvalid
  refine cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [R, contentPtr, w0, w1, w2] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [R, contentPtr, w0, w1, w2] at hq ⊢
    xperm_hyp hq) h

private theorem copy_post_region_to_epiPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor toBuf isCreationPtr
      contentPtr w0 w1 w2 old16 ra s7 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h,
      (haveFieldCopyAmbientNoBytes txBase lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
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
        copyEpiRestRegion spC txBase toBuf isCreationPtr typeW innerW contentPtr
          w0 w1 w2 old16 txBytes) h := by
  intro h hp
  simp only [haveFieldCopyAmbientNoBytes, joinStackAmbient, copyEpiRestRegion] at hp ⊢
  rw [regsAt_joinCur]
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem extractHaveFieldCopy_then_epi_region
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr cursor toBuf isCreationPtr
      t2Old t1Old t0Old a0Old old16 ra s7 : Word)
    (txBytes : List (BitVec 8)) (q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hq : 8 * q + 16 < txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hcover : txBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    let contentPtr := txBase + BitVec.ofNat 64 (8 * q)
    let w0 := (contentWordsAt txBytes q).1
    let w1 := (contentWordsAt txBytes q).2.1
    let w2 := (contentWordsAt txBytes q).2.2
    cpsTripleWithin
      ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
      HaveField s.ra extractLinkedCode
      (haveFieldCopyAmbientNoBytes txBase lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (0 : Word)) **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
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
  intro contentPtr w0 w1 w2
  let cur :=
    joinCur ra txBase lenW toBuf isCreationPtr typeW cursor endPtr s7
  have hHave := extractHaveFieldCopy_stack_region spC s txBase lenW typeW
    innerW endPtr cursor toBuf isCreationPtr t2Old t1Old t0Old a0Old old16
    ra s7 txBytes q hq halign hcover hcvalid htalign htover htvalid
  have hHave2 :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (copy_post_region_to_epiPre spC s txBase lenW typeW innerW endPtr cursor
        toBuf isCreationPtr contentPtr w0 w1 w2 old16 ra s7 txBytes) hHave
  have hHave3 : cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))
      HaveField EpiRestore extractLinkedCode
      (haveFieldCopyAmbientNoBytes txBase lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame (extractSavedVals cur) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        copyEpiRestRegion spC txBase toBuf isCreationPtr typeW innerW contentPtr
          w0 w1 w2 old16 txBytes) := by
    simpa [cur] using hHave2
  have hEpi := extractEpilogueSuccess_linked sp0 spC s cur (0 : Word) hspC hret
  have hEpiF :=
    cpsTripleWithin_frameR
      (copyEpiRestRegion spC txBase toBuf isCreationPtr typeW innerW contentPtr
        w0 w1 w2 old16 txBytes)
      (copyEpiRestRegion_pcFree _ _ _ _ _ _ _ _ _ _ _ _) hEpi
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
            copyEpiRestRegion spC txBase toBuf isCreationPtr typeW innerW
              contentPtr w0 w1 w2 old16 txBytes) st := by
        xperm_hyp hq
      simp only [copyEpiRestRegion] at hq1
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
      have hto := copyToBuf_to_own_region toBuf contentPtr w0 w1 w2 old16
      have hq3 :=
        sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono hsf
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono hto (fun _ x => x)))))) st hq2
      xperm_hyp hq3) hseq

#print axioms extractHaveFieldCopy_stack_region
#print axioms extractHaveFieldCopy_then_epi_region

end EvmAsm.Codegen.TxExtractToAddressSpec
