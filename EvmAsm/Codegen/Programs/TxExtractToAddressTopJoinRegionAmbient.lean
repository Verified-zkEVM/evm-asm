/-
  Ambient dual: HaveField copy → epi with content inside bytesRegion
  (x8=loadPtr, regionBase for blob/content).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopHaveField
import EvmAsm.Codegen.Programs.TxExtractToAddressTopEpilogue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoinRegion
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

/-- Epi rest after ambient region copy. -/
def copyEpiRestRegionAmbient (spC regionBase toBuf isCreationPtr typeW innerW
    contentPtr w0 w1 w2 old16 : Word) (bs : List (BitVec 8)) : Assertion :=
  extractSpareSlot spC **
    bytesRegion regionBase bs **
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

private theorem copyEpiRestRegionAmbient_pcFree (spC regionBase toBuf isCreationPtr
    typeW innerW contentPtr w0 w1 w2 old16 : Word) (bs : List (BitVec 8)) :
    (copyEpiRestRegionAmbient spC regionBase toBuf isCreationPtr typeW innerW
      contentPtr w0 w1 w2 old16 bs).pcFree := by
  unfold copyEpiRestRegionAmbient; pcf

private theorem copy_post_region_to_epiPre_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr cursor toBuf isCreationPtr
      contentPtr w0 w1 w2 old16 ra s7 : Word)
    (bs : List (BitVec 8)) :
    ∀ h,
      (haveFieldCopyAmbientNoBytes loadPtr lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame
            (extractSavedVals
              (joinCur ra loadPtr lenW toBuf isCreationPtr typeW cursor endPtr
                s7)) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        copyEpiRestRegionAmbient spC regionBase toBuf isCreationPtr typeW innerW
          contentPtr w0 w1 w2 old16 bs) h := by
  intro h hp
  simp only [haveFieldCopyAmbientNoBytes, joinStackAmbient,
    copyEpiRestRegionAmbient] at hp ⊢
  rw [regsAt_joinCur]
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- HaveField → EpiRestore ambient region copy (x8=loadPtr, blob=regionBase). -/
theorem extractHaveFieldCopy_stack_region_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr cursor toBuf isCreationPtr
      t2Old t1Old t0Old a0Old old16 ra s7 : Word)
    (bs : List (BitVec 8)) (q : Nat)
    (hq : 8 * q + 16 < bs.length)
    (halign : regionBase.toNat % 8 = 0)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    let contentPtr := regionBase + BitVec.ofNat 64 (8 * q)
    let w0 := (contentWordsAt bs q).1
    let w1 := (contentWordsAt bs q).2.1
    let w2 := (contentWordsAt bs q).2.2
    cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))
      HaveField EpiRestore extractLinkedCode
      (haveFieldCopyAmbientNoBytes loadPtr lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      (haveFieldCopyAmbientNoBytes loadPtr lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) := by
  intro contentPtr w0 w1 w2
  let R : Assertion :=
    haveFieldCopyAmbientNoBytes loadPtr lenW typeW innerW endPtr cursor **
      joinStackAmbient spC s **
      (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7)
  have hR : R.pcFree := by
    dsimp only [R]; pcf
  have h := extractHaveFieldCopy_region_frame regionBase toBuf isCreationPtr
    t2Old t1Old t0Old a0Old old16 bs q R hR hq halign hcover hcvalid
    htalign htover htvalid
  refine cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [R, contentPtr, w0, w1, w2] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [R, contentPtr, w0, w1, w2] at hq ⊢
    xperm_hyp hq) h

set_option maxRecDepth 8000 in
theorem extractHaveFieldCopy_then_epi_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr cursor toBuf isCreationPtr
      t2Old t1Old t0Old a0Old old16 ra s7 : Word)
    (bs : List (BitVec 8)) (q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hq : 8 * q + 16 < bs.length)
    (halign : regionBase.toNat % 8 = 0)
    (hcover : regionBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    let contentPtr := regionBase + BitVec.ofNat 64 (8 * q)
    let w0 := (contentWordsAt bs q).1
    let w1 := (contentWordsAt bs q).2.1
    let w2 := (contentWordsAt bs q).2.2
    cpsTripleWithin
      ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
      HaveField s.ra extractLinkedCode
      (haveFieldCopyAmbientNoBytes loadPtr lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
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
    joinCur ra loadPtr lenW toBuf isCreationPtr typeW cursor endPtr s7
  have hHave := extractHaveFieldCopy_stack_region_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr cursor toBuf isCreationPtr t2Old t1Old t0Old a0Old
    old16 ra s7 bs q hq halign hcover hcvalid htalign htover htvalid
  have hHave2 :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (copy_post_region_to_epiPre_ambient spC s loadPtr regionBase lenW typeW
        innerW endPtr cursor toBuf isCreationPtr contentPtr w0 w1 w2 old16 ra s7
        bs) hHave
  have hHave3 : cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))
      HaveField EpiRestore extractLinkedCode
      (haveFieldCopyAmbientNoBytes loadPtr lenW typeW innerW endPtr cursor **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame (extractSavedVals cur) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        copyEpiRestRegionAmbient spC regionBase toBuf isCreationPtr typeW innerW
          contentPtr w0 w1 w2 old16 bs) := by
    simpa [cur] using hHave2
  have hEpi := extractEpilogueSuccess_linked sp0 spC s cur (0 : Word) hspC hret
  have hEpiF :=
    cpsTripleWithin_frameR
      (copyEpiRestRegionAmbient spC regionBase toBuf isCreationPtr typeW innerW
        contentPtr w0 w1 w2 old16 bs)
      (copyEpiRestRegionAmbient_pcFree _ _ _ _ _ _ _ _ _ _ _ _) hEpi
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
            copyEpiRestRegionAmbient spC regionBase toBuf isCreationPtr typeW
              innerW contentPtr w0 w1 w2 old16 bs) st := by
        xperm_hyp hq
      simp only [copyEpiRestRegionAmbient] at hq1
      have hq2 :
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            (frameSlotsSaved extractFrame spC (extractSavedVals s) **
              extractSpareSlot spC) **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion regionBase bs **
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

#print axioms extractHaveFieldCopy_stack_region_ambient
#print axioms extractHaveFieldCopy_then_epi_region_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
