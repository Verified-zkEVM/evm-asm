/-
  Ambient dual: type234 HaveField creation under midOwned (split loadPtr/regionBase).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext5Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNextRest
import EvmAsm.Codegen.Programs.TxExtractToAddressTopHaveField
import EvmAsm.Codegen.Programs.TxExtractToAddressHaveFieldBody
import EvmAsm.Codegen.Programs.TxExtractToAddressHaveField
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopEpilogue
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
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

/-- Split-base HaveField creation ambient. -/
def haveFieldCreAmbientAmbient
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (.x18 ↦ᵣ toBuf) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ contentPtr) ** (.x22 ↦ᵣ endPtr) **
    (.x11 ↦ᵣ (0 : Word)) **
    (.x31 ↦ᵣ (next - (0 : Word))) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf

private theorem haveFieldCreAmbientAmbient_pcFree
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next : Word)
    (bs : List (BitVec 8)) :
    (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
      contentPtr endPtr next bs).pcFree := by
  unfold haveFieldCreAmbientAmbient; pcf

/-- Epi rest with ambient blob. -/
def creationEpiRestAmbient (spC regionBase toBuf isCreationPtr typeW innerW next : Word)
    (bs : List (BitVec 8)) : Assertion :=
  extractSpareSlot spC **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x31 ↦ᵣ (next - (0 : Word)))

private theorem creationEpiRestAmbient_pcFree
    (spC regionBase toBuf isCreationPtr typeW innerW next : Word)
    (bs : List (BitVec 8)) :
    (creationEpiRestAmbient spC regionBase toBuf isCreationPtr typeW innerW next
      bs).pcFree := by
  unfold creationEpiRestAmbient; pcf

private def creationFlatPostAmbient (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) ** (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ contentPtr) ** (.x22 ↦ᵣ endPtr) ** (Reg.x23 ↦ᵣ s7) **
    frameSlotsSaved extractFrame spC (extractSavedVals s) **
    extractSpareSlot spC **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x31 ↦ᵣ (next - (0 : Word)))

private theorem creation_post_to_flat_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (bs : List (BitVec 8)) :
    ∀ h,
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) h →
      creationFlatPostAmbient spC s loadPtr regionBase lenW typeW innerW toBuf
        contentPtr endPtr next isCreationPtr ra s7 bs h := by
  intro h hp
  simp only [haveFieldCreAmbientAmbient, joinStackAmbient,
    creationFlatPostAmbient] at hp ⊢
  xperm_hyp hp

private theorem creation_flat_to_epiPre_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (bs : List (BitVec 8)) :
    ∀ h,
      creationFlatPostAmbient spC s loadPtr regionBase lenW typeW innerW toBuf
        contentPtr endPtr next isCreationPtr ra s7 bs h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame
            (extractSavedVals
              (joinCur ra loadPtr lenW toBuf isCreationPtr typeW contentPtr endPtr
                s7)) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        creationEpiRestAmbient spC regionBase toBuf isCreationPtr typeW innerW next
          bs) h := by
  intro h hp
  simp only [creationFlatPostAmbient, creationEpiRestAmbient] at hp ⊢
  rw [regsAt_joinCur]
  xperm_hyp hp

private theorem creation_post_to_epiPre_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr ra s7 : Word)
    (bs : List (BitVec 8)) :
    ∀ h,
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) h →
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame
            (extractSavedVals
              (joinCur ra loadPtr lenW toBuf isCreationPtr typeW contentPtr endPtr
                s7)) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        creationEpiRestAmbient spC regionBase toBuf isCreationPtr typeW innerW next
          bs) h := by
  intro h hp
  exact creation_flat_to_epiPre_ambient spC s loadPtr regionBase lenW typeW
    innerW toBuf contentPtr endPtr next isCreationPtr ra s7 bs h
    (creation_post_to_flat_ambient spC s loadPtr regionBase lenW typeW innerW
      toBuf contentPtr endPtr next isCreationPtr ra s7 bs h hp)

set_option maxRecDepth 8000 in
theorem extractHaveFieldCreation_framed_ambient
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr t2Old t0Old a0Old : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + (1 + (1 + (1 + 1))))) HaveField EpiRestore
      extractLinkedCode
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
  have h := extractHaveFieldCreation isCreationPtr t2Old t0Old a0Old
  have hF := cpsTripleWithin_frameR
    (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
      contentPtr endPtr next bs)
    (haveFieldCreAmbientAmbient_pcFree _ _ _ _ _ _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractHaveFieldCreation_stack_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr t2Old t0Old a0Old ra s7 : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + (1 + (1 + (1 + 1))))) HaveField EpiRestore
      extractLinkedCode
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
  have h := extractHaveFieldCreation_framed_ambient loadPtr regionBase lenW
    typeW innerW toBuf contentPtr endPtr next isCreationPtr t2Old t0Old a0Old bs
  have hF := cpsTripleWithin_frameR
    (joinStackAmbient spC s ** (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7))
    (by pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractHaveFieldCreation_then_epi_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr t2Old t0Old a0Old ra s7 : Word)
    (bs : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
      HaveField s.ra extractLinkedCode
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
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
    joinCur ra loadPtr lenW toBuf isCreationPtr typeW contentPtr endPtr s7
  have hHave := extractHaveFieldCreation_stack_ambient spC s loadPtr regionBase
    lenW typeW innerW toBuf contentPtr endPtr next isCreationPtr t2Old t0Old
    a0Old ra s7 bs
  have hHave2 :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (creation_post_to_epiPre_ambient spC s loadPtr regionBase lenW typeW
        innerW toBuf contentPtr endPtr next isCreationPtr ra s7 bs) hHave
  have hHave3 : cpsTripleWithin (1 + (1 + (1 + (1 + (1 + 1))))) HaveField EpiRestore
      extractLinkedCode
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          contentPtr endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ ra) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
          regsAt extractFrame (extractSavedVals cur) **
          frameSlotsSaved extractFrame spC (extractSavedVals s)) **
        creationEpiRestAmbient spC regionBase toBuf isCreationPtr typeW innerW
          next bs) := by
    simpa [cur] using hHave2
  have hEpi := extractEpilogueSuccess_linked sp0 spC s cur (0 : Word) hspC hret
  have hEpiF :=
    cpsTripleWithin_frameR
      (creationEpiRestAmbient spC regionBase toBuf isCreationPtr typeW innerW
        next bs)
      (creationEpiRestAmbient_pcFree _ _ _ _ _ _ _ _) hEpi
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
            creationEpiRestAmbient spC regionBase toBuf isCreationPtr typeW
              innerW next bs) st := by
        xperm_hyp hq
      simp only [creationEpiRestAmbient] at hq1
      have hq2 :
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            (frameSlotsSaved extractFrame spC (extractSavedVals s) **
              extractSpareSlot spC) **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion regionBase bs **
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
theorem extractType234ToHaveField_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff5 : Nat) :
    cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
      (wn5OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
          bs absOff5 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn5StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff5
  let Pcore : Assertion :=
    wn5StableAmbient loadPtr lenW typeW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
      bytesRegion regionBase bs **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)
  let Q : Assertion :=
    wn5StableAmbient loadPtr lenW typeW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
      bytesRegion regionBase bs **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
      (.x31 ↦ᵣ (next - len))
  have htemps : cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
      (Pcore ** regOwn .x31) Q := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31) (fun t6Old => ?_)
    have h := extractType234ToHaveField next len t6Old
    have hF := cpsTripleWithin_frameR
      (wn5StableAmbient loadPtr lenW typeW innerW endPtr cursor **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion regionBase bs **
        (.x11 ↦ᵣ (0 : Word)))
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by dsimp only [Q] at hq ⊢; xperm_hyp hq) hF
  have hcore : cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
      (wn5OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
          bs absOff5)
      Q := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [wn5OkConcreteAmbient, wn5OkRegsAmbient, wn5CommonAmbient] at hp
      obtain ⟨hRegs, _hdec⟩ := (sepConj_pure_right h).mp hp
      have hP : (Pcore ** regOwn .x31) h := by
        dsimp only [Pcore]
        simp only [wn5StableAmbient] at hRegs ⊢
        xperm_hyp hRegs
      exact hP) (fun _ hq => by dsimp only [Q] at hq ⊢; exact hq) htemps
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) hcore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp only [Q, cursor] at hq ⊢
      xperm_hyp hq) hF

/-- Reshape ToHaveField ambient post (len=0) → creation pre ambient. -/
private theorem toHaveField_owned_post_to_creationPre_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff5 : Nat) :
    ∀ h,
      (wn5StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        midOwned spC s toBuf isCreationPtr s7) h →
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          (regionBase + BitVec.ofNat 64 absOff5) endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps ** regOwn .x7 ** regOwn .x5) h := by
  intro h hp
  simp only [wn5StableAmbient, midOwned, joinStackAmbient,
    haveFieldCreAmbientAmbient, extractToBufOwn, creExtraTemps] at hp ⊢
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem extractType234HaveFieldCreation_then_epi_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff5 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11))
      AfterWalkNext5Bne s.ra extractLinkedCode
      (wn5OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next
          (0 : Word) bs absOff5 **
        midOwned spC s toBuf isCreationPtr s7)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
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
        (.x31 ↦ᵣ (next - (0 : Word))) **
        creExtraTemps) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff5
  have hTo := extractType234ToHaveField_owned_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr next (0 : Word) toBuf isCreationPtr s7 bs absOff5
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
        (wn5OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next
            (0 : Word) bs absOff5 **
          midOwned spC s toBuf isCreationPtr s7)
        (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
            cursor endPtr next bs **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq1 :
            (wn5StableAmbient loadPtr lenW typeW innerW endPtr cursor **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
              regOwn .x29 ** regOwn .x30 **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
              bytesRegion regionBase bs **
              (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
              (.x31 ↦ᵣ (next - (0 : Word))) **
              midOwned spC s toBuf isCreationPtr s7) h := by
          simpa [cursor] using hq
        exact toHaveField_owned_post_to_creationPre_ambient spC s loadPtr
          regionBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 bs
          absOff5 _ hq1) hTo
  have hCre :
      cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
        HaveField s.ra extractLinkedCode
        (haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
            cursor endPtr next bs **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5)
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs **
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
          (.x31 ↦ᵣ (next - (0 : Word))) **
          creExtraTemps) := by
    let Pcore : Assertion :=
      haveFieldCreAmbientAmbient loadPtr regionBase lenW typeW innerW toBuf
          cursor endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps
    have htemps :
        cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** regOwn .x7 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion regionBase bs **
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
            (.x31 ↦ᵣ (next - (0 : Word))) **
            creExtraTemps) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x5)
        (P := Pcore) (fun t2Old t0Old => ?_)
      have h := extractHaveFieldCreation_then_epi_ambient sp0 spC s loadPtr
        regionBase lenW typeW innerW toBuf cursor endPtr next isCreationPtr
        t2Old t0Old next LinkWalkNext5 s7 bs hspC hret
      have hF := cpsTripleWithin_frameR creExtraTemps creExtraTemps_pcFree h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore, creExtraTemps] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [creExtraTemps] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, creExtraTemps] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  exact cpsTripleWithin_seq_same_cr hTo2 hCre

#print axioms extractHaveFieldCreation_then_epi_ambient
#print axioms extractType234ToHaveField_owned_ambient
#print axioms extractType234HaveFieldCreation_then_epi_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
