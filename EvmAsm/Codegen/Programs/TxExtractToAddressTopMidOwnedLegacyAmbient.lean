/-
  Ambient dual: legacy HaveField creation under midOwned (split loadPtr/regionBase).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressLegacyWalk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwnedAmbient
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

set_option maxRecDepth 8000 in
theorem extractLegacyToHaveField_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff3 : Nat) :
    cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      (leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff3) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff3
  let Pcore : Assertion :=
    legStableAmbient loadPtr lenW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
      bytesRegion regionBase bs **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)
  let Q : Assertion :=
    legStableAmbient loadPtr lenW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
      bytesRegion regionBase bs **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
      (.x31 ↦ᵣ (next - len))
  have htemps : cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      (Pcore ** regOwn .x31) Q := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31) (fun t6Old => ?_)
    have h := extractLegacyToHaveField next len t6Old
    have hF := cpsTripleWithin_frameR
      (legStableAmbient loadPtr lenW innerW endPtr cursor **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion regionBase bs **
        (.x11 ↦ᵣ (0 : Word)))
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by dsimp only [Q] at hq ⊢; xperm_hyp hq) hF
  have hcore : cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      (leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff3)
      Q := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [leg3OkConcreteAmbient, leg3OkRegsAmbient, leg3CommonAmbient] at hp
      obtain ⟨hRegs, _hdec⟩ := (sepConj_pure_right h).mp hp
      have hP : (Pcore ** regOwn .x31) h := by
        dsimp only [Pcore]
        simp only [legStableAmbient] at hRegs ⊢
        xperm_hyp hRegs
      exact hP) (fun _ hq => by dsimp only [Q] at hq ⊢; exact hq) htemps
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) hcore
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp only [Q, cursor] at hq ⊢
      xperm_hyp hq) hF

private theorem legacy_toHaveField_owned_post_to_creationPre_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff3 : Nat) :
    ∀ h,
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff3) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        midOwned spC s toBuf isCreationPtr s7) h →
      (haveFieldCreAmbientAmbient loadPtr regionBase lenW (0 : Word) innerW toBuf
          (regionBase + BitVec.ofNat 64 absOff3) endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps ** regOwn .x7 ** regOwn .x5) h := by
  intro h hp
  simp only [legStableAmbient, midOwned, joinStackAmbient,
    haveFieldCreAmbientAmbient, extractToBufOwn, creExtraTemps] at hp ⊢
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem extractLegacyHaveFieldCreation_then_epi_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff3 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11))
      AfterLegacyWalk3Bne s.ra extractLinkedCode
      (leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next
          (0 : Word) bs absOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (1 : Word)) **
        (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
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
  let cursor := regionBase + BitVec.ofNat 64 absOff3
  have hTo := extractLegacyToHaveField_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr next (0 : Word) toBuf isCreationPtr s7 bs absOff3
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
        (leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next
            (0 : Word) bs absOff3 **
          midOwned spC s toBuf isCreationPtr s7)
        (haveFieldCreAmbientAmbient loadPtr regionBase lenW (0 : Word) innerW toBuf
            cursor endPtr next bs **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq1 :
            (legStableAmbient loadPtr lenW innerW endPtr cursor **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
              regOwn .x29 ** regOwn .x30 **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
              bytesRegion regionBase bs **
              (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
              (.x31 ↦ᵣ (next - (0 : Word))) **
              midOwned spC s toBuf isCreationPtr s7) h := by
          simpa [cursor] using hq
        exact legacy_toHaveField_owned_post_to_creationPre_ambient spC s loadPtr
          regionBase lenW innerW endPtr next toBuf isCreationPtr s7 bs
          absOff3 _ hq1) hTo
  have hCre :
      cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
        HaveField s.ra extractLinkedCode
        (haveFieldCreAmbientAmbient loadPtr regionBase lenW (0 : Word) innerW toBuf
            cursor endPtr next bs **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
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
          (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
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
      haveFieldCreAmbientAmbient loadPtr regionBase lenW (0 : Word) innerW toBuf
          cursor endPtr next bs **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
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
            (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
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
        regionBase lenW (0 : Word) innerW toBuf cursor endPtr next isCreationPtr
        t2Old t0Old next LinkLegacyWalk3 s7 bs hspC hret
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

#print axioms extractLegacyToHaveField_owned_ambient
#print axioms extractLegacyHaveFieldCreation_then_epi_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
