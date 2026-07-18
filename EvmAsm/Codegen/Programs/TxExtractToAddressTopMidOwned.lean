/-
  Frame stack + toBuf/isCreation through type234 end → HaveField creation → ret.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNextRest
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoin
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

/-- Owned across mid walks / HaveField (not in wn*Stable). -/
def midOwned (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr s7 : Word) : Assertion :=
  joinStackAmbient spC s **
    (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
    extractToBufOwn toBuf ** memOwn isCreationPtr **
    (Reg.x23 ↦ᵣ s7)

private theorem midOwned_pcFree (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr s7 : Word) :
    (midOwned spC s toBuf isCreationPtr s7).pcFree := by
  unfold midOwned joinStackAmbient extractToBufOwn; pcf

/-- Temps framed across creation (not clobbered). -/
def creExtraTemps : Assertion :=
  regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30

private theorem creExtraTemps_pcFree : creExtraTemps.pcFree := by
  unfold creExtraTemps; pcf

set_option maxRecDepth 8000 in
/-- type234 SUB+JAL HaveField with stack/toBuf/isCreation framed. -/
theorem extractType234ToHaveField_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff5 : Nat) :
    cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
      (wn5OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff5 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractType234ToHaveField_framed txBase lenW typeW innerW endPtr
    next len txBytes srcOff5
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- Reshape ToHaveField post (len=0) → creation pre + extra temps.
    Shape: `Pcore ** regOwn x7 ** regOwn x5` (right-assoc for of_forall2). -/
private theorem toHaveField_owned_post_to_creationPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff5 : Nat) :
    ∀ h,
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        midOwned spC s toBuf isCreationPtr s7) h →
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf
          (txBase + BitVec.ofNat 64 srcOff5) endPtr next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps ** regOwn .x7 ** regOwn .x5) h := by
  intro h hp
  simp only [wn5Stable, midOwned, joinStackAmbient, haveFieldCreAmbient,
    extractToBufOwn, creExtraTemps] at hp ⊢
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- type234 end (len=0) → creation → ret under midOwned. -/
theorem extractType234HaveFieldCreation_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff5 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11))
      AfterWalkNext5Bne s.ra extractLinkedCode
      (wn5OkConcrete txBase lenW typeW innerW endPtr next (0 : Word)
          txBytes srcOff5 **
        midOwned spC s toBuf isCreationPtr s7)
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
        (.x31 ↦ᵣ (next - (0 : Word))) **
        creExtraTemps) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff5
  have hTo := extractType234ToHaveField_owned spC s txBase lenW typeW innerW
    endPtr next (0 : Word) toBuf isCreationPtr s7 txBytes srcOff5
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
        (wn5OkConcrete txBase lenW typeW innerW endPtr next (0 : Word)
            txBytes srcOff5 **
          midOwned spC s toBuf isCreationPtr s7)
        (haveFieldCreAmbient txBase lenW typeW innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq1 :
            (wn5Stable txBase lenW typeW innerW endPtr cursor **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
              regOwn .x29 ** regOwn .x30 **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
              bytesRegion txBase txBytes **
              (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
              (.x31 ↦ᵣ (next - (0 : Word))) **
              midOwned spC s toBuf isCreationPtr s7) h := by
          simpa [cursor] using hq
        exact toHaveField_owned_post_to_creationPre spC s txBase lenW typeW
          innerW endPtr next toBuf isCreationPtr s7 txBytes srcOff5 _ hq1) hTo
  have hCre :
      cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
        HaveField s.ra extractLinkedCode
        (haveFieldCreAmbient txBase lenW typeW innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5)
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
          (.x31 ↦ᵣ (next - (0 : Word))) **
          creExtraTemps) := by
    let Pcore : Assertion :=
      haveFieldCreAmbient txBase lenW typeW innerW toBuf cursor endPtr next
          txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps
    -- of_forall2 shape first (TopT1 pattern), then reassoc to flat.
    have htemps :
        cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** regOwn .x7 ** regOwn .x5)
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
            (.x31 ↦ᵣ (next - (0 : Word))) **
            creExtraTemps) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x5)
        (P := Pcore) (fun t2Old t0Old => ?_)
      have h := extractHaveFieldCreation_then_epi sp0 spC s txBase lenW typeW
        innerW toBuf cursor endPtr next isCreationPtr t2Old t0Old next
        LinkWalkNext5 s7 txBytes hspC hret
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

#print axioms extractType234ToHaveField_owned
#print axioms extractType234HaveFieldCreation_then_epi

end EvmAsm.Codegen.TxExtractToAddressSpec
