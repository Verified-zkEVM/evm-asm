/-
  ExtractAssumed packaging: reshape E2E creation post → Assumed post
  (KEEP s0–s7; memIs→memOwn; temps→regOwn), mono nSteps.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2E
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps nTypeSteps nExtractStackDwords extractToBufOwn teaScratchOwn
    ExtractAssumed)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

theorem nFrontCreation_le_nExtract : nFrontCreationSteps ≤ nExtractSteps := by
  simp only [nFrontCreationSteps, nExtractSteps, nTypeSteps]
  omega

/-- Matches private `nFrontCopySteps` in TopFrontE2ECopy. -/
def nFrontCopySteps' : Nat :=
  (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) + ((1 + 81) + (1 + (1 + 1)))) +
    (((((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        ((1 + 1) +
          ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)))

theorem nFrontCopy_le_nExtract : nFrontCopySteps' ≤ nExtractSteps := by
  simp only [nFrontCopySteps', nExtractSteps, nTypeSteps]
  omega

private theorem regIs_to_regOwn (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h :=
  fun _ hx => ⟨v, hx⟩

/-- Flat E2E creation post (one witness for ∃ next5). -/
def creationE2EPost (sp0 : Word) (s : ExtractSaved)
    (txBase toBuf isCreationPtr next5 : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion txBase txBytes **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
    (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x31 ↦ᵣ (next5 - (0 : Word))) **
    creExtraTemps

private def keepPart (sp0 : Word) (s : ExtractSaved)
    (txBase toBuf : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion txBase txBytes **
    extractToBufOwn toBuf **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30

private def convIs (isCreationPtr next5 : Word) (txBytes : List (BitVec 8)) :
    Assertion :=
  (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
    (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
    (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x31 ↦ᵣ (next5 - (0 : Word)))

private def convOwn (isCreationPtr : Word) : Assertion :=
  memOwn isCreationPtr **
    memOwn TeaTypeAddr **
    memOwn TeaInnerAddr **
    regOwn .x5 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
    regOwn .x31

private theorem convIs_to_own (isCreationPtr next5 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ (st : PartialState), convIs isCreationPtr next5 txBytes st →
      convOwn isCreationPtr st := by
  intro st hp
  simp only [convIs, convOwn] at hp ⊢
  obtain ⟨a1, a2, ad, au, his, rest1⟩ := hp
  obtain ⟨b1, b2, bd, bu, hteaT, rest2⟩ := rest1
  obtain ⟨c1, c2, cd, cu, hteaI, rest3⟩ := rest2
  obtain ⟨d1, d2, dd, du, hx5, rest4⟩ := rest3
  obtain ⟨e1, e2, ed, eu, hx7, rest5⟩ := rest4
  obtain ⟨f1, f2, fd, fu, hx11, rest6⟩ := rest5
  obtain ⟨g1, g2, gd, gu, hx12, hx31⟩ := rest6
  exact ⟨a1, a2, ad, au, memIs_implies_memOwn _ his,
    b1, b2, bd, bu, memIs_implies_memOwn _ hteaT,
    c1, c2, cd, cu, memIs_implies_memOwn _ hteaI,
    d1, d2, dd, du, regIs_to_regOwn .x5 _ _ hx5,
    e1, e2, ed, eu, regIs_to_regOwn .x7 _ _ hx7,
    f1, f2, fd, fu, regIs_to_regOwn .x11 _ _ hx11,
    g1, g2, gd, gu, regIs_to_regOwn .x12 _ _ hx12,
    regIs_to_regOwn .x31 _ _ hx31⟩

set_option maxRecDepth 8000 in
/-- Creation E2E post → extractAssumedPost (KEEP s0–s7). -/
theorem creationPost_to_assumed
    (sp0 : Word) (s : ExtractSaved)
    (txBase toBuf isCreationPtr next5 : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h, creationE2EPost sp0 s txBase toBuf isCreationPtr next5 txBytes h →
      extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes h := by
  intro h hp
  simp only [creationE2EPost, creExtraTemps] at hp
  have hp1 : (keepPart sp0 s txBase toBuf txBytes **
      convIs isCreationPtr next5 txBytes) h := by
    simp only [keepPart, convIs]
    xperm_hyp hp
  obtain ⟨hk, hc, hd, hu, hKeep, hConv⟩ := hp1
  have hConv' := convIs_to_own isCreationPtr next5 txBytes hc hConv
  have hJoined : (keepPart sp0 s txBase toBuf txBytes **
      convOwn isCreationPtr) h :=
    ⟨hk, hc, hd, hu, hKeep, hConv'⟩
  simp only [keepPart, convOwn, extractAssumedPost, teaScratchOwn] at hJoined ⊢
  xperm_hyp hJoined

/-- Drop ∃ next5 and reshape to Assumed post. -/
theorem creationPostEx_to_assumed
    (sp0 : Word) (s : ExtractSaved)
    (txBase toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) :
    ∀ h, (∃ next5 : Word,
        creationE2EPost sp0 s txBase toBuf isCreationPtr next5 txBytes h) →
      extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes h := by
  intro h ⟨next5, hp⟩
  exact creationPost_to_assumed sp0 s txBase toBuf isCreationPtr next5
    txBytes h hp

/-- E2E entry pre (matches `extractFrontCreation_then_epi`). -/
def creationE2EPre (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
    frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
    (prologueAbiRest txBase lenW toBuf isCreationPtr
      old5 old6 old7 old14 old15 old16) **
    extractToBufOwn toBuf ** memOwn isCreationPtr **
    frontExtraAmbient txBase txBytes

/-- Assumed pre with concrete temps (after of_forall peels). -/
def assumedPreConcrete (ret sp0 : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
    (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
    bytesRegion txBase txBytes **
    extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
    (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
    (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
theorem assumedPreConcrete_to_e2e
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12)) :
    ∀ h, assumedPreConcrete s.ra sp0 s txBase lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 txBytes h →
      creationE2EPre sp0 spC s txBase lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 txBytes h := by
  intro h hp
  simp only [assumedPreConcrete, creationE2EPre, prologueAbiRest,
    frontExtraAmbient, teaScratchOwn, regsAt_extractFrame s] at hp ⊢
  have heq := stackFree10_eq_frameSlotsOwn sp0 spC hspC
  simp only [heq] at hp
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_concrete
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : cpsTripleWithin nFrontCreationSteps E s.ra extractLinkedCode
      (creationE2EPre sp0 spC s txBase lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 txBytes)
      (fun h => ∃ next5 : Word,
        creationE2EPost sp0 s txBase toBuf isCreationPtr next5 txBytes h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (assumedPreConcrete s.ra sp0 s txBase lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  have h1 := cpsTripleWithin_mono_nSteps nFrontCreation_le_nExtract hE2E
  refine cpsTripleWithin_weaken
    (fun st hp => assumedPreConcrete_to_e2e sp0 spC s txBase lenW toBuf
      isCreationPtr old5 old6 old7 old14 old15 old16 txBytes hspC st hp)
    (fun st hq => creationPostEx_to_assumed sp0 s txBase toBuf isCreationPtr
      txBytes st hq) h1

private theorem of_forall_regOwn6
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 r4 r5 r6 : Reg} {P Q : Assertion}
    (hspec : ∀ v1 v2 v3 v4 v5 v6, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 **
       regOwn r4 ** regOwn r5 ** regOwn r6) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, ⟨v6, hv6⟩⟩ := hO5
  exact hspec v1 v2 v3 v4 v5 v6 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1,
        g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
        g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5, hv6⟩, hRb⟩ hpc

private def assumedCore (sp0 : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
    (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
    bytesRegion txBase txBytes **
    extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_temps
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCreationSteps E s.ra extractLinkedCode
        (creationE2EPre sp0 spC s txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 txBytes)
        (fun h => ∃ next5 : Word,
          creationE2EPost sp0 s txBase toBuf isCreationPtr next5 txBytes h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  let Q := extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
    s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes
  let Core := assumedCore sp0 s txBase lenW toBuf isCreationPtr txBytes
  have htemps : cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (Core ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16) Q := by
    refine of_forall_regOwn6 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x14) (r5 := .x15) (r6 := .x16) (fun old5 old6 old7 old14 old15 old16 => ?_)
    have hc := extractAssumed_creation_concrete sp0 spC s txBase lenW
      toBuf isCreationPtr old5 old6 old7 old14 old15 old16 txBytes hspC
      (hE2E old5 old6 old7 old14 old15 old16)
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Core, assumedCore, assumedPreConcrete] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Q] at hq ⊢; exact hq) hc
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [extractAssumedPre] at hp ⊢
    dsimp [Core, assumedCore] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp [Q] at hq ⊢; exact hq) htemps


/-- FrontCreation pre is defeq to `creationE2EPre` (shared atom list). -/
theorem frontCreation_pre_eq_e2e
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8)) :
    ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
      frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
      prologueAbiRest txBase lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
      extractToBufOwn toBuf ** memOwn isCreationPtr **
      frontExtraAmbient txBase txBytes) =
    creationE2EPre sp0 spC s txBase lenW toBuf isCreationPtr
      old5 old6 old7 old14 old15 old16 txBytes := by
  simp only [creationE2EPre]

set_option maxRecDepth 8000 in
/-- Wire: Assumed pre/post under extractLinkedCode given FrontCreation E2E
    for all temp olds (honesty residuals live on the E2E hyp). -/
theorem extractAssumed_creation_of_front
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hFront : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCreationSteps E s.ra extractLinkedCode
        ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
          frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
          prologueAbiRest txBase lenW toBuf isCreationPtr
            old5 old6 old7 old14 old15 old16 **
          extractToBufOwn toBuf ** memOwn isCreationPtr **
          frontExtraAmbient txBase txBytes)
        (fun h => ∃ next5 : Word,
          creationE2EPost sp0 s txBase toBuf isCreationPtr next5 txBytes h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  extractAssumed_creation_temps sp0 spC s txBase lenW toBuf isCreationPtr
    txBytes hspC (fun old5 old6 old7 old14 old15 old16 => by
      have h := hFront old5 old6 old7 old14 old15 old16
      simpa only [creationE2EPre] using h)

#print axioms nFrontCreation_le_nExtract
#print axioms nFrontCopy_le_nExtract
#print axioms creationPost_to_assumed
#print axioms creationPostEx_to_assumed
#print axioms assumedPreConcrete_to_e2e
#print axioms extractAssumed_creation_concrete
#print axioms extractAssumed_creation_temps
#print axioms extractAssumed_creation_of_front

end EvmAsm.Codegen.TxExtractToAddressSpec
