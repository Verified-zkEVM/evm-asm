/-
  Ambient dual: reshape E2E creation post → ExtractAssumedAmbient footprint.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontMidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2EShortDecode
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2E
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2ELongConcrete
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps nTypeSteps nExtractStackDwords extractToBufOwn teaScratchOwn
    fullCode extractLinked_mono)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch txSlice)

theorem nFrontCreationStepsShort_le_nExtract :
    nFrontCreationStepsShort ≤ nExtractSteps := by
  simp only [nFrontCreationStepsShort, nExtractSteps, nTypeSteps]
  omega

private theorem regIs_to_regOwn (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h :=
  fun _ hx => ⟨v, hx⟩

/-- Ambient E2E creation post (regionBase/bs; teer on slice). -/
def creationE2EPostAmbient (sp0 : Word) (s : ExtractSaved)
    (regionBase toBuf isCreationPtr next5 : Word)
    (bs : List (BitVec 8)) (off len : Nat) : Assertion :=
  (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
    (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
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

private def keepPartAmbient (sp0 : Word) (s : ExtractSaved)
    (regionBase toBuf : Word) (bs : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30

private def convIsAmbient (isCreationPtr next5 : Word)
    (bs : List (BitVec 8)) (off len : Nat) : Assertion :=
  (isCreationPtr ↦ₘ (1 : Word)) **
    (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
    (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
    (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x31 ↦ᵣ (next5 - (0 : Word)))

private def convOwnAmbient (isCreationPtr : Word) : Assertion :=
  memOwn isCreationPtr **
    memOwn TeaTypeAddr **
    memOwn TeaInnerAddr **
    regOwn .x5 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 **
    regOwn .x31

private theorem convIs_to_own_ambient (isCreationPtr next5 : Word)
    (bs : List (BitVec 8)) (off len : Nat) :
    ∀ (st : PartialState), convIsAmbient isCreationPtr next5 bs off len st →
      convOwnAmbient isCreationPtr st := by
  intro st hp
  simp only [convIsAmbient, convOwnAmbient] at hp ⊢
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

/-- Ambient Assumed post footprint (matches ExtractAssumedAmbient.success_flat post). -/
def extractAssumedPostAmbient (ret spVal : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (regionBase toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
    stackFree spVal nExtractStackDwords **
    (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
    (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
    (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

/-- Ambient Assumed pre footprint. -/
def extractAssumedPreAmbient (ret spVal loadPtr lenW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (regionBase toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
    stackFree spVal nExtractStackDwords **
    (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
    (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
    (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
    (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

theorem creationPost_to_assumed_ambient
    (sp0 : Word) (s : ExtractSaved)
    (regionBase toBuf isCreationPtr next5 : Word)
    (bs : List (BitVec 8)) (off len : Nat) :
    ∀ h, creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
        bs off len h →
      extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs h := by
  intro h hp
  simp only [creationE2EPostAmbient, creExtraTemps] at hp
  have hp1 : (keepPartAmbient sp0 s regionBase toBuf bs **
      convIsAmbient isCreationPtr next5 bs off len) h := by
    simp only [keepPartAmbient, convIsAmbient]
    xperm_hyp hp
  obtain ⟨hk, hc, hd, hu, hKeep, hConv⟩ := hp1
  have hConv' := convIs_to_own_ambient isCreationPtr next5 bs off len hc hConv
  have hJoined : (keepPartAmbient sp0 s regionBase toBuf bs **
      convOwnAmbient isCreationPtr) h :=
    ⟨hk, hc, hd, hu, hKeep, hConv'⟩
  simp only [keepPartAmbient, convOwnAmbient, extractAssumedPostAmbient,
    teaScratchOwn] at hJoined ⊢
  xperm_hyp hJoined

theorem creationPostEx_to_assumed_ambient
    (sp0 : Word) (s : ExtractSaved)
    (regionBase toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat) :
    ∀ h, (∃ next5 : Word,
        creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
          bs off len h) →
      extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs h := by
  intro h ⟨next5, hp⟩
  exact creationPost_to_assumed_ambient sp0 s regionBase toBuf isCreationPtr
    next5 bs off len h hp

def creationE2EPreAmbient (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
    frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
    (prologueAbiRest loadPtr lenW toBuf isCreationPtr
      old5 old6 old7 old14 old15 old16) **
    extractToBufOwn toBuf ** memOwn isCreationPtr **
    frontExtraAmbientAmb regionBase bs

def assumedPreConcreteAmbient (ret sp0 : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
    (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
    (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
    (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
theorem assumedPreConcrete_to_e2e_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12)) :
    ∀ h, assumedPreConcreteAmbient s.ra sp0 s regionBase loadPtr lenW
        toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs h →
      creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf
        isCreationPtr old5 old6 old7 old14 old15 old16 bs h := by
  intro h hp
  simp only [assumedPreConcreteAmbient, creationE2EPreAmbient, prologueAbiRest,
    frontExtraAmbientAmb, teaScratchOwn, regsAt_extractFrame s] at hp ⊢
  have heq := stackFree10_eq_frameSlotsOwn sp0 spC hspC
  simp only [heq] at hp
  xperm_hyp hp

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_concrete_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : cpsTripleWithin nFrontCreationStepsShort E s.ra extractLinkedCode
      (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf
        isCreationPtr old5 old6 old7 old14 old15 old16 bs)
      (fun h => ∃ next5 : Word,
        creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
          bs off len h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (assumedPreConcreteAmbient s.ra sp0 s regionBase loadPtr lenW toBuf
        isCreationPtr old5 old6 old7 old14 old15 old16 bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  have h1 := cpsTripleWithin_mono_nSteps nFrontCreationStepsShort_le_nExtract hE2E
  refine cpsTripleWithin_weaken
    (fun st hp => assumedPreConcrete_to_e2e_ambient sp0 spC s regionBase loadPtr
      lenW toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs hspC st hp)
    (fun st hq => creationPostEx_to_assumed_ambient sp0 s regionBase toBuf
      isCreationPtr bs off len st hq) h1

private theorem of_forall_regOwn6_amb
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

private def assumedCoreAmbient (sp0 : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
    (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_temps_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCreationStepsShort E s.ra extractLinkedCode
        (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf
          isCreationPtr old5 old6 old7 old14 old15 old16 bs)
        (fun h => ∃ next5 : Word,
          creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
            bs off len h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  let Q := extractAssumedPostAmbient s.ra sp0
    s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
    regionBase toBuf isCreationPtr bs
  let Core := assumedCoreAmbient sp0 s regionBase loadPtr lenW toBuf
    isCreationPtr bs
  have htemps : cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (Core ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16) Q := by
    refine of_forall_regOwn6_amb (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x14) (r5 := .x15) (r6 := .x16) (fun old5 old6 old7 old14 old15 old16 => ?_)
    have hc := extractAssumed_creation_concrete_ambient sp0 spC s regionBase
      loadPtr lenW toBuf isCreationPtr old5 old6 old7 old14 old15 old16
      bs off len hspC (hE2E old5 old6 old7 old14 old15 old16)
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Core, assumedCoreAmbient, assumedPreConcreteAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Q] at hq ⊢; exact hq) hc
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [extractAssumedPreAmbient] at hp ⊢
    dsimp [Core, assumedCoreAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp [Q] at hq ⊢; exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_of_front_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hFront : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCreationStepsShort E s.ra extractLinkedCode
        ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
          frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
          prologueAbiRest loadPtr lenW toBuf isCreationPtr
            old5 old6 old7 old14 old15 old16 **
          extractToBufOwn toBuf ** memOwn isCreationPtr **
          frontExtraAmbientAmb regionBase bs)
        (fun h => ∃ next5 : Word,
          creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
            bs off len h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_creation_temps_ambient sp0 spC s regionBase loadPtr lenW
    toBuf isCreationPtr bs off len hspC (fun old5 old6 old7 old14 old15 old16 => by
      have h := hFront old5 old6 old7 old14 old15 old16
      simpa only [creationE2EPreAmbient] using h)

#print axioms creationPost_to_assumed_ambient
#print axioms extractAssumed_creation_of_front_ambient

theorem nFrontCreationSteps_le_nExtract :
    nFrontCreationSteps ≤ nExtractSteps := by
  simp only [nFrontCreationSteps, nExtractSteps, nTypeSteps]
  omega

theorem nFrontCreationStepsLong_le_nFront
    (lol : Nat) (hlol : lol ≤ 8) :
    nFrontCreationStepsLong lol ≤ nFrontCreationSteps := by
  simp only [nFrontCreationStepsLong, nFrontCreationSteps, nTypeSteps]
  omega

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_concrete_long_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : cpsTripleWithin nFrontCreationSteps E s.ra extractLinkedCode
      (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf
        isCreationPtr old5 old6 old7 old14 old15 old16 bs)
      (fun h => ∃ next5 : Word,
        creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
          bs off len h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (assumedPreConcreteAmbient s.ra sp0 s regionBase loadPtr lenW toBuf
        isCreationPtr old5 old6 old7 old14 old15 old16 bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  have h1 := cpsTripleWithin_mono_nSteps nFrontCreationSteps_le_nExtract hE2E
  refine cpsTripleWithin_weaken
    (fun st hp => assumedPreConcrete_to_e2e_ambient sp0 spC s regionBase loadPtr
      lenW toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs hspC st hp)
    (fun st hq => creationPostEx_to_assumed_ambient sp0 s regionBase toBuf
      isCreationPtr bs off len st hq) h1

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_temps_long_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCreationSteps E s.ra extractLinkedCode
        (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf
          isCreationPtr old5 old6 old7 old14 old15 old16 bs)
        (fun h => ∃ next5 : Word,
          creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
            bs off len h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  let Q := extractAssumedPostAmbient s.ra sp0
    s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
    regionBase toBuf isCreationPtr bs
  let Core := assumedCoreAmbient sp0 s regionBase loadPtr lenW toBuf
    isCreationPtr bs
  have htemps : cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (Core ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16) Q := by
    refine of_forall_regOwn6_amb (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x14) (r5 := .x15) (r6 := .x16) (fun old5 old6 old7 old14 old15 old16 => ?_)
    have hc := extractAssumed_creation_concrete_long_ambient sp0 spC s regionBase
      loadPtr lenW toBuf isCreationPtr old5 old6 old7 old14 old15 old16
      bs off len hspC (hE2E old5 old6 old7 old14 old15 old16)
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Core, assumedCoreAmbient, assumedPreConcreteAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Q] at hq ⊢; exact hq) hc
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [extractAssumedPreAmbient] at hp ⊢
    dsimp [Core, assumedCoreAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp [Q] at hq ⊢; exact hq) htemps

set_option maxRecDepth 8000 in
/-- Long-budget ambient of_front (nFrontCreationSteps). -/
theorem extractAssumed_creation_of_front_long_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hFront : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCreationSteps E s.ra extractLinkedCode
        ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
          frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
          prologueAbiRest loadPtr lenW toBuf isCreationPtr
            old5 old6 old7 old14 old15 old16 **
          extractToBufOwn toBuf ** memOwn isCreationPtr **
          frontExtraAmbientAmb regionBase bs)
        (fun h => ∃ next5 : Word,
          creationE2EPostAmbient sp0 s regionBase toBuf isCreationPtr next5
            bs off len h)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_creation_temps_long_ambient sp0 spC s regionBase loadPtr lenW
    toBuf isCreationPtr bs off len hspC (fun old5 old6 old7 old14 old15 old16 => by
      have h := hFront old5 old6 old7 old14 old15 old16
      simpa only [creationE2EPreAmbient] using h)

#print axioms extractAssumed_creation_of_front_long_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
