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

/-- Matches private `nFrontCreationSteps` in TopFrontE2E. -/
def nFrontCreationSteps' : Nat :=
  (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) + ((1 + 81) + (1 + (1 + 1)))) +
    (((((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
            (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)))

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

theorem nFrontCreation_le_nExtract : nFrontCreationSteps' ≤ nExtractSteps := by
  simp only [nFrontCreationSteps', nExtractSteps, nTypeSteps]
  omega

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

#print axioms nFrontCreation_le_nExtract
#print axioms nFrontCopy_le_nExtract
#print axioms creationPost_to_assumed
#print axioms creationPostEx_to_assumed

end EvmAsm.Codegen.TxExtractToAddressSpec
