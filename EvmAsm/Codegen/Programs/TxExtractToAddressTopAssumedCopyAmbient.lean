/-
  Ambient Assumed packaging for type234 short 20B copy (region partition).
  Split loadPtr/regionBase; bare extractAssumedPostAmbient (no contentDwords).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2ECopyShortConcreteAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwnedAmbient
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
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch txSlice ambientAbsOff)
open EvmAsm.Rv64.RLP (rlpItemDecode)

theorem nFrontCopyStepsShortRegionAmbient_le_nExtract :
    nFrontCopyStepsShortRegionAmbient ≤ nExtractSteps := by
  simp only [nFrontCopyStepsShortRegionAmbient, nExtractSteps, nTypeSteps]
  omega

private theorem regIs_to_regOwn_c (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h :=
  fun _ hx => ⟨v, hx⟩

/-- Flat E2E copy post ambient (matches FrontE2ECopyShortConcreteAmbient). -/
def copyE2EPostAmbient (sp0 : Word) (s : ExtractSaved)
    (regionBase toBuf isCreationPtr contentPtr w2 : Word)
    (bs : List (BitVec 8)) (off len : Nat) : Assertion :=
  (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
    stackFree sp0 nExtractStackDwords **
    (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion regionBase bs **
    extractToBufOwn toBuf **
    (isCreationPtr ↦ₘ (0 : Word)) **
    (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
    (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
    (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x5 ↦ᵣ (extractWord32 w2
        (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
    (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
    (.x31 ↦ᵣ contentPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30

private def copyKeepAmbient (sp0 : Word) (s : ExtractSaved)
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
    regOwn .x28 ** regOwn .x29 ** regOwn .x30

private def copyConvIsAmbient (isCreationPtr contentPtr w2 : Word)
    (bs : List (BitVec 8)) (off len : Nat) : Assertion :=
  (isCreationPtr ↦ₘ (0 : Word)) **
    (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
    (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
    (.x5 ↦ᵣ (extractWord32 w2
        (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
    (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
    (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
    (.x31 ↦ᵣ contentPtr)

private def copyConvOwnAmbient (isCreationPtr : Word) : Assertion :=
  memOwn isCreationPtr **
    memOwn TeaTypeAddr **
    memOwn TeaInnerAddr **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x31

private theorem copyConvIs_to_own_ambient (isCreationPtr contentPtr w2 : Word)
    (bs : List (BitVec 8)) (off len : Nat) :
    ∀ (st : PartialState), copyConvIsAmbient isCreationPtr contentPtr w2 bs off len st →
      copyConvOwnAmbient isCreationPtr st := by
  intro st hp
  simp only [copyConvIsAmbient, copyConvOwnAmbient] at hp ⊢
  obtain ⟨a1, a2, ad, au, his, rest1⟩ := hp
  obtain ⟨b1, b2, bd, bu, hteaT, rest2⟩ := rest1
  obtain ⟨c1, c2, cd, cu, hteaI, rest3⟩ := rest2
  obtain ⟨d1, d2, dd, du, hx5, rest4⟩ := rest3
  obtain ⟨e1, e2, ed, eu, hx6, rest5⟩ := rest4
  obtain ⟨f1, f2, fd, fu, hx7, rest6⟩ := rest5
  obtain ⟨g1, g2, gd, gu, hx11, rest7⟩ := rest6
  obtain ⟨h1, h2, hd, hu, hx12, hx31⟩ := rest7
  exact ⟨a1, a2, ad, au, memIs_implies_memOwn _ his,
    b1, b2, bd, bu, memIs_implies_memOwn _ hteaT,
    c1, c2, cd, cu, memIs_implies_memOwn _ hteaI,
    d1, d2, dd, du, regIs_to_regOwn_c .x5 _ _ hx5,
    e1, e2, ed, eu, regIs_to_regOwn_c .x6 _ _ hx6,
    f1, f2, fd, fu, regIs_to_regOwn_c .x7 _ _ hx7,
    g1, g2, gd, gu, regIs_to_regOwn_c .x11 _ _ hx11,
    h1, h2, hd, hu, regIs_to_regOwn_c .x12 _ _ hx12,
    regIs_to_regOwn_c .x31 _ _ hx31⟩

set_option maxRecDepth 8000 in
theorem copyPost_to_assumed_ambient
    (sp0 : Word) (s : ExtractSaved)
    (regionBase toBuf isCreationPtr contentPtr w2 : Word)
    (bs : List (BitVec 8)) (off len : Nat) :
    ∀ h, copyE2EPostAmbient sp0 s regionBase toBuf isCreationPtr contentPtr w2
        bs off len h →
      extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs h := by
  intro h hp
  simp only [copyE2EPostAmbient] at hp
  have hp1 : (copyKeepAmbient sp0 s regionBase toBuf bs **
      copyConvIsAmbient isCreationPtr contentPtr w2 bs off len) h := by
    simp only [copyKeepAmbient, copyConvIsAmbient]
    xperm_hyp hp
  obtain ⟨hk, hc, hd, hu, hKeep, hConv⟩ := hp1
  have hConv' := copyConvIs_to_own_ambient isCreationPtr contentPtr w2 bs off len hc hConv
  have hJoined : (copyKeepAmbient sp0 s regionBase toBuf bs **
      copyConvOwnAmbient isCreationPtr) h :=
    ⟨hk, hc, hd, hu, hKeep, hConv'⟩
  simp only [copyKeepAmbient, copyConvOwnAmbient, extractAssumedPostAmbient,
    teaScratchOwn] at hJoined ⊢
  xperm_hyp hJoined

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_concrete_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr contentPtr w2 : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : cpsTripleWithin nFrontCopyStepsShortRegionAmbient E s.ra extractLinkedCode
      (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf
        isCreationPtr old5 old6 old7 old14 old15 old16 bs)
      (copyE2EPostAmbient sp0 s regionBase toBuf isCreationPtr contentPtr w2
        bs off len)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (assumedPreConcreteAmbient s.ra sp0 s regionBase loadPtr lenW toBuf
        isCreationPtr old5 old6 old7 old14 old15 old16 bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  have h1 := cpsTripleWithin_mono_nSteps nFrontCopyStepsShortRegionAmbient_le_nExtract hE2E
  refine cpsTripleWithin_weaken
    (fun st hp => assumedPreConcrete_to_e2e_ambient sp0 spC s regionBase loadPtr
      lenW toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs hspC st hp)
    (fun st hq => copyPost_to_assumed_ambient sp0 s regionBase toBuf isCreationPtr
      contentPtr w2 bs off len st hq) h1

private theorem of_forall_regOwn6_c
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

private def assumedCoreCopyAmbient (sp0 : Word) (s : ExtractSaved)
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
theorem extractAssumed_copy_temps_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr contentPtr w2 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hE2E : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCopyStepsShortRegionAmbient E s.ra extractLinkedCode
        (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf
          isCreationPtr old5 old6 old7 old14 old15 old16 bs)
        (copyE2EPostAmbient sp0 s regionBase toBuf isCreationPtr contentPtr w2
          bs off len)) :
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
  let Core := assumedCoreCopyAmbient sp0 s regionBase loadPtr lenW toBuf
    isCreationPtr bs
  have htemps : cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (Core ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16) Q := by
    refine of_forall_regOwn6_c (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x14) (r5 := .x15) (r6 := .x16) (fun old5 old6 old7 old14 old15 old16 => ?_)
    have hc := extractAssumed_copy_concrete_ambient sp0 spC s regionBase
      loadPtr lenW toBuf isCreationPtr contentPtr w2 old5 old6 old7 old14 old15 old16
      bs off len hspC (hE2E old5 old6 old7 old14 old15 old16)
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Core, assumedCoreCopyAmbient, assumedPreConcreteAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Q] at hq ⊢; exact hq) hc
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [extractAssumedPreAmbient] at hp ⊢
    dsimp [Core, assumedCoreCopyAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp [Q] at hq ⊢; exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_of_front_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr contentPtr w2 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hFront : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin nFrontCopyStepsShortRegionAmbient E s.ra extractLinkedCode
        ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
          frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
          prologueAbiRest loadPtr lenW toBuf isCreationPtr
            old5 old6 old7 old14 old15 old16 **
          extractToBufOwn toBuf ** memOwn isCreationPtr **
          frontExtraAmbientAmb regionBase bs)
        (copyE2EPostAmbient sp0 s regionBase toBuf isCreationPtr contentPtr w2
          bs off len)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  extractAssumed_copy_temps_ambient sp0 spC s regionBase loadPtr lenW
    toBuf isCreationPtr contentPtr w2 bs off len hspC
    (fun old5 old6 old7 old14 old15 old16 => by
      have h := hFront old5 old6 old7 old14 old15 old16
      simpa only [creationE2EPreAmbient] using h)

#print axioms copyPost_to_assumed_ambient
#print axioms extractAssumed_copy_of_front_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
