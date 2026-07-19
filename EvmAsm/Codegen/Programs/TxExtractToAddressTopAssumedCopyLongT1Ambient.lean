/-
  Ambient dual: Assumed long concrete t1 20B copy of_decode (regionBase/loadPtr).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedCopyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressCopyFromRegion
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontE2ECopyLongConcreteT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLongAmbient
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
open EvmAsm.EL.RLP (Nat.fromBytesBE)

theorem nFrontCopyStepsLongT1Region_le_nExtract (lol : Nat) (hlol : lol ≤ 8) :
    nFrontCopyStepsLongT1Region lol ≤ nExtractSteps := by
  simp only [nFrontCopyStepsLongT1Region, nExtractSteps, nTypeSteps]
  omega
  -- lol ≤ 8 ⇒ 7*lol+25 ≤ 81 (= short full walk_init budget)

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_concrete_long_t1_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr contentPtr w2 : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (lol : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hlol : lol ≤ 8)
    (hE2E : cpsTripleWithin (nFrontCopyStepsLongT1Region lol) E s.ra extractLinkedCode
      (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 bs)
      (copyE2EPostAmbient sp0 s regionBase toBuf isCreationPtr contentPtr w2
        bs off len)) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (assumedPreConcreteAmbient s.ra sp0 s regionBase loadPtr lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  have h1 := cpsTripleWithin_mono_nSteps (nFrontCopyStepsLongT1Region_le_nExtract lol hlol) hE2E
  refine cpsTripleWithin_weaken
    (fun st hp => assumedPreConcrete_to_e2e_ambient sp0 spC s regionBase loadPtr
      lenW toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs hspC st hp)
    (fun st hq => copyPost_to_assumed_ambient sp0 s regionBase toBuf isCreationPtr
      contentPtr w2 bs off len st hq) h1

private theorem of_forall_regOwn6_long_legacy_amb
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

private def assumedCoreCopyLongLegacyAmbient (sp0 : Word) (s : ExtractSaved)
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
theorem extractAssumed_copy_temps_long_t1_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr contentPtr w2 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (lol : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hlol : lol ≤ 8)
    (hE2E : ∀ (old5 old6 old7 old14 old15 old16 : Word),
      cpsTripleWithin (nFrontCopyStepsLongT1Region lol) E s.ra extractLinkedCode
        (creationE2EPreAmbient sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 bs)
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
  let Core := assumedCoreCopyLongLegacyAmbient sp0 s regionBase loadPtr lenW toBuf isCreationPtr bs
  have htemps : cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (Core ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16) Q := by
    refine of_forall_regOwn6_long_legacy_amb (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x14) (r5 := .x15) (r6 := .x16) (fun old5 old6 old7 old14 old15 old16 => ?_)
    have hc := extractAssumed_copy_concrete_long_t1_region_ambient sp0 spC s regionBase loadPtr lenW
      toBuf isCreationPtr contentPtr w2 old5 old6 old7 old14 old15 old16
      bs off len lol hspC hlol (hE2E old5 old6 old7 old14 old15 old16)
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp [Core, assumedCoreCopyLongLegacyAmbient, assumedPreConcreteAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp [Q] at hq ⊢; exact hq) hc
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [extractAssumedPreAmbient] at hp ⊢
    dsimp [Core, assumedCoreCopyLongLegacyAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp [Q] at hq ⊢; exact hq) htemps

set_option maxRecDepth 8000 in
/-- Wire Assumed bare under long concrete copy E2E of_decode region. -/
theorem extractAssumed_copy_of_front_long_concrete_t1_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (absOff0 absOff1 absOff2 absOff3 absOff4 q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hwi_off : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hcur : longWalkCursorAmbient regionBase bs (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hwi_off =
        regionBase + BitVec.ofNat 64 absOff0)
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff0 : absOff0 < bs.length)
    (hover0 : regionBase.toNat + absOff0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        absOff0 + 1 < bs.length ∧ regionBase.toNat + (absOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0)
    (hinb0 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff0)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff1 : absOff1 < bs.length)
    (hover1 : regionBase.toNat + absOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        absOff1 + 1 < bs.length ∧ regionBase.toNat + (absOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1)
    (hinb1 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff1)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff2 : absOff2 < bs.length)
    (hover2 : regionBase.toNat + absOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        absOff2 + 1 < bs.length ∧ regionBase.toNat + (absOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2)
    (hinb2 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff2)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff3 : absOff3 < bs.length)
    (hover3 : regionBase.toNat + absOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        absOff3 + 1 < bs.length ∧ regionBase.toNat + (absOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3)
    (hinb3 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff3)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3)
    (hoff4 : absOff4 < bs.length)
    (hover4 : regionBase.toNat + absOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        absOff4 + 1 < bs.length ∧ regionBase.toNat + (absOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4)
    (hinb4 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 absOff4)
    (hlen20 : ∀ (next4 len4 : Word),
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4 →
        len4 = (20 : Word))
    (hnext_content : ∀ (next4 len4 : Word),
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4 →
        next4 = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word))
    (hq : 8 * q + 16 < bs.length)
    (hcover : regionBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat ≤ bs.length)
    (hlover : regionBase.toNat + (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hwi_off1 : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 < bs.length)
    (h_fits : ¬ BitVec.ult
        ((regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
        ((regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1]'hwi_off1).zeroExtend 64 ≠
      (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
            ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
              (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (hlol : ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat ≤ 8) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) := by
  let contentPtr := regionBase + BitVec.ofNat 64 (8 * q)
  let w2 := (contentWordsAt bs q).2.2
  let lol := ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
      (0xf7 : Word)).toNat
  refine extractAssumed_copy_temps_long_t1_region_ambient sp0 spC s regionBase loadPtr lenW toBuf
    isCreationPtr contentPtr w2 bs off len lol hspC hlol
    (fun old5 old6 old7 old14 old15 old16 => ?_)
  have hE := extractFrontCopy_then_epi_of_decode_long_concrete_t1_region_ambient
    sp0 spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len
    absOff0 absOff1 absOff2 absOff3 absOff4 q
    hspC hret htype1 hsalign
    hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
    hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    hnext1 hnext2 hnext3
    hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    hnext4 hlen20 hnext_content
    hq hcover hcvalid htalign htover htvalid hlen hsuccess hover
    hvalidTx0 hptr hbound hspan hoff hinover hinvalid hcur hlistLen_ne h_ge h_ge_f8 hllen hlover hlvalid
    hwi_off1 h_fits h_llz h_min h_match
    old5 old6 old7 old14 old15 old16
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [creationE2EPreAmbient] at hp ⊢
    exact hp) (fun _ hq => by
    dsimp only [copyE2EPostAmbient, contentPtr, w2] at hq ⊢
    simp only [htype1] at hq ⊢
    xperm_hyp hq) hE

set_option maxRecDepth 8000 in
theorem extractAssumed_copy_fullCode_of_decode_long_concrete_t1_region_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (absOff0 absOff1 absOff2 absOff3 absOff4 q : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hwi_off : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hcur : longWalkCursorAmbient regionBase bs (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hwi_off =
        regionBase + BitVec.ofNat 64 absOff0)
    (htype1 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (1 : Word))
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff0 : absOff0 < bs.length)
    (hover0 : regionBase.toNat + absOff0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        absOff0 + 1 < bs.length ∧ regionBase.toNat + (absOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + k)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0)
    (hinb0 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff0)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff1 : absOff1 < bs.length)
    (hover1 : regionBase.toNat + absOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        absOff1 + 1 < bs.length ∧ regionBase.toNat + (absOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1)
    (hinb1 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff1)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff2 : absOff2 < bs.length)
    (hover2 : regionBase.toNat + absOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        absOff2 + 1 < bs.length ∧ regionBase.toNat + (absOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + k)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2)
    (hinb2 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff2)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hoff3 : absOff3 < bs.length)
    (hover3 : regionBase.toNat + absOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        absOff3 + 1 < bs.length ∧ regionBase.toNat + (absOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + k)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3)
    (hinb3 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff3)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3)
    (hoff4 : absOff4 < bs.length)
    (hover4 : regionBase.toNat + absOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        absOff4 + 1 < bs.length ∧ regionBase.toNat + (absOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + k)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4)
    (hinb4 :
      BitVec.ult (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 absOff4)
    (hlen20 : ∀ (next4 len4 : Word),
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4 →
        len4 = (20 : Word))
    (hnext_content : ∀ (next4 len4 : Word),
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) next4 len4 →
        next4 = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word))
    (hq : 8 * q + 16 < bs.length)
    (hcover : regionBase.toNat + (8 * q + 16) < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (regionBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidTx0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat ≤ bs.length)
    (hlover : regionBase.toNat + (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hwi_off1 : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 < bs.length)
    (h_fits : ¬ BitVec.ult
        ((regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
        ((regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1]'hwi_off1).zeroExtend 64 ≠
      (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
            ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
              (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64 (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (hlol : ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat ≤ 8) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPreAmbient s.ra sp0 loadPtr lenW
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs)
      (extractAssumedPostAmbient s.ra sp0
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7
        regionBase toBuf isCreationPtr bs) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_copy_of_front_long_concrete_t1_region_ambient sp0 spC s
      regionBase loadPtr lenW toBuf isCreationPtr bs off len
      absOff0 absOff1 absOff2 absOff3 absOff4 q
      hspC hret hwi_off hcur htype1 hsalign
      hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
      hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
      hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
      hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
      hnext1 hnext2 hnext3
      hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      hnext4 hlen20 hnext_content
      hq hcover hcvalid htalign htover htvalid hlen hsuccess hover
      hvalidTx0 hptr hbound hspan hoff hinover hinvalid hlistLen_ne h_ge h_ge_f8 hllen hlover hlvalid
      hwi_off1 h_fits h_llz h_min h_match hlol)

#print axioms extractAssumed_copy_of_front_long_concrete_t1_region_ambient
#print axioms extractAssumed_copy_fullCode_of_decode_long_concrete_t1_region_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
