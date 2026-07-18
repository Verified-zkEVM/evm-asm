/-
  Ambient legacy MidJoin: AfterSave → creation under pure decode (split loadPtr/regionBase).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwnedLegacyAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacyWalkRestAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

theorem leg3Exists_to_creation_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff3 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcre : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        endPtr next3 len3 → len3 = (0 : Word)) :
    cpsTripleWithin
      ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11))
      AfterLegacyWalk3Bne s.ra extractLinkedCode
      (fun h => ∃ next3 len3 : Word,
        (leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next3 len3
            bs absOff3 **
          midOwned spC s toBuf isCreationPtr s7) h)
      (fun h => ∃ next3 : Word,
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
          (.x31 ↦ᵣ (next3 - (0 : Word))) **
          creExtraTemps) h) := by
  refine cpsTripleWithin_exists_pre_gen (fun next3 => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len3 => ?_)
  have h := extractLegacyHaveFieldCreation_then_epi_ambient sp0 spC s loadPtr
    regionBase lenW innerW endPtr next3 toBuf isCreationPtr s7 bs absOff3
    hspC hret
  refine cpsTripleWithin_weaken (fun hst hp => by
    obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
    obtain ⟨hRegs, hdec⟩ := (sepConj_pure_right h1).mp (by
      simpa only [leg3OkConcreteAmbient] using hOkC)
    have hlen : len3 = (0 : Word) := hcre next3 len3 hdec
    have hOk0 : leg3OkConcreteAmbient loadPtr regionBase lenW innerW endPtr
        next3 (0 : Word) bs absOff3 h1 := by
      simp only [leg3OkConcreteAmbient, hlen] at hRegs hdec ⊢
      exact (sepConj_pure_right h1).mpr ⟨hRegs, hdec⟩
    exact ⟨h1, h2, hd, hu, hOk0, hM⟩) (fun _ hq => ⟨next3, hq⟩) h

set_option maxRecDepth 8000 in
theorem extractLegacyAfterSaveCreation_then_epi_of_decode_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8))
    (absOff0 absOff1 absOff2 absOff3 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcur : cursor = regionBase + BitVec.ofNat 64 absOff0)
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
        ∀ j, j < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + j)) = true)
    (hll0 : ¬ BitVec.ult ((bs[absOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        absOff0 + 1 + ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff0 + 1 +
          ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff0 + 1 + j)) = true)
    (hdec0 : ∃ next0 len0 : Word,
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        endPtr next0 len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff0) endPtr = true)
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
        ∀ j, j < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + j)) = true)
    (hll1 : ¬ BitVec.ult ((bs[absOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + j)) = true)
    (hdec1 : ∃ next1 len1 : Word,
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        endPtr next1 len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff1) endPtr = true)
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
        ∀ j, j < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + j)) = true)
    (hll2 : ¬ BitVec.ult ((bs[absOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        absOff2 + 1 + ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff2 + 1 +
          ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff2 + 1 + j)) = true)
    (hdec2 : ∃ next2 len2 : Word,
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        endPtr next2 len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff2) endPtr = true)
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
        ∀ j, j < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + j)) = true)
    (hll3 : ¬ BitVec.ult ((bs[absOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        absOff3 + 1 + ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff3 + 1 +
          ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff3 + 1 + j)) = true)
    (hdec3 : ∃ next3 len3 : Word,
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        endPtr next3 len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff3) endPtr = true)
    (hnext1 : ∀ (next0 len0 : Word),
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        endPtr next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1)
    (hnext2 : ∀ (next1 len1 : Word),
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        endPtr next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2)
    (hnext3 : ∀ (next2 len2 : Word),
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        endPtr next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3)
    (hcre : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        endPtr next3 len3 → len3 = (0 : Word)) :
    cpsTripleWithin
      (((((((1 + 1) + (1 + 1)) + ((1 + 87) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)))
      AfterSaveCursor s.ra extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next3 : Word,
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
          (.x31 ↦ᵣ (next3 - (0 : Word))) **
          creExtraTemps) h) := by
  have hW := extractLegacyToWalk3Ok_owned_of_decode_ambient spC s loadPtr regionBase
    lenW innerW cursor endPtr toBuf isCreationPtr s7 bs
    absOff0 absOff1 absOff2 absOff3
    hcur hsalign
    hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
    hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    hnext1 hnext2 hnext3
  have hC := leg3Exists_to_creation_ambient sp0 spC s loadPtr regionBase lenW
    innerW endPtr toBuf isCreationPtr s7 bs absOff3 hspC hret hcre
  exact cpsTripleWithin_seq_same_cr hW hC

#print axioms leg3Exists_to_creation_ambient
#print axioms extractLegacyAfterSaveCreation_then_epi_of_decode_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
