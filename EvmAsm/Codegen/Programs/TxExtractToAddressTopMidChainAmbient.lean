/-
  Ambient dual of type234 MidChain ToWn5 of_decode.
  Split bases: loadPtr for s0; regionBase+absOff for blob/cursor.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidSeqAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext5Ambient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

set_option maxRecDepth 8000 in
/-- AfterSave → AfterWalkNext5Bne under ambient midOwned (of_decode). -/
theorem extractType234ToWn5Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8))
    (absOff0 absOff1 absOff2 absOff3 absOff4 absOff5 : Nat)
    (hcur : cursor = regionBase + BitVec.ofNat 64 absOff0)
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1)
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
        endPtr next3 len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff3) endPtr = true)
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
        endPtr next4 len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff4) endPtr = true)
    (hoff5 : absOff5 < bs.length)
    (hover5 : regionBase.toNat + absOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        absOff5 + 1 < bs.length ∧ regionBase.toNat + (absOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[absOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        absOff5 + 1 + ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff5 + 1 +
          ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff5 + 1 + k)) = true)
    (hdec5 : ∃ next5 len5 : Word,
      rlpItemDecode bs absOff5 (regionBase + BitVec.ofNat 64 absOff5)
        endPtr next5 len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff5) endPtr = true)
    (hnext1 : ∀ next0 len0 : Word,
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        endPtr next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1)
    (hnext2 : ∀ next1 len1 : Word,
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        endPtr next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 absOff2)
    (hnext3 : ∀ next2 len2 : Word,
      rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
        endPtr next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 absOff3)
    (hnext4 : ∀ next3 len3 : Word,
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        endPtr next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 absOff4)
    (hnext5 : ∀ next4 len4 : Word,
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        endPtr next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 absOff5)
  :
    cpsTripleWithin ((((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1)) + (((1 + (1 + 1)) + (1 + 87)) + 1))
      AfterSaveCursor AfterWalkNext5Bne extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next5 len5 : Word,
        (wn5OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next5 len5
          bs absOff5 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h0 := extractType234ToWn0Ok_owned_of_decode_ambient spC s loadPtr regionBase
    lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 bs absOff0
    hcur hne0 hne1 hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  have h1 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
        (fun h => ∃ next0 len0 : Word,
          (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next0 len0 bs absOff0 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next1 len1 : Word,
          (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next1 len1 bs absOff1 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next0 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len0 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
              endPtr next0 len0⌝ **
            (wn0OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
              next0 len0 bs absOff0 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next1 len1 : Word,
            (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
              next1 len1 bs absOff1 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractWalkNext1PrepCallOk_owned_of_decode_ambient spC s
        loadPtr regionBase lenW typeW innerW endPtr next0 len0
        toBuf isCreationPtr s7 bs absOff0 absOff1
        (hnext1 next0 len0 hdecN) hsalign
        hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW
            endPtr next0 len0 bs absOff0 h1 := by
          simp only [wn0OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [wn0OkConcreteAmbient] using hOkC)
      have hRest :
          (wn0OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
            next0 len0 bs absOff0 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure

  have h2 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext1Bne AfterWalkNext2Bne extractLinkedCode
        (fun h => ∃ next1 len1 : Word,
          (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next1 len1 bs absOff1 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next2 len2 : Word,
          (wn2OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next2 len2 bs absOff2 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next1 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len1 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterWalkNext1Bne AfterWalkNext2Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
              endPtr next1 len1⌝ **
            (wn1OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
              next1 len1 bs absOff1 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next2 len2 : Word,
            (wn2OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
              next2 len2 bs absOff2 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractWalkNext2PrepCallOk_owned_of_decode_ambient spC s
        loadPtr regionBase lenW typeW innerW endPtr next1 len1
        toBuf isCreationPtr s7 bs absOff1 absOff2
        (hnext2 next1 len1 hdecN) hsalign
        hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW
            endPtr next1 len1 bs absOff1 h1 := by
          simp only [wn1OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [wn1OkConcreteAmbient] using hOkC)
      have hRest :
          (wn1OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
            next1 len1 bs absOff1 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure

  have h3 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext2Bne AfterWalkNext3Bne extractLinkedCode
        (fun h => ∃ next2 len2 : Word,
          (wn2OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next2 len2 bs absOff2 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next3 len3 : Word,
          (wn3OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next3 len3 bs absOff3 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next2 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len2 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterWalkNext2Bne AfterWalkNext3Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
              endPtr next2 len2⌝ **
            (wn2OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
              next2 len2 bs absOff2 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next3 len3 : Word,
            (wn3OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
              next3 len3 bs absOff3 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractWalkNext3PrepCallOk_owned_of_decode_ambient spC s
        loadPtr regionBase lenW typeW innerW endPtr next2 len2
        toBuf isCreationPtr s7 bs absOff2 absOff3
        (hnext3 next2 len2 hdecN) hsalign
        hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : wn2OkConcreteAmbient loadPtr regionBase lenW typeW innerW
            endPtr next2 len2 bs absOff2 h1 := by
          simp only [wn2OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [wn2OkConcreteAmbient] using hOkC)
      have hRest :
          (wn2OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
            next2 len2 bs absOff2 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure

  have h4 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext3Bne AfterWalkNext4Bne extractLinkedCode
        (fun h => ∃ next3 len3 : Word,
          (wn3OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next3 len3 bs absOff3 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next4 len4 : Word,
          (wn4OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next4 len4 bs absOff4 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next3 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len3 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterWalkNext3Bne AfterWalkNext4Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
              endPtr next3 len3⌝ **
            (wn3OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
              next3 len3 bs absOff3 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next4 len4 : Word,
            (wn4OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
              next4 len4 bs absOff4 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractWalkNext4PrepCallOk_owned_of_decode_ambient spC s
        loadPtr regionBase lenW typeW innerW endPtr next3 len3
        toBuf isCreationPtr s7 bs absOff3 absOff4
        (hnext4 next3 len3 hdecN) hsalign
        hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : wn3OkConcreteAmbient loadPtr regionBase lenW typeW innerW
            endPtr next3 len3 bs absOff3 h1 := by
          simp only [wn3OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [wn3OkConcreteAmbient] using hOkC)
      have hRest :
          (wn3OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
            next3 len3 bs absOff3 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure

  have h5 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext4Bne AfterWalkNext5Bne extractLinkedCode
        (fun h => ∃ next4 len4 : Word,
          (wn4OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next4 len4 bs absOff4 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next5 len5 : Word,
          (wn5OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
            next5 len5 bs absOff5 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next4 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len4 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterWalkNext4Bne AfterWalkNext5Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
              endPtr next4 len4⌝ **
            (wn4OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
              next4 len4 bs absOff4 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next5 len5 : Word,
            (wn5OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr
              next5 len5 bs absOff5 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractWalkNext5PrepCallOk_owned_of_decode_ambient spC s
        loadPtr regionBase lenW typeW innerW endPtr next4 len4
        toBuf isCreationPtr s7 bs absOff4 absOff5
        (hnext5 next4 len4 hdecN) hsalign
        hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : wn4OkConcreteAmbient loadPtr regionBase lenW typeW innerW
            endPtr next4 len4 bs absOff4 h1 := by
          simp only [wn4OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [wn4OkConcreteAmbient] using hOkC)
      have hRest :
          (wn4OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr
            next4 len4 bs absOff4 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure

  have h01 := cpsTripleWithin_seq_same_cr h0 h1
  have h012 := cpsTripleWithin_seq_same_cr h01 h2
  have h0123 := cpsTripleWithin_seq_same_cr h012 h3
  have h01234 := cpsTripleWithin_seq_same_cr h0123 h4
  exact cpsTripleWithin_seq_same_cr h01234 h5

#print axioms extractType234ToWn5Ok_owned_of_decode_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
