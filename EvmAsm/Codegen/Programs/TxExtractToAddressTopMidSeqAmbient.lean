/-
  Ambient dual of MidSeq wn0 CallOk of_decode + ToWn0 under midOwned.
  Split bases: loadPtr / regionBase + absOff.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext0Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopType234Ambient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

set_option maxRecDepth 8000 in
theorem extractWalkNext0Call_owned_outcome_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff < bs.length)
    (hover : regionBase.toNat + absOff < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff) = true)
    (hss : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        absOff + 1 < bs.length ∧ regionBase.toNat + (absOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
      (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
          (regionBase + BitVec.ofNat 64 absOff) endPtr bs **
        midOwned spC s toBuf isCreationPtr s7)
      (wn0StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        wn0CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext0Call_type234_outcome_ambient loadPtr regionBase
    lenW typeW innerW endPtr bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext0OkNested_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      (wn0StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        wn0CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext0OkNested_bne_ambient loadPtr regionBase
    lenW typeW innerW endPtr bs absOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext0CallOk_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff < bs.length)
    (hover : regionBase.toNat + absOff < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff) = true)
    (hss : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        absOff + 1 < bs.length ∧ regionBase.toNat + (absOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hdec : ∃ next0 len0 : Word,
      rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
        endPtr next0 len0)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 absOff) endPtr = true) :
    cpsTripleWithin ((1 + 87) + 1) WalkNext0JalPc AfterWalkNext0Bne extractLinkedCode
      (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
          (regionBase + BitVec.ofNat 64 absOff) endPtr bs **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next0 len0 : Word,
        (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next0 len0
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hCall := extractWalkNext0Call_owned_outcome_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr toBuf isCreationPtr s7 bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hCall2 :
      cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
        (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
            (regionBase + BitVec.ofNat 64 absOff) endPtr bs **
          midOwned spC s toBuf isCreationPtr s7)
        (wn0StableAmbient loadPtr lenW typeW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          wn0CommonAmbient regionBase bs **
          rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode regionBase endPtr bs absOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hCall
  have hOk := extractWalkNext0OkNested_owned_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr toBuf isCreationPtr s7 bs absOff
  exact cpsTripleWithin_seq_same_cr hCall2 hOk

set_option maxRecDepth 8000 in
theorem extractType234ToWn0Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff0 : Nat)
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
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff0) endPtr = true) :
    cpsTripleWithin
      (((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1))
      AfterSaveCursor AfterWalkNext0Bne extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next0 len0 : Word,
        (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next0 len0
          bs absOff0 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hBr := extractType234ToWalkNext0_ambient loadPtr regionBase
    lenW typeW innerW cursor endPtr bs hne0 hne1
  have hBr2 :
      cpsTripleWithin ((1 + (1 + (1 + 1))) + (1 + 1))
        AfterSaveCursor WalkNext0JalPc extractLinkedCode
        (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
            cursor endPtr bs **
          (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
          midOwned spC s toBuf isCreationPtr s7)
        (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
            (regionBase + BitVec.ofNat 64 absOff0) endPtr bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    have hBrF := cpsTripleWithin_frameR
      (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) hBr
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by
      simp only [hcur] at hq
      xperm_hyp hq) hBrF
  have hOk := extractWalkNext0CallOk_owned_of_decode_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr toBuf isCreationPtr s7 bs absOff0
    hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  exact cpsTripleWithin_seq_same_cr hBr2 hOk

#print axioms extractWalkNext0CallOk_owned_of_decode_ambient
#print axioms extractType234ToWn0Ok_owned_of_decode_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
