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
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext1Ambient
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

set_option maxRecDepth 8000 in
theorem extractWalkNext1Prep_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext0Bne WalkNext1JalPc extractLinkedCode
      (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
          bs absOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn1StableAmbient loadPtr lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext1Prep_framed_ambient loadPtr regionBase
    lenW typeW innerW endPtr next len bs absOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext1Call_owned_a2_outcome_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
    cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 extractLinkedCode
      (wn1StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7)
      (wn1StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        wn1CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext1Call_type234_a2_outcome_ambient loadPtr regionBase
    lenW typeW innerW endPtr a2Old bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext1OkNested_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne extractLinkedCode
      (wn1StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        wn1CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext1OkNested_bne_ambient loadPtr regionBase
    lenW typeW innerW endPtr bs absOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext1PrepCallOk_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff0 absOff1 : Nat)
    (hnext : next = regionBase + BitVec.ofNat 64 absOff1)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff1 < bs.length)
    (hover : regionBase.toNat + absOff1 < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff1) = true)
    (hss : ¬ BitVec.ult ((bs[absOff1]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        absOff1 + 1 < bs.length ∧ regionBase.toNat + (absOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[absOff1]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff1]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff1]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff1 + 1 + ((bs[absOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff1 + 1 +
          ((bs[absOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff1 + 1 + k)) = true)
    (hdec : ∃ next1 len1 : Word,
      rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
        endPtr next1 len1)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 absOff1) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
      (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
          bs absOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next1 len1 : Word,
        (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next1 len1
          bs absOff1 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPrep := extractWalkNext1Prep_owned_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr next len toBuf isCreationPtr s7 bs absOff0
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterWalkNext0Bne WalkNext1JalPc extractLinkedCode
        (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
            bs absOff0 **
          midOwned spC s toBuf isCreationPtr s7)
        (wn1StableAmbient loadPtr lenW typeW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff1) **
          (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff1)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion regionBase bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractWalkNext1Call_owned_a2_outcome_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr len toBuf isCreationPtr s7 bs absOff1
    hsalign hoff hover hvalid hss hls hll
  have hPC := cpsTripleWithin_seq_same_cr hPrep2 hCall
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterWalkNext0Bne LinkWalkNext1 extractLinkedCode
        (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next len
            bs absOff0 **
          midOwned spC s toBuf isCreationPtr s7)
        (wn1StableAmbient loadPtr lenW typeW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff1) **
          wn1CommonAmbient regionBase bs **
          rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff1) endPtr bs absOff1 **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode regionBase endPtr bs absOff1
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractWalkNext1OkNested_owned_ambient spC s loadPtr regionBase
    lenW typeW innerW endPtr toBuf isCreationPtr s7 bs absOff1
  exact cpsTripleWithin_seq_same_cr hPC2 hOk

#print axioms extractWalkNext1PrepCallOk_owned_of_decode_ambient

set_option maxRecDepth 8000 in
/-- AfterSave → AfterWalkNext1Bne under ambient midOwned (of_decode). -/
theorem extractType234ToWn1Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff0 absOff1 : Nat)
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
    (hnext1 : ∀ next0 len0 : Word,
      rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
        endPtr next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 absOff1) :
    cpsTripleWithin
      (((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)))
      AfterSaveCursor AfterWalkNext1Bne extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next1 len1 : Word,
        (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next1 len1
          bs absOff1 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h0 := extractType234ToWn0Ok_owned_of_decode_ambient spC s loadPtr regionBase
    lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 bs absOff0
    hcur hne0 hne1 hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  have h1 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
        (fun h => ∃ next0 len0 : Word,
          (wn0OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next0 len0
            bs absOff0 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next1 len1 : Word,
          (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next1 len1
            bs absOff1 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next0 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len0 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterWalkNext0Bne AfterWalkNext1Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
              endPtr next0 len0⌝ **
            (wn0OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr next0 len0
              bs absOff0 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next1 len1 : Word,
            (wn1OkConcreteAmbient loadPtr regionBase lenW typeW innerW endPtr next1 len1
              bs absOff1 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractWalkNext1PrepCallOk_owned_of_decode_ambient spC s
        loadPtr regionBase lenW typeW innerW endPtr next0 len0 toBuf isCreationPtr s7
        bs absOff0 absOff1
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
          (wn0OkRegsAmbient loadPtr regionBase lenW typeW innerW endPtr next0 len0
            bs absOff0 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  exact cpsTripleWithin_seq_same_cr h0 h1

#print axioms extractType234ToWn1Ok_owned_of_decode_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
