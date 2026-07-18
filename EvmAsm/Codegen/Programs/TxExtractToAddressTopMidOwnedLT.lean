/-
  midOwned frames for legacy + t1 walk chains.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressTopT1
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen


set_option maxRecDepth 8000 in
theorem extractLegacyLoadArgs_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) LegacyStart LegacyWalk0JalPc extractLinkedCode
      (legacyStartFrame txBase lenW innerW cursor endPtr txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legacyStartFrame txBase lenW innerW cursor endPtr txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyLoadArgs_framed txBase lenW innerW cursor endPtr txBytes
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk0Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg0Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk0Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk0OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        leg0Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractLegacyWalk0OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk1Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk0Bne LegacyWalk1JalPc extractLinkedCode
      (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk1Prep_framed txBase lenW innerW endPtr next len txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk1Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk1JalPc LinkLegacyWalk1 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg1Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk1Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk1OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk1 AfterLegacyWalk1Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        leg1Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractLegacyWalk1OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk2Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk1Bne LegacyWalk2JalPc extractLinkedCode
      (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk2Prep_framed txBase lenW innerW endPtr next len txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk2Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk2JalPc LinkLegacyWalk2 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg2Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk2Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk2OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk2 AfterLegacyWalk2Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        leg2Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractLegacyWalk2OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk3Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk2Bne LegacyWalk3JalPc extractLinkedCode
      (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk3Prep_framed txBase lenW innerW endPtr next len txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk3Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk3JalPc LinkLegacyWalk3 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg3Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk3Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractLegacyWalk3OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk3 AfterLegacyWalk3Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        leg3Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (leg3OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractLegacyWalk3OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractLegacyToHaveField_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff3 : Nat) :
    cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      (leg3OkConcrete txBase lenW innerW endPtr next len txBytes srcOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff3) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyToHaveField_framed txBase lenW innerW endPtr next len txBytes srcOff3
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1LoadArgs_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) T1Start T1Walk0JalPc extractLinkedCode
      (t1StartFrame txBase lenW innerW cursor endPtr txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StartFrame txBase lenW innerW cursor endPtr txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1LoadArgs_framed txBase lenW innerW cursor endPtr txBytes
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk0Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) T1Walk0JalPc LinkT1Walk0 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t10Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk0Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk0OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk0 AfterT1Walk0Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        t10Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t10OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk0OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk1Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
      (t10OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk1Prep_framed txBase lenW innerW endPtr next len txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk1Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) T1Walk1JalPc LinkT1Walk1 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t11Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk1Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk1OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        t11Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t11OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk1OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk2Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
      (t11OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk2Prep_framed txBase lenW innerW endPtr next len txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk2Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) T1Walk2JalPc LinkT1Walk2 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t12Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk2Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk2OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        t12Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t12OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk2OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk3Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
      (t12OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk3Prep_framed txBase lenW innerW endPtr next len txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk3Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) T1Walk3JalPc LinkT1Walk3 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t13Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk3Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk3OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        t13Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t13OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk3OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk4Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
      (t13OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk4Prep_framed txBase lenW innerW endPtr next len txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk4Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)

    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) T1Walk4JalPc LinkT1Walk4 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t14Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk4Call_framed txBase lenW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF


set_option maxRecDepth 8000 in
theorem extractT1Walk4OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        t14Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t14OkConcrete txBase lenW innerW endPtr next len txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk4OkNested_bne txBase lenW innerW endPtr txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
theorem extractT1ToHaveField_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff4 : Nat) :
    cpsTripleWithin 1 AfterT1Walk4Bne HaveField extractLinkedCode
      (t14OkConcrete txBase lenW innerW endPtr next len txBytes srcOff4 **
        midOwned spC s toBuf isCreationPtr s7)
      (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff4) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1ToHaveField_framed txBase lenW innerW endPtr next len txBytes srcOff4
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractLegacyLoadArgs_owned
#print axioms extractLegacyWalk0Call_owned
#print axioms extractLegacyWalk0OkNested_owned
#print axioms extractLegacyWalk1Prep_owned
#print axioms extractLegacyWalk1Call_owned
#print axioms extractLegacyWalk1OkNested_owned
#print axioms extractLegacyWalk2Prep_owned
#print axioms extractLegacyWalk2Call_owned
#print axioms extractLegacyWalk2OkNested_owned
#print axioms extractLegacyWalk3Prep_owned
#print axioms extractLegacyWalk3Call_owned
#print axioms extractLegacyWalk3OkNested_owned
#print axioms extractLegacyToHaveField_owned
#print axioms extractT1LoadArgs_owned
#print axioms extractT1Walk0Call_owned
#print axioms extractT1Walk0OkNested_owned
#print axioms extractT1Walk1Prep_owned
#print axioms extractT1Walk1Call_owned
#print axioms extractT1Walk1OkNested_owned
#print axioms extractT1Walk2Prep_owned
#print axioms extractT1Walk2Call_owned
#print axioms extractT1Walk2OkNested_owned
#print axioms extractT1Walk3Prep_owned
#print axioms extractT1Walk3Call_owned
#print axioms extractT1Walk3OkNested_owned
#print axioms extractT1Walk4Prep_owned
#print axioms extractT1Walk4Call_owned
#print axioms extractT1Walk4OkNested_owned
#print axioms extractT1ToHaveField_owned

end EvmAsm.Codegen.TxExtractToAddressSpec
