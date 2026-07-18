/-
  midOwned frames for legacy + t1 walk chains.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressTopT1
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)


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

/-- Reshape legacy ToHaveField post (len=0) → creation pre + extra temps. -/
private theorem legacy_toHaveField_owned_post_to_creationPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff3 : Nat) :
    ∀ h,
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff3) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        midOwned spC s toBuf isCreationPtr s7) h →
      (haveFieldCreAmbient txBase lenW (0 : Word) innerW toBuf
          (txBase + BitVec.ofNat 64 srcOff3) endPtr next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps ** regOwn .x7 ** regOwn .x5) h := by
  intro h hp
  simp only [legStable, midOwned, joinStackAmbient, haveFieldCreAmbient,
    extractToBufOwn, creExtraTemps] at hp ⊢
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- legacy end (len=0) → creation → ret under midOwned. -/
theorem extractLegacyHaveFieldCreation_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff3 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11))
      AfterLegacyWalk3Bne s.ra extractLinkedCode
      (leg3OkConcrete txBase lenW innerW endPtr next (0 : Word)
          txBytes srcOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
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
        (.x31 ↦ᵣ (next - (0 : Word))) **
        creExtraTemps) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff3
  have hTo := extractLegacyToHaveField_owned spC s txBase lenW innerW
    endPtr next (0 : Word) toBuf isCreationPtr s7 txBytes srcOff3
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
        (leg3OkConcrete txBase lenW innerW endPtr next (0 : Word)
            txBytes srcOff3 **
          midOwned spC s toBuf isCreationPtr s7)
        (haveFieldCreAmbient txBase lenW (0 : Word) innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq1 :
            (legStable txBase lenW innerW endPtr cursor **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
              regOwn .x29 ** regOwn .x30 **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
              bytesRegion txBase txBytes **
              (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
              (.x31 ↦ᵣ (next - (0 : Word))) **
              midOwned spC s toBuf isCreationPtr s7) h := by
          simpa [cursor] using hq
        exact legacy_toHaveField_owned_post_to_creationPre spC s txBase lenW
          innerW endPtr next toBuf isCreationPtr s7 txBytes srcOff3 _ hq1) hTo
  have hCre :
      cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
        HaveField s.ra extractLinkedCode
        (haveFieldCreAmbient txBase lenW (0 : Word) innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5)
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
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
          (.x31 ↦ᵣ (next - (0 : Word))) **
          creExtraTemps) := by
    let Pcore : Assertion :=
      haveFieldCreAmbient txBase lenW (0 : Word) innerW toBuf cursor endPtr next
          txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps
    have htemps :
        cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** regOwn .x7 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
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
            (.x31 ↦ᵣ (next - (0 : Word))) **
            creExtraTemps) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x5)
        (P := Pcore) (fun t2Old t0Old => ?_)
      have h := extractHaveFieldCreation_then_epi sp0 spC s txBase lenW (0 : Word)
        innerW toBuf cursor endPtr next isCreationPtr t2Old t0Old next
        LinkLegacyWalk3 s7 txBytes hspC hret
      have hF := cpsTripleWithin_frameR creExtraTemps creExtraTemps_pcFree h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore, creExtraTemps] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [creExtraTemps] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, creExtraTemps] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  exact cpsTripleWithin_seq_same_cr hTo2 hCre

set_option maxRecDepth 8000 in
/-- legacy end (len=20) → copy → ret under midOwned + content dwords. -/
theorem extractLegacyHaveFieldCopy_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff3 : Nat)
    (w0 w1 w2 : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcalign : (next - (20 : Word)).toNat % 8 = 0)
    (hcover : (next - (20 : Word)).toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess ((next - (20 : Word)) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin
      ((1 + 1) +
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11))
      AfterLegacyWalk3Bne s.ra extractLinkedCode
      (leg3OkConcrete txBase lenW innerW endPtr next (20 : Word)
          txBytes srcOff3 **
        midOwned spC s toBuf isCreationPtr s7 **
        ((next - (20 : Word)) ↦ₘ w0) **
        ((next - (20 : Word) + 8) ↦ₘ w1) **
        ((next - (20 : Word) + 16) ↦ₘ w2))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (0 : Word)) **
        (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
        ((next - (20 : Word)) ↦ₘ w0) **
        ((next - (20 : Word) + 8) ↦ₘ w1) **
        ((next - (20 : Word) + 16) ↦ₘ w2) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (extractWord32 w2
            (byteOffset ((next - (20 : Word)) + 16) / 4)).zeroExtend 64) **
        (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ (next - (20 : Word))) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff3
  let contentPtr := next - (20 : Word)
  have hTo := extractLegacyToHaveField_owned spC s txBase lenW innerW
    endPtr next (20 : Word) toBuf isCreationPtr s7 txBytes srcOff3
  have hToF := cpsTripleWithin_frameR
    ((contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
    (by
      apply pcFree_sepConj
      · exact pcFree_memIs
      · apply pcFree_sepConj
        · exact pcFree_memIs
        · exact pcFree_memIs) hTo
  have hCopy :
      cpsTripleWithin
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
        HaveField s.ra extractLinkedCode
        (legStable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          extractToBufOwn toBuf **
          (isCreationPtr ↦ₘ (0 : Word)) **
          (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (Reg.x23 ↦ᵣ s.s7) **
          (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
          (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
    let Pcore : Assertion :=
      haveFieldCopyAmbient txBase lenW (0 : Word) innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkLegacyWalk3) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) **
        (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x10 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        memOwn toBuf ** memOwn (toBuf + 8) ** memOwn isCreationPtr **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30
    have htemps :
        cpsTripleWithin
          ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
            extractToBufOwn toBuf **
            (isCreationPtr ↦ₘ (0 : Word)) **
            (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
            (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
            (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
            (.x31 ↦ᵣ contentPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6)
          (fun t0Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** (.x5 ↦ᵣ t0Old))
          (fun t1Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
          (P := Pcore ** memOwn (toBuf + 16) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun t2Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_memIs_to_memOwn (a := toBuf + 16)
          (P := Pcore ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun old16' => ?_))
      have h := extractHaveFieldCopy_then_epi sp0 spC s txBase lenW (0 : Word)
        innerW endPtr cursor contentPtr toBuf isCreationPtr
        t2Old t1Old t0Old next w0 w1 w2 old16' LinkLegacyWalk3 s7 txBytes
        hspC hret hcalign hcover hcvalid htalign htover htvalid
      have hF := cpsTripleWithin_frameR
        (regOwn .x28 ** regOwn .x29 ** regOwn .x30)
        (by
          apply pcFree_sepConj
          · exact pcFree_regOwn
          · apply pcFree_sepConj
            · exact pcFree_regOwn
            · exact pcFree_regOwn) h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [extractToBufOwn] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, midOwned, joinStackAmbient, haveFieldCopyAmbient,
        extractToBufOwn, legStable] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
        (leg3OkConcrete txBase lenW innerW endPtr next (20 : Word)
            txBytes srcOff3 **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
        (legStable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [contentPtr] at hp ⊢; xperm_hyp hp) (fun _ hq => by
      dsimp only [contentPtr, cursor] at hq ⊢; xperm_hyp hq) hToF
  exact cpsTripleWithin_seq_same_cr hTo2 hCopy

/-- Reshape t1 ToHaveField post (len=0) → creation pre + extra temps. -/
private theorem t1_toHaveField_owned_post_to_creationPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff4 : Nat) :
    ∀ h,
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff4) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        midOwned spC s toBuf isCreationPtr s7) h →
      (haveFieldCreAmbient txBase lenW (1 : Word) innerW toBuf
          (txBase + BitVec.ofNat 64 srcOff4) endPtr next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkT1Walk4) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps ** regOwn .x7 ** regOwn .x5) h := by
  intro h hp
  simp only [t1Stable, midOwned, joinStackAmbient, haveFieldCreAmbient,
    extractToBufOwn, creExtraTemps] at hp ⊢
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- t1 end (len=0) → creation → ret under midOwned. -/
theorem extractT1HaveFieldCreation_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff4 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      (1 + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11))
      AfterT1Walk4Bne s.ra extractLinkedCode
      (t14OkConcrete txBase lenW innerW endPtr next (0 : Word)
          txBytes srcOff4 **
        midOwned spC s toBuf isCreationPtr s7)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (1 : Word)) **
        (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        creExtraTemps) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff4
  have hTo := extractT1ToHaveField_owned spC s txBase lenW innerW
    endPtr next (0 : Word) toBuf isCreationPtr s7 txBytes srcOff4
  have hTo2 :
      cpsTripleWithin 1 AfterT1Walk4Bne HaveField extractLinkedCode
        (t14OkConcrete txBase lenW innerW endPtr next (0 : Word)
            txBytes srcOff4 **
          midOwned spC s toBuf isCreationPtr s7)
        (haveFieldCreAmbient txBase lenW (1 : Word) innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkT1Walk4) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq1 :
            (t1Stable txBase lenW innerW endPtr cursor **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
              regOwn .x29 ** regOwn .x30 **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
              bytesRegion txBase txBytes **
              (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
              (.x31 ↦ᵣ (next - (0 : Word))) **
              midOwned spC s toBuf isCreationPtr s7) h := by
          simpa [cursor] using hq
        exact t1_toHaveField_owned_post_to_creationPre spC s txBase lenW
          innerW endPtr next toBuf isCreationPtr s7 txBytes srcOff4 _ hq1) hTo
  have hCre :
      cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
        HaveField s.ra extractLinkedCode
        (haveFieldCreAmbient txBase lenW (1 : Word) innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkT1Walk4) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5)
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          extractToBufOwn toBuf **
          (isCreationPtr ↦ₘ (1 : Word)) **
          (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (Reg.x23 ↦ᵣ s.s7) **
          (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          (.x31 ↦ᵣ (next - (0 : Word))) **
          creExtraTemps) := by
    let Pcore : Assertion :=
      haveFieldCreAmbient txBase lenW (1 : Word) innerW toBuf cursor endPtr next
          txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkT1Walk4) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps
    have htemps :
        cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** regOwn .x7 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
            extractToBufOwn toBuf **
            (isCreationPtr ↦ₘ (1 : Word)) **
            (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            (.x31 ↦ᵣ (next - (0 : Word))) **
            creExtraTemps) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x5)
        (P := Pcore) (fun t2Old t0Old => ?_)
      have h := extractHaveFieldCreation_then_epi sp0 spC s txBase lenW (1 : Word)
        innerW toBuf cursor endPtr next isCreationPtr t2Old t0Old next
        LinkT1Walk4 s7 txBytes hspC hret
      have hF := cpsTripleWithin_frameR creExtraTemps creExtraTemps_pcFree h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore, creExtraTemps] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [creExtraTemps] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, creExtraTemps] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  exact cpsTripleWithin_seq_same_cr hTo2 hCre

set_option maxRecDepth 8000 in
/-- t1 end (len=20) → copy → ret under midOwned + content dwords. -/
theorem extractT1HaveFieldCopy_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff4 : Nat)
    (w0 w1 w2 : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcalign : (next - (20 : Word)).toNat % 8 = 0)
    (hcover : (next - (20 : Word)).toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess ((next - (20 : Word)) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin
      (1 +
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11))
      AfterT1Walk4Bne s.ra extractLinkedCode
      (t14OkConcrete txBase lenW innerW endPtr next (20 : Word)
          txBytes srcOff4 **
        midOwned spC s toBuf isCreationPtr s7 **
        ((next - (20 : Word)) ↦ₘ w0) **
        ((next - (20 : Word) + 8) ↦ₘ w1) **
        ((next - (20 : Word) + 16) ↦ₘ w2))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (0 : Word)) **
        (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
        ((next - (20 : Word)) ↦ₘ w0) **
        ((next - (20 : Word) + 8) ↦ₘ w1) **
        ((next - (20 : Word) + 16) ↦ₘ w2) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (extractWord32 w2
            (byteOffset ((next - (20 : Word)) + 16) / 4)).zeroExtend 64) **
        (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ (next - (20 : Word))) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff4
  let contentPtr := next - (20 : Word)
  have hTo := extractT1ToHaveField_owned spC s txBase lenW innerW
    endPtr next (20 : Word) toBuf isCreationPtr s7 txBytes srcOff4
  have hToF := cpsTripleWithin_frameR
    ((contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
    (by
      apply pcFree_sepConj
      · exact pcFree_memIs
      · apply pcFree_sepConj
        · exact pcFree_memIs
        · exact pcFree_memIs) hTo
  have hCopy :
      cpsTripleWithin
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
        HaveField s.ra extractLinkedCode
        (t1Stable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          extractToBufOwn toBuf **
          (isCreationPtr ↦ₘ (0 : Word)) **
          (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (Reg.x23 ↦ᵣ s.s7) **
          (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
          (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
    let Pcore : Assertion :=
      haveFieldCopyAmbient txBase lenW (1 : Word) innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkT1Walk4) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) **
        (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x10 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        memOwn toBuf ** memOwn (toBuf + 8) ** memOwn isCreationPtr **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30
    have htemps :
        cpsTripleWithin
          ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
            extractToBufOwn toBuf **
            (isCreationPtr ↦ₘ (0 : Word)) **
            (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
            (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
            (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
            (.x31 ↦ᵣ contentPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6)
          (fun t0Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** (.x5 ↦ᵣ t0Old))
          (fun t1Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
          (P := Pcore ** memOwn (toBuf + 16) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun t2Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_memIs_to_memOwn (a := toBuf + 16)
          (P := Pcore ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun old16' => ?_))
      have h := extractHaveFieldCopy_then_epi sp0 spC s txBase lenW (1 : Word)
        innerW endPtr cursor contentPtr toBuf isCreationPtr
        t2Old t1Old t0Old next w0 w1 w2 old16' LinkT1Walk4 s7 txBytes
        hspC hret hcalign hcover hcvalid htalign htover htvalid
      have hF := cpsTripleWithin_frameR
        (regOwn .x28 ** regOwn .x29 ** regOwn .x30)
        (by
          apply pcFree_sepConj
          · exact pcFree_regOwn
          · apply pcFree_sepConj
            · exact pcFree_regOwn
            · exact pcFree_regOwn) h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [extractToBufOwn] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, midOwned, joinStackAmbient, haveFieldCopyAmbient,
        extractToBufOwn, t1Stable] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  have hTo2 :
      cpsTripleWithin 1 AfterT1Walk4Bne HaveField extractLinkedCode
        (t14OkConcrete txBase lenW innerW endPtr next (20 : Word)
            txBytes srcOff4 **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
        (t1Stable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [contentPtr] at hp ⊢; xperm_hyp hp) (fun _ hq => by
      dsimp only [contentPtr, cursor] at hq ⊢; xperm_hyp hq) hToF
  exact cpsTripleWithin_seq_same_cr hTo2 hCopy

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
#print axioms extractLegacyHaveFieldCreation_then_epi
#print axioms extractLegacyHaveFieldCopy_then_epi
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
#print axioms extractT1HaveFieldCreation_then_epi
#print axioms extractT1HaveFieldCopy_then_epi

end EvmAsm.Codegen.TxExtractToAddressSpec
