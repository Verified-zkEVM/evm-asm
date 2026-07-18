/-
  Legacy mid-seq of_decode: Outcome posts + drop-fail via pure decode.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwnedLT
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext0
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)


set_option maxRecDepth 8000 in
/-- leg0 call with any a2, post Outcome (honest drop). -/
theorem extractLegacyWalk0Call_a2_outcome
    (txBase lenW innerW endPtr a2Old : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg0Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg0Common txBase txBytes **
      wn0Outcome txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk0Call txBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkWalkInit
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (legStable txBase lenW innerW endPtr cursor)
      (legStable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, legStable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (legStable txBase lenW innerW endPtr cursor **
            extractLegacyWalk0Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractLegacyWalk0Post_to_commonOutcome
        txBase endPtr txBytes srcOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
/-- leg0 call under midOwned posting Outcome. -/
theorem extractLegacyWalk0Call_owned_a2_outcome
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg0Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk0Call_a2_outcome txBase lenW innerW endPtr a2Old
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- leg0 call+Ok under pure decode (a2=0 from loadArgs). -/
theorem extractLegacyWalk0CallOk_owned_of_decode
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
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next0 len0 : Word,
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next0 len0)
    (hinb : BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    cpsTripleWithin ((1 + 87) + 1) LegacyWalk0JalPc AfterLegacyWalk0Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next0 len0 : Word,
        (leg0OkConcrete txBase lenW innerW endPtr next0 len0
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hCall := extractLegacyWalk0Call_owned_a2_outcome spC s txBase lenW innerW endPtr
    (0 : Word) toBuf isCreationPtr s7 txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  have hCall2 :
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
          rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode txBase endPtr txBytes srcOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hCall
  have hOk := extractLegacyWalk0OkNested_owned spC s txBase lenW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff
  exact cpsTripleWithin_seq_same_cr hCall2 hOk

set_option maxRecDepth 8000 in
/-- leg1 call with any a2, post Outcome (honest drop). -/
theorem extractLegacyWalk1Call_a2_outcome
    (txBase lenW innerW endPtr a2Old : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg1Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg1Common txBase txBytes **
      wn0Outcome txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk1JalPc LinkLegacyWalk1 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk1Call txBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkLegacyWalk0
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (legStable txBase lenW innerW endPtr cursor)
      (legStable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, legStable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (legStable txBase lenW innerW endPtr cursor **
            extractLegacyWalk1Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractLegacyWalk1Post_to_commonOutcome
        txBase endPtr txBytes srcOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
/-- leg1 call under midOwned posting Outcome. -/
theorem extractLegacyWalk1Call_owned_a2_outcome
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg1Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk1Call_a2_outcome txBase lenW innerW endPtr a2Old
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- leg1 prep+call under midOwned posting Outcome. -/
theorem extractLegacyWalk1PrepCall_owned_outcome
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOffPrev srcOff : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff)
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
    cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
      AfterLegacyWalk0Bne LinkLegacyWalk1 extractLinkedCode
      (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg1Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have hPrep := extractLegacyWalk1Prep_owned spC s txBase lenW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOffPrev
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk0Bne LegacyWalk1JalPc extractLinkedCode
        (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (legStable txBase lenW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff) **
          (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractLegacyWalk1Call_owned_a2_outcome spC s txBase lenW innerW endPtr
    len toBuf isCreationPtr s7 txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  exact cpsTripleWithin_seq_same_cr hPrep2 hCall

set_option maxRecDepth 8000 in
/-- leg1 prep+call+Ok under pure decode. -/
theorem extractLegacyWalk1PrepCallOk_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOffPrev srcOff : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff)
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
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ nextN lenN : Word,
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr nextN lenN)
    (hinb : BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterLegacyWalk0Bne AfterLegacyWalk1Bne extractLinkedCode
      (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ nextN lenN : Word,
        (leg1OkConcrete txBase lenW innerW endPtr nextN lenN
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPC := extractLegacyWalk1PrepCall_owned_outcome spC s txBase lenW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOffPrev srcOff
    hnext hsalign hoff hover hvalid hss hls hll
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterLegacyWalk0Bne LinkLegacyWalk1 extractLinkedCode
        (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (legStable txBase lenW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff) **
          leg1Common txBase txBytes **
          rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode txBase endPtr txBytes srcOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractLegacyWalk1OkNested_owned spC s txBase lenW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff
  exact cpsTripleWithin_seq_same_cr hPC2 hOk

set_option maxRecDepth 8000 in
/-- leg2 call with any a2, post Outcome (honest drop). -/
theorem extractLegacyWalk2Call_a2_outcome
    (txBase lenW innerW endPtr a2Old : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg2Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg2Common txBase txBytes **
      wn0Outcome txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk2JalPc LinkLegacyWalk2 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk2Call txBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkLegacyWalk1
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (legStable txBase lenW innerW endPtr cursor)
      (legStable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, legStable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (legStable txBase lenW innerW endPtr cursor **
            extractLegacyWalk2Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractLegacyWalk2Post_to_commonOutcome
        txBase endPtr txBytes srcOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
/-- leg2 call under midOwned posting Outcome. -/
theorem extractLegacyWalk2Call_owned_a2_outcome
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg2Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk2Call_a2_outcome txBase lenW innerW endPtr a2Old
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- leg2 prep+call under midOwned posting Outcome. -/
theorem extractLegacyWalk2PrepCall_owned_outcome
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOffPrev srcOff : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff)
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
    cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
      AfterLegacyWalk1Bne LinkLegacyWalk2 extractLinkedCode
      (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg2Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have hPrep := extractLegacyWalk2Prep_owned spC s txBase lenW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOffPrev
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk1Bne LegacyWalk2JalPc extractLinkedCode
        (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (legStable txBase lenW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff) **
          (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractLegacyWalk2Call_owned_a2_outcome spC s txBase lenW innerW endPtr
    len toBuf isCreationPtr s7 txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  exact cpsTripleWithin_seq_same_cr hPrep2 hCall

set_option maxRecDepth 8000 in
/-- leg2 prep+call+Ok under pure decode. -/
theorem extractLegacyWalk2PrepCallOk_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOffPrev srcOff : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff)
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
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ nextN lenN : Word,
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr nextN lenN)
    (hinb : BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterLegacyWalk1Bne AfterLegacyWalk2Bne extractLinkedCode
      (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ nextN lenN : Word,
        (leg2OkConcrete txBase lenW innerW endPtr nextN lenN
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPC := extractLegacyWalk2PrepCall_owned_outcome spC s txBase lenW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOffPrev srcOff
    hnext hsalign hoff hover hvalid hss hls hll
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterLegacyWalk1Bne LinkLegacyWalk2 extractLinkedCode
        (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (legStable txBase lenW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff) **
          leg2Common txBase txBytes **
          rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode txBase endPtr txBytes srcOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractLegacyWalk2OkNested_owned spC s txBase lenW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff
  exact cpsTripleWithin_seq_same_cr hPC2 hOk

set_option maxRecDepth 8000 in
/-- leg3 call with any a2, post Outcome (honest drop). -/
theorem extractLegacyWalk3Call_a2_outcome
    (txBase lenW innerW endPtr a2Old : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg3Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg3Common txBase txBytes **
      wn0Outcome txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk3JalPc LinkLegacyWalk3 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk3Call txBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkLegacyWalk2
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (legStable txBase lenW innerW endPtr cursor)
      (legStable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, legStable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (legStable txBase lenW innerW endPtr cursor **
            extractLegacyWalk3Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractLegacyWalk3Post_to_commonOutcome
        txBase endPtr txBytes srcOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
/-- leg3 call under midOwned posting Outcome. -/
theorem extractLegacyWalk3Call_owned_a2_outcome
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg3Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk3Call_a2_outcome txBase lenW innerW endPtr a2Old
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- leg3 prep+call under midOwned posting Outcome. -/
theorem extractLegacyWalk3PrepCall_owned_outcome
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOffPrev srcOff : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff)
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
    cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
      AfterLegacyWalk2Bne LinkLegacyWalk3 extractLinkedCode
      (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg3Common txBase txBytes **
        wn0Outcome txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have hPrep := extractLegacyWalk3Prep_owned spC s txBase lenW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOffPrev
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk2Bne LegacyWalk3JalPc extractLinkedCode
        (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (legStable txBase lenW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff) **
          (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractLegacyWalk3Call_owned_a2_outcome spC s txBase lenW innerW endPtr
    len toBuf isCreationPtr s7 txBytes srcOff
    hsalign hoff hover hvalid hss hls hll
  exact cpsTripleWithin_seq_same_cr hPrep2 hCall

set_option maxRecDepth 8000 in
/-- leg3 prep+call+Ok under pure decode. -/
theorem extractLegacyWalk3PrepCallOk_owned_of_decode
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOffPrev srcOff : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff)
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
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ nextN lenN : Word,
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr nextN lenN)
    (hinb : BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterLegacyWalk2Bne AfterLegacyWalk3Bne extractLinkedCode
      (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ nextN lenN : Word,
        (leg3OkConcrete txBase lenW innerW endPtr nextN lenN
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPC := extractLegacyWalk3PrepCall_owned_outcome spC s txBase lenW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOffPrev srcOff
    hnext hsalign hoff hover hvalid hss hls hll
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterLegacyWalk2Bne LinkLegacyWalk3 extractLinkedCode
        (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (legStable txBase lenW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff) **
          leg3Common txBase txBytes **
          rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode txBase endPtr txBytes srcOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractLegacyWalk3OkNested_owned spC s txBase lenW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff
  exact cpsTripleWithin_seq_same_cr hPC2 hOk

#print axioms extractLegacyWalk0Call_a2_outcome
#print axioms extractLegacyWalk0CallOk_owned_of_decode
#print axioms extractLegacyWalk1PrepCallOk_owned_of_decode
#print axioms extractLegacyWalk2PrepCallOk_owned_of_decode
#print axioms extractLegacyWalk3PrepCallOk_owned_of_decode

end EvmAsm.Codegen.TxExtractToAddressSpec
