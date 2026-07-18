/-
  Mid-seq composition: prep→call (any a2) under midOwned for type234 wn5.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNextRest
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact pcFree_regsAt _ _
    | exact pcFree_frameSlotsSaved _ _ _
    | exact bytesRegion_pcFree _ _)

/-- Peel seven owned scratch registers (WalkNext1 style). -/
private theorem of_forall_regOwn7
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 r4 r5 r6 r7 : Reg} {P Q : Assertion}
    (hspec : ∀ v1 v2 v3 v4 v5 v6 v7, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact hspec v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1,
        g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
        g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
        g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

set_option maxRecDepth 8000 in
/-- wn5 call (no midOwned) with arbitrary a2 — matches prep post x12. -/
theorem extractWalkNext5Call_type234_a2
    (txBase lenW typeW innerW endPtr a2Old : Word)
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
    cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 extractLinkedCode
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes)
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn5Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    wn5Stable txBase lenW typeW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    wn5Stable txBase lenW typeW innerW endPtr cursor **
      wn5Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext5Call txBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkWalkNext4
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (wn5Stable txBase lenW typeW innerW endPtr cursor)
      (wn5Stable_pcFree _ _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, wn5Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (wn5Stable txBase lenW typeW innerW endPtr cursor **
            extractWalkNext5Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractWalkNext5Post_to_commonOutcome
        txBase endPtr txBytes srcOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      have hok := wn0Outcome_to_okFail txBase endPtr txBytes srcOff _ hout
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hok⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
/-- wn5 call under midOwned with arbitrary a2. -/
theorem extractWalkNext5Call_owned_a2
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
    cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 extractLinkedCode
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn5Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext5Call_type234_a2 txBase lenW typeW innerW endPtr a2Old
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- prep + call: AfterWalkNext4Bne → LinkWalkNext5 under midOwned.
    Requires `next = txBase + srcOff5` (cursor identity after wn4). -/
theorem extractWalkNext5PrepCall_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff4 srcOff5 : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff5)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff5 < txBytes.length)
    (hover : txBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff5) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < txBytes.length ∧ txBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true) :
    cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
      AfterWalkNext4Bne LinkWalkNext5 extractLinkedCode
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff4 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff5) **
        wn5Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff5 **
        midOwned spC s toBuf isCreationPtr s7) := by
  have hPrep := extractWalkNext5Prep_owned spC s txBase lenW typeW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOff4
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterWalkNext4Bne WalkNext5JalPc extractLinkedCode
        (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff4 **
          midOwned spC s toBuf isCreationPtr s7)
        (wn5Stable txBase lenW typeW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff5) **
          (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff5)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      -- prep post: wn5Stable ... next ** x10↦next; rewrite next via hnext
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractWalkNext5Call_owned_a2 spC s txBase lenW typeW innerW endPtr
    len toBuf isCreationPtr s7 txBytes srcOff5
    hsalign hoff hover hvalid hss hls hll
  exact cpsTripleWithin_seq_same_cr hPrep2 hCall

set_option maxRecDepth 8000 in
/-- prep+call+OkNested under drop-fail hyp on wn0OkFail. -/
theorem extractWalkNext5PrepCallOk_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff4 srcOff5 : Nat)
    (hnext : next = txBase + BitVec.ofNat 64 srcOff5)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff5 < txBytes.length)
    (hover : txBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff5) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < txBytes.length ∧ txBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff5]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff5 + 1 +
          ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff5]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hok : ∀ (h : PartialState),
      wn0OkFail txBase endPtr txBytes srcOff5 h →
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff5) endPtr txBytes srcOff5 h) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterWalkNext4Bne AfterWalkNext5Bne extractLinkedCode
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff4 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next5 len5 : Word,
        (wn5OkConcrete txBase lenW typeW innerW endPtr next5 len5
          txBytes srcOff5 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPC := extractWalkNext5PrepCall_owned spC s txBase lenW typeW innerW endPtr
    next len toBuf isCreationPtr s7 txBytes srcOff4 srcOff5
    hnext hsalign hoff hover hvalid hss hls hll
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterWalkNext4Bne LinkWalkNext5 extractLinkedCode
        (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff4 **
          midOwned spC s toBuf isCreationPtr s7)
        (wn5Stable txBase lenW typeW innerW endPtr
            (txBase + BitVec.ofNat 64 srcOff5) **
          wn5Common txBase txBytes **
          rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff5) endPtr txBytes srcOff5 **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      -- hq : (wn5Stable ** wn5Common ** wn0OkFail ** midOwned) h
      -- right-assoc: A ** (B ** (C ** D))
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hF, hM⟩ := hCD
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hok h5 hF, hM⟩) hPC
  have hOk := extractWalkNext5OkNested_owned spC s txBase lenW typeW innerW endPtr
    toBuf isCreationPtr s7 txBytes srcOff5
  exact cpsTripleWithin_seq_same_cr hPC2 hOk

#print axioms extractWalkNext5Call_type234_a2
#print axioms extractWalkNext5Call_owned_a2
#print axioms extractWalkNext5PrepCall_owned
#print axioms extractWalkNext5PrepCallOk_owned

end EvmAsm.Codegen.TxExtractToAddressSpec
