/-
  Ambient dual of t1 walk1..3 Prep/Call/Ok under split bases.
  x8=loadPtr; bytesRegion/cursor use regionBase + absOff.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressT1Walk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopT1
import EvmAsm.Codegen.Programs.TxExtractToAddressTopT1Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopT1Walk0Ambient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext0
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
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
    | exact bytesRegion_pcFree _ _)


theorem extractT1Walk1Post_to_commonOutcome_ambient
    (regionBase endPtr : Word) (bs : List (BitVec 8)) (absOff : Nat) :
    ∀ h, extractT1Walk1Post regionBase endPtr bs absOff h →
      (t11CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) h := by
  intro h hp
  simp only [extractT1Walk1Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t11CommonAmbient regionBase bs h1 := by
    simp only [t11CommonAmbient]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk1Prep_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
      (t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
        bs absOffPrev)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs) := by
  let oldCursor := regionBase + BitVec.ofNat 64 absOffPrev
  have h := extractT1Walk1Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
        (t10OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev)
        (t1StableAmbient loadPtr lenW innerW endPtr next **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t10OkRegsAmbient, t1StableAmbient, t10CommonAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1StableAmbient] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t10OkConcreteAmbient] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk1Call_a2_outcome_ambient
    (loadPtr regionBase lenW innerW endPtr a2Old : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk1JalPc LinkT1Walk1 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t11CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  let Pcore : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs
  let Qassumed : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      t11CommonAmbient regionBase bs **
      wn0Outcome regionBase endPtr bs absOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk1JalPc LinkT1Walk1 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk1Call regionBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 bs absOff LinkT1Walk0
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1StableAmbient loadPtr lenW innerW endPtr cursor)
      (t1StableAmbient_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1StableAmbient, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1StableAmbient loadPtr lenW innerW endPtr cursor **
            extractT1Walk1Post regionBase endPtr bs absOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk1Post_to_commonOutcome_ambient
        regionBase endPtr bs absOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractT1Walk1BneOk_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      (t11OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff)
      (t11OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff) := by
  have h0 := extractT1Walk1BneOk
  have hF := cpsTripleWithin_frameR
    (t1StableAmbient loadPtr lenW innerW endPtr
        (regionBase + BitVec.ofNat 64 absOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk1) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t11OkRegsAmbient, t1StableAmbient, t11CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t11OkRegsAmbient, t1StableAmbient, t11CommonAmbient] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk1OkNested_bne_ambient
    (loadPtr regionBase lenW innerW endPtr : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t11CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff)
      (fun h => ∃ next len : Word,
        t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff h) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1StableAmbient loadPtr lenW innerW endPtr cursor **
        t11CommonAmbient regionBase bs **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs absOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs absOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (t1StableAmbient loadPtr lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk1) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t11CommonAmbient] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk1BneOk_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t11OkRegsAmbient, t11CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t11OkConcreteAmbient, t11OkRegsAmbient]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk1Prep_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
      (t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk1Prep_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOffPrev
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk1Call_owned_a2_outcome_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk1JalPc LinkT1Walk1 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t11CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk1Call_a2_outcome_ambient loadPtr regionBase
    lenW innerW endPtr a2Old bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk1OkNested_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t11CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk1OkNested_bne_ambient loadPtr regionBase
    lenW innerW endPtr bs absOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk1PrepCallOk_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev absOff : Nat)
    (hnext : next = regionBase + BitVec.ofNat 64 absOff)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hdec : ∃ nextN lenN : Word,
      rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
        endPtr nextN lenN)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 absOff) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk0Bne AfterT1Walk1Bne extractLinkedCode
      (t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ nextN lenN : Word,
        (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr nextN lenN
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPrep := extractT1Walk1Prep_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr next len toBuf isCreationPtr s7 bs absOffPrev
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
        (t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion regionBase bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractT1Walk1Call_owned_a2_outcome_ambient spC s loadPtr
    regionBase lenW innerW endPtr len toBuf isCreationPtr s7 bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hPC := cpsTripleWithin_seq_same_cr hPrep2 hCall
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterT1Walk0Bne LinkT1Walk1 extractLinkedCode
        (t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          t11CommonAmbient regionBase bs **
          rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode regionBase endPtr bs absOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractT1Walk1OkNested_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr toBuf isCreationPtr s7 bs absOff
  exact cpsTripleWithin_seq_same_cr hPC2 hOk


theorem extractT1Walk2Post_to_commonOutcome_ambient
    (regionBase endPtr : Word) (bs : List (BitVec 8)) (absOff : Nat) :
    ∀ h, extractT1Walk2Post regionBase endPtr bs absOff h →
      (t12CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) h := by
  intro h hp
  simp only [extractT1Walk2Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t12CommonAmbient regionBase bs h1 := by
    simp only [t12CommonAmbient]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk2Prep_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
      (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
        bs absOffPrev)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs) := by
  let oldCursor := regionBase + BitVec.ofNat 64 absOffPrev
  have h := extractT1Walk2Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
        (t11OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev)
        (t1StableAmbient loadPtr lenW innerW endPtr next **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t11OkRegsAmbient, t1StableAmbient, t11CommonAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1StableAmbient] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t11OkConcreteAmbient] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk2Call_a2_outcome_ambient
    (loadPtr regionBase lenW innerW endPtr a2Old : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk2JalPc LinkT1Walk2 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t12CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  let Pcore : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs
  let Qassumed : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      t12CommonAmbient regionBase bs **
      wn0Outcome regionBase endPtr bs absOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk2JalPc LinkT1Walk2 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk2Call regionBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 bs absOff LinkT1Walk1
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1StableAmbient loadPtr lenW innerW endPtr cursor)
      (t1StableAmbient_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1StableAmbient, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1StableAmbient loadPtr lenW innerW endPtr cursor **
            extractT1Walk2Post regionBase endPtr bs absOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk2Post_to_commonOutcome_ambient
        regionBase endPtr bs absOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractT1Walk2BneOk_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      (t12OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff)
      (t12OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff) := by
  have h0 := extractT1Walk2BneOk
  have hF := cpsTripleWithin_frameR
    (t1StableAmbient loadPtr lenW innerW endPtr
        (regionBase + BitVec.ofNat 64 absOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk2) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t12OkRegsAmbient, t1StableAmbient, t12CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t12OkRegsAmbient, t1StableAmbient, t12CommonAmbient] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk2OkNested_bne_ambient
    (loadPtr regionBase lenW innerW endPtr : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t12CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff)
      (fun h => ∃ next len : Word,
        t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff h) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1StableAmbient loadPtr lenW innerW endPtr cursor **
        t12CommonAmbient regionBase bs **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs absOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs absOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (t1StableAmbient loadPtr lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk2) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t12CommonAmbient] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk2BneOk_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t12OkRegsAmbient, t12CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t12OkConcreteAmbient, t12OkRegsAmbient]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk2Prep_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
      (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk2Prep_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOffPrev
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk2Call_owned_a2_outcome_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk2JalPc LinkT1Walk2 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t12CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk2Call_a2_outcome_ambient loadPtr regionBase
    lenW innerW endPtr a2Old bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk2OkNested_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t12CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk2OkNested_bne_ambient loadPtr regionBase
    lenW innerW endPtr bs absOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk2PrepCallOk_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev absOff : Nat)
    (hnext : next = regionBase + BitVec.ofNat 64 absOff)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hdec : ∃ nextN lenN : Word,
      rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
        endPtr nextN lenN)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 absOff) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk1Bne AfterT1Walk2Bne extractLinkedCode
      (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ nextN lenN : Word,
        (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr nextN lenN
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPrep := extractT1Walk2Prep_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr next len toBuf isCreationPtr s7 bs absOffPrev
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
        (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion regionBase bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractT1Walk2Call_owned_a2_outcome_ambient spC s loadPtr
    regionBase lenW innerW endPtr len toBuf isCreationPtr s7 bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hPC := cpsTripleWithin_seq_same_cr hPrep2 hCall
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterT1Walk1Bne LinkT1Walk2 extractLinkedCode
        (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          t12CommonAmbient regionBase bs **
          rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode regionBase endPtr bs absOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractT1Walk2OkNested_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr toBuf isCreationPtr s7 bs absOff
  exact cpsTripleWithin_seq_same_cr hPC2 hOk


theorem extractT1Walk3Post_to_commonOutcome_ambient
    (regionBase endPtr : Word) (bs : List (BitVec 8)) (absOff : Nat) :
    ∀ h, extractT1Walk3Post regionBase endPtr bs absOff h →
      (t13CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) h := by
  intro h hp
  simp only [extractT1Walk3Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t13CommonAmbient regionBase bs h1 := by
    simp only [t13CommonAmbient]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk3Prep_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
      (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
        bs absOffPrev)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs) := by
  let oldCursor := regionBase + BitVec.ofNat 64 absOffPrev
  have h := extractT1Walk3Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
        (t12OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev)
        (t1StableAmbient loadPtr lenW innerW endPtr next **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t12OkRegsAmbient, t1StableAmbient, t12CommonAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1StableAmbient] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t12OkConcreteAmbient] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk3Call_a2_outcome_ambient
    (loadPtr regionBase lenW innerW endPtr a2Old : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk3JalPc LinkT1Walk3 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t13CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  let Pcore : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs
  let Qassumed : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      t13CommonAmbient regionBase bs **
      wn0Outcome regionBase endPtr bs absOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk3JalPc LinkT1Walk3 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk3Call regionBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 bs absOff LinkT1Walk2
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1StableAmbient loadPtr lenW innerW endPtr cursor)
      (t1StableAmbient_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1StableAmbient, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1StableAmbient loadPtr lenW innerW endPtr cursor **
            extractT1Walk3Post regionBase endPtr bs absOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk3Post_to_commonOutcome_ambient
        regionBase endPtr bs absOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractT1Walk3BneOk_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      (t13OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff)
      (t13OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff) := by
  have h0 := extractT1Walk3BneOk
  have hF := cpsTripleWithin_frameR
    (t1StableAmbient loadPtr lenW innerW endPtr
        (regionBase + BitVec.ofNat 64 absOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk3) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t13OkRegsAmbient, t1StableAmbient, t13CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t13OkRegsAmbient, t1StableAmbient, t13CommonAmbient] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk3OkNested_bne_ambient
    (loadPtr regionBase lenW innerW endPtr : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t13CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff)
      (fun h => ∃ next len : Word,
        t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff h) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1StableAmbient loadPtr lenW innerW endPtr cursor **
        t13CommonAmbient regionBase bs **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs absOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs absOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (t1StableAmbient loadPtr lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk3) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t13CommonAmbient] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk3BneOk_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t13OkRegsAmbient, t13CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t13OkConcreteAmbient, t13OkRegsAmbient]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk3Prep_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
      (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk3Prep_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOffPrev
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk3Call_owned_a2_outcome_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk3JalPc LinkT1Walk3 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t13CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk3Call_a2_outcome_ambient loadPtr regionBase
    lenW innerW endPtr a2Old bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk3OkNested_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t13CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk3OkNested_bne_ambient loadPtr regionBase
    lenW innerW endPtr bs absOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk3PrepCallOk_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev absOff : Nat)
    (hnext : next = regionBase + BitVec.ofNat 64 absOff)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hdec : ∃ nextN lenN : Word,
      rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
        endPtr nextN lenN)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 absOff) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk2Bne AfterT1Walk3Bne extractLinkedCode
      (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ nextN lenN : Word,
        (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr nextN lenN
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPrep := extractT1Walk3Prep_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr next len toBuf isCreationPtr s7 bs absOffPrev
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
        (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion regionBase bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractT1Walk3Call_owned_a2_outcome_ambient spC s loadPtr
    regionBase lenW innerW endPtr len toBuf isCreationPtr s7 bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hPC := cpsTripleWithin_seq_same_cr hPrep2 hCall
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterT1Walk2Bne LinkT1Walk3 extractLinkedCode
        (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          t13CommonAmbient regionBase bs **
          rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode regionBase endPtr bs absOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractT1Walk3OkNested_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr toBuf isCreationPtr s7 bs absOff
  exact cpsTripleWithin_seq_same_cr hPC2 hOk


theorem extractT1Walk4Post_to_commonOutcome_ambient
    (regionBase endPtr : Word) (bs : List (BitVec 8)) (absOff : Nat) :
    ∀ h, extractT1Walk4Post regionBase endPtr bs absOff h →
      (t14CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) h := by
  intro h hp
  simp only [extractT1Walk4Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t14CommonAmbient regionBase bs h1 := by
    simp only [t14CommonAmbient]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk4Prep_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
      (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
        bs absOffPrev)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs) := by
  let oldCursor := regionBase + BitVec.ofNat 64 absOffPrev
  have h := extractT1Walk4Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
        (t13OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev)
        (t1StableAmbient loadPtr lenW innerW endPtr next **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t13OkRegsAmbient, t1StableAmbient, t13CommonAmbient] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1StableAmbient] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t13OkConcreteAmbient] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk4Call_a2_outcome_ambient
    (loadPtr regionBase lenW innerW endPtr a2Old : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk4JalPc LinkT1Walk4 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t14CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  let Pcore : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs
  let Qassumed : Assertion :=
    t1StableAmbient loadPtr lenW innerW endPtr cursor **
      t14CommonAmbient regionBase bs **
      wn0Outcome regionBase endPtr bs absOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk4JalPc LinkT1Walk4 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk4Call regionBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 bs absOff LinkT1Walk3
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1StableAmbient loadPtr lenW innerW endPtr cursor)
      (t1StableAmbient_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1StableAmbient, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1StableAmbient loadPtr lenW innerW endPtr cursor **
            extractT1Walk4Post regionBase endPtr bs absOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk4Post_to_commonOutcome_ambient
        regionBase endPtr bs absOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hout⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractT1Walk4BneOk_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      (t14OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff)
      (t14OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff) := by
  have h0 := extractT1Walk4BneOk
  have hF := cpsTripleWithin_frameR
    (t1StableAmbient loadPtr lenW innerW endPtr
        (regionBase + BitVec.ofNat 64 absOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk4) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t14OkRegsAmbient, t1StableAmbient, t14CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t14OkRegsAmbient, t1StableAmbient, t14CommonAmbient] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk4OkNested_bne_ambient
    (loadPtr regionBase lenW innerW endPtr : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t14CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff)
      (fun h => ∃ next len : Word,
        t14OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff h) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1StableAmbient loadPtr lenW innerW endPtr cursor **
        t14CommonAmbient regionBase bs **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs absOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs absOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (t1StableAmbient loadPtr lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk4) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t14CommonAmbient] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk4BneOk_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t14OkRegsAmbient, t14CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t14OkConcreteAmbient, t14OkRegsAmbient]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk4Prep_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
      (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk4Prep_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOffPrev
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk4Call_owned_a2_outcome_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr a2Old toBuf isCreationPtr s7 : Word)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true) :
    cpsTripleWithin (1 + 87) T1Walk4JalPc LinkT1Walk4 extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7)
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t14CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractT1Walk4Call_a2_outcome_ambient loadPtr regionBase
    lenW innerW endPtr a2Old bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk4OkNested_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      (t1StableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        t14CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (t14OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractT1Walk4OkNested_bne_ambient loadPtr regionBase
    lenW innerW endPtr bs absOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk4PrepCallOk_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOffPrev absOff : Nat)
    (hnext : next = regionBase + BitVec.ofNat 64 absOff)
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
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + j)) = true)
    (hdec : ∃ nextN lenN : Word,
      rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
        endPtr nextN lenN)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 absOff) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk3Bne AfterT1Walk4Bne extractLinkedCode
      (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOffPrev **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ nextN lenN : Word,
        (t14OkConcreteAmbient loadPtr regionBase lenW innerW endPtr nextN lenN
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hPrep := extractT1Walk4Prep_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr next len toBuf isCreationPtr s7 bs absOffPrev
  have hPrep2 :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
        (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion regionBase bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [hnext] at hq
      xperm_hyp hq) hPrep
  have hCall := extractT1Walk4Call_owned_a2_outcome_ambient spC s loadPtr
    regionBase lenW innerW endPtr len toBuf isCreationPtr s7 bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hPC := cpsTripleWithin_seq_same_cr hPrep2 hCall
  have hPC2 :
      cpsTripleWithin ((1 + (1 + 1)) + (1 + 87))
        AfterT1Walk3Bne LinkT1Walk4 extractLinkedCode
        (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
            bs absOffPrev **
          midOwned spC s toBuf isCreationPtr s7)
        (t1StableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          t14CommonAmbient regionBase bs **
          rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
      obtain ⟨h1, h2, hd1, hu1, hS, hBCD⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hC, hCD⟩ := hBCD
      obtain ⟨h5, h6, hd3, hu3, hOut, hM⟩ := hCD
      have hOk := wn0Outcome_drop_fail_of_decode regionBase endPtr bs absOff
        hdec hinb h5 hOut
      exact ⟨h1, h2, hd1, hu1, hS, h3, h4, hd2, hu2, hC,
        h5, h6, hd3, hu3, hOk, hM⟩) hPC
  have hOk := extractT1Walk4OkNested_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr toBuf isCreationPtr s7 bs absOff
  exact cpsTripleWithin_seq_same_cr hPC2 hOk



theorem extractT1Walk0to1Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next0 len0 toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff0 absOff1 : Nat)
    (hnext : next0 = regionBase + BitVec.ofNat 64 absOff1)
    (hsalign : regionBase.toNat % 8 = 0)

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
 :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk0Bne AfterT1Walk1Bne extractLinkedCode
      (t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next0 len0
          bs absOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next1 len1 : Word,
        (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next1 len1
          bs absOff1 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk1PrepCallOk_owned_of_decode_ambient spC s loadPtr regionBase lenW innerW endPtr
    next0 len0 toBuf isCreationPtr s7 bs absOff0 absOff1
    hnext hsalign hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1


set_option maxRecDepth 8000 in
/-- AfterT1Walk1Bne → AfterT1Walk2Bne under pure decode. -/
theorem extractT1Walk1to2Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next1 len1 toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff1 absOff2 : Nat)
    (hnext : next1 = regionBase + BitVec.ofNat 64 absOff2)
    (hsalign : regionBase.toNat % 8 = 0)

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
 :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk1Bne AfterT1Walk2Bne extractLinkedCode
      (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next1 len1
          bs absOff1 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next2 len2 : Word,
        (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next2 len2
          bs absOff2 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk2PrepCallOk_owned_of_decode_ambient spC s loadPtr regionBase lenW innerW endPtr
    next1 len1 toBuf isCreationPtr s7 bs absOff1 absOff2
    hnext hsalign hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2


set_option maxRecDepth 8000 in
/-- AfterT1Walk2Bne → AfterT1Walk3Bne under pure decode. -/
theorem extractT1Walk2to3Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next2 len2 toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff2 absOff3 : Nat)
    (hnext : next2 = regionBase + BitVec.ofNat 64 absOff3)
    (hsalign : regionBase.toNat % 8 = 0)

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
 :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk2Bne AfterT1Walk3Bne extractLinkedCode
      (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next2 len2
          bs absOff2 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next3 len3 : Word,
        (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next3 len3
          bs absOff3 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk3PrepCallOk_owned_of_decode_ambient spC s loadPtr regionBase lenW innerW endPtr
    next2 len2 toBuf isCreationPtr s7 bs absOff2 absOff3
    hnext hsalign hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3


set_option maxRecDepth 8000 in
theorem extractT1Walk3to4Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr next3 len3 toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff3 absOff4 : Nat)
    (hnext : next3 = regionBase + BitVec.ofNat 64 absOff4)
    (hsalign : regionBase.toNat % 8 = 0)
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
        ∀ j, j < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + j)) = true)
    (hll4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + j)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        endPtr next4 len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff4) endPtr = true) :
    cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
      AfterT1Walk3Bne AfterT1Walk4Bne extractLinkedCode
      (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next3 len3
          bs absOff3 **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next4 len4 : Word,
        (t14OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next4 len4
          bs absOff4 **
          midOwned spC s toBuf isCreationPtr s7) h) :=
  extractT1Walk4PrepCallOk_owned_of_decode_ambient spC s loadPtr regionBase lenW innerW endPtr
    next3 len3 toBuf isCreationPtr s7 bs absOff3 absOff4
    hnext hsalign hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4


set_option maxRecDepth 8000 in
theorem extractT1ToWalk4Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8))
    (absOff0 absOff1 absOff2 absOff3 absOff4 : Nat)
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
        ∀ j, j < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + j)) = true)
    (hll4 : ¬ BitVec.ult ((bs[absOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        absOff4 + 1 + ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff4 + 1 +
          ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ j, j < ((bs[absOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff4 + 1 + j)) = true)
    (hdec4 : ∃ next4 len4 : Word,
      rlpItemDecode bs absOff4 (regionBase + BitVec.ofNat 64 absOff4)
        endPtr next4 len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff4) endPtr = true)
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
    (hnext4 : ∀ (next3 len3 : Word),
      rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
        endPtr next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 absOff4)
 :
    cpsTripleWithin
      (((((((1 + (1 + (1 + 1))) + (1 + 1)) + ((1 + 87) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1)) +
        (((1 + (1 + 1)) + (1 + 87)) + 1))
      AfterSaveCursor AfterT1Walk4Bne extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW (1 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next4 len4 : Word,
        (t14OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next4 len4
          bs absOff4 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h0 := extractT1ToWalk0Ok_owned_of_decode_ambient spC s loadPtr regionBase lenW innerW
    cursor endPtr toBuf isCreationPtr s7 bs absOff0
    hcur hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  have h1 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk0Bne AfterT1Walk1Bne extractLinkedCode
        (fun h => ∃ next0 len0 : Word,
          (t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next0 len0
            bs absOff0 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next1 len1 : Word,
          (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next1 len1
            bs absOff1 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next0 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len0 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk0Bne AfterT1Walk1Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff0 (regionBase + BitVec.ofNat 64 absOff0)
              endPtr next0 len0⌝ **
            (t10OkRegsAmbient loadPtr regionBase lenW innerW endPtr next0 len0
              bs absOff0 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next1 len1 : Word,
            (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next1 len1
              bs absOff1 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk0to1Ok_owned_of_decode_ambient spC s loadPtr regionBase lenW
        innerW endPtr next0 len0 toBuf isCreationPtr s7 bs
        absOff0 absOff1
        (hnext1 next0 len0 hdecN) hsalign
        hoff1 hover1 hvalid1 hss1 hls1 hll1
        hdec1 hinb1
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t10OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next0 len0
            bs absOff0 h1 := by
          simp only [t10OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t10OkConcreteAmbient] using hOkC)
      have hRest :
          (t10OkRegsAmbient loadPtr regionBase lenW innerW endPtr next0 len0
            bs absOff0 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h2 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk1Bne AfterT1Walk2Bne extractLinkedCode
        (fun h => ∃ next1 len1 : Word,
          (t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next1 len1
            bs absOff1 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next2 len2 : Word,
          (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next2 len2
            bs absOff2 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next1 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len1 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk1Bne AfterT1Walk2Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff1 (regionBase + BitVec.ofNat 64 absOff1)
              endPtr next1 len1⌝ **
            (t11OkRegsAmbient loadPtr regionBase lenW innerW endPtr next1 len1
              bs absOff1 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next2 len2 : Word,
            (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next2 len2
              bs absOff2 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk1to2Ok_owned_of_decode_ambient spC s loadPtr regionBase lenW
        innerW endPtr next1 len1 toBuf isCreationPtr s7 bs
        absOff1 absOff2
        (hnext2 next1 len1 hdecN) hsalign
        hoff2 hover2 hvalid2 hss2 hls2 hll2
        hdec2 hinb2
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t11OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next1 len1
            bs absOff1 h1 := by
          simp only [t11OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t11OkConcreteAmbient] using hOkC)
      have hRest :
          (t11OkRegsAmbient loadPtr regionBase lenW innerW endPtr next1 len1
            bs absOff1 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h3 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk2Bne AfterT1Walk3Bne extractLinkedCode
        (fun h => ∃ next2 len2 : Word,
          (t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next2 len2
            bs absOff2 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next3 len3 : Word,
          (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next3 len3
            bs absOff3 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next2 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len2 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk2Bne AfterT1Walk3Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff2 (regionBase + BitVec.ofNat 64 absOff2)
              endPtr next2 len2⌝ **
            (t12OkRegsAmbient loadPtr regionBase lenW innerW endPtr next2 len2
              bs absOff2 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next3 len3 : Word,
            (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next3 len3
              bs absOff3 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk2to3Ok_owned_of_decode_ambient spC s loadPtr regionBase lenW
        innerW endPtr next2 len2 toBuf isCreationPtr s7 bs
        absOff2 absOff3
        (hnext3 next2 len2 hdecN) hsalign
        hoff3 hover3 hvalid3 hss3 hls3 hll3
        hdec3 hinb3
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t12OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next2 len2
            bs absOff2 h1 := by
          simp only [t12OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t12OkConcreteAmbient] using hOkC)
      have hRest :
          (t12OkRegsAmbient loadPtr regionBase lenW innerW endPtr next2 len2
            bs absOff2 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h4 :
      cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
        AfterT1Walk3Bne AfterT1Walk4Bne extractLinkedCode
        (fun h => ∃ next3 len3 : Word,
          (t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next3 len3
            bs absOff3 **
            midOwned spC s toBuf isCreationPtr s7) h)
        (fun h => ∃ next4 len4 : Word,
          (t14OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next4 len4
            bs absOff4 **
            midOwned spC s toBuf isCreationPtr s7) h) := by
    refine cpsTripleWithin_exists_pre_gen (fun next3 => ?_)
    refine cpsTripleWithin_exists_pre_gen (fun len3 => ?_)
    have hpure :
        cpsTripleWithin (((1 + (1 + 1)) + (1 + 87)) + 1)
          AfterT1Walk3Bne AfterT1Walk4Bne extractLinkedCode
          (⌜rlpItemDecode bs absOff3 (regionBase + BitVec.ofNat 64 absOff3)
              endPtr next3 len3⌝ **
            (t13OkRegsAmbient loadPtr regionBase lenW innerW endPtr next3 len3
              bs absOff3 **
              midOwned spC s toBuf isCreationPtr s7))
          (fun h => ∃ next4 len4 : Word,
            (t14OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next4 len4
              bs absOff4 **
              midOwned spC s toBuf isCreationPtr s7) h) := by
      refine cpsTripleWithin_pure_pre (fun hdecN => ?_)
      have hstep := extractT1Walk3to4Ok_owned_of_decode_ambient spC s loadPtr regionBase lenW
        innerW endPtr next3 len3 toBuf isCreationPtr s7 bs
        absOff3 absOff4
        (hnext4 next3 len3 hdecN) hsalign
        hoff4 hover4 hvalid4 hss4 hls4 hll4
        hdec4 hinb4
      refine cpsTripleWithin_weaken (fun st hp => by
        obtain ⟨h1, h2, hd, hu, hRegs, hM⟩ := hp
        have hOkC : t13OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next3 len3
            bs absOff3 h1 := by
          simp only [t13OkConcreteAmbient]
          exact (sepConj_pure_right h1).mpr ⟨hRegs, hdecN⟩
        exact ⟨h1, h2, hd, hu, hOkC, hM⟩) (fun _ hq => hq) hstep
    refine cpsTripleWithin_weaken (fun st hp => by
      obtain ⟨h1, h2, hd, hu, hOkC, hM⟩ := hp
      obtain ⟨hRegs, hdecN⟩ := (sepConj_pure_right h1).mp (by
        simpa only [t13OkConcreteAmbient] using hOkC)
      have hRest :
          (t13OkRegsAmbient loadPtr regionBase lenW innerW endPtr next3 len3
            bs absOff3 **
            midOwned spC s toBuf isCreationPtr s7) st :=
        ⟨h1, h2, hd, hu, hRegs, hM⟩
      exact (sepConj_pure_left st).mpr ⟨hdecN, hRest⟩) (fun _ hq => hq) hpure
  have h01 := cpsTripleWithin_seq_same_cr h0 h1
  have h012 := cpsTripleWithin_seq_same_cr h01 h2
  have h0123 := cpsTripleWithin_seq_same_cr h012 h3
  exact cpsTripleWithin_seq_same_cr h0123 h4


#print axioms extractT1ToWalk4Ok_owned_of_decode_ambient
#print axioms extractT1Walk0to1Ok_owned_of_decode_ambient

#print axioms extractT1Walk2PrepCallOk_owned_of_decode_ambient
#print axioms extractT1Walk3PrepCallOk_owned_of_decode_ambient
#print axioms extractT1Walk4PrepCallOk_owned_of_decode_ambient
#print axioms extractT1Walk3to4Ok_owned_of_decode_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
