/-
  Ambient dual of legacy walk0 call/BNE/Ok under split bases.
  x8=loadPtr; bytesRegion/cursor use regionBase + absOff.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressLegacyWalk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacyAmbient
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

theorem extractLegacyWalk0Post_to_commonOutcome_ambient
    (regionBase endPtr : Word) (bs : List (BitVec 8)) (absOff : Nat) :
    ∀ h, extractLegacyWalk0Post regionBase endPtr bs absOff h →
      (leg0CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) h := by
  intro h hp
  simp only [extractLegacyWalk0Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : leg0CommonAmbient regionBase bs h1 := by
    simp only [leg0CommonAmbient]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
/-- leg0 call ambient posting Outcome (any a2Old). -/
theorem extractLegacyWalk0Call_a2_outcome_ambient
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
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs)
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        leg0CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  let Pcore : Assertion :=
    legStableAmbient loadPtr lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs
  let Qassumed : Assertion :=
    legStableAmbient loadPtr lenW innerW endPtr cursor **
      leg0CommonAmbient regionBase bs **
      wn0Outcome regionBase endPtr bs absOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk0Call regionBase endPtr a2Old
      t0 t1 t2 t3 t4 t5 t6 bs absOff LinkWalkInit
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (legStableAmbient loadPtr lenW innerW endPtr cursor)
      (legStableAmbient_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, legStableAmbient, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (legStableAmbient loadPtr lenW innerW endPtr cursor **
            extractLegacyWalk0Post regionBase endPtr bs absOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractLegacyWalk0Post_to_commonOutcome_ambient
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
theorem extractLegacyWalk0Call_owned_a2_outcome_ambient
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
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7)
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        leg0CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractLegacyWalk0Call_a2_outcome_ambient loadPtr regionBase
    lenW innerW endPtr a2Old bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0BneOk_framed_ambient
    (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      (leg0OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff)
      (leg0OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len
        bs absOff) := by
  have h0 := extractLegacyWalk0BneOk
  have hF := cpsTripleWithin_frameR
    (legStableAmbient loadPtr lenW innerW endPtr
        (regionBase + BitVec.ofNat 64 absOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk0) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [leg0OkRegsAmbient, legStableAmbient, leg0CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [leg0OkRegsAmbient, legStableAmbient, leg0CommonAmbient] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0OkNested_bne_ambient
    (loadPtr regionBase lenW innerW endPtr : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        leg0CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff)
      (fun h => ∃ next len : Word,
        leg0OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff h) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (legStableAmbient loadPtr lenW innerW endPtr cursor **
        leg0CommonAmbient regionBase bs **
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
        (legStableAmbient loadPtr lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk0) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [leg0CommonAmbient] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractLegacyWalk0BneOk_framed_ambient loadPtr regionBase
    lenW innerW endPtr next len bs absOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [leg0OkRegsAmbient, leg0CommonAmbient] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [leg0OkConcreteAmbient, leg0OkRegsAmbient]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0OkNested_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        leg0CommonAmbient regionBase bs **
        rlpWalkNextOk (regionBase + BitVec.ofNat 64 absOff) endPtr bs absOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (leg0OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next len
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractLegacyWalk0OkNested_bne_ambient loadPtr regionBase
    lenW innerW endPtr bs absOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

set_option maxRecDepth 8000 in
/-- leg0 call+Ok ambient under pure decode (a2=0 from loadArgs). -/
theorem extractLegacyWalk0CallOk_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 : Word)
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
    cpsTripleWithin ((1 + 87) + 1) LegacyWalk0JalPc AfterLegacyWalk0Bne
      extractLinkedCode
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next0 len0 : Word,
        (leg0OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next0 len0
          bs absOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hCall := extractLegacyWalk0Call_owned_a2_outcome_ambient spC s loadPtr
    regionBase lenW innerW endPtr (0 : Word) toBuf isCreationPtr s7 bs absOff
    hsalign hoff hover hvalid hss hls hll
  have hCall2 :
      cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
        (legStableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs **
          midOwned spC s toBuf isCreationPtr s7)
        (legStableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff) **
          leg0CommonAmbient regionBase bs **
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
  have hOk := extractLegacyWalk0OkNested_owned_ambient spC s loadPtr regionBase
    lenW innerW endPtr toBuf isCreationPtr s7 bs absOff
  exact cpsTripleWithin_seq_same_cr hCall2 hOk

/-- Reshape legacy start ambient (+ midOwned) to leg0 CallOk pre under hcur. -/
theorem legacyStartFrameAmbient_to_leg0CallPre
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff0 : Nat)
    (hcur : cursor = regionBase + BitVec.ofNat 64 absOff0) :
    ∀ h, (legacyStartFrameAmbient loadPtr regionBase lenW innerW cursor endPtr bs **
        midOwned spC s toBuf isCreationPtr s7) h →
      (legStableAmbient loadPtr lenW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff0) **
        (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff0)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs **
        midOwned spC s toBuf isCreationPtr s7) h := by
  intro h hp
  let Core : Assertion :=
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion regionBase bs **
      (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff0)) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff0)) **
      (.x22 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (0 : Word))
  let Tail : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** midOwned spC s toBuf isCreationPtr s7
  have hp1 : ((Core ** (.x5 ↦ᵣ (0 : Word))) ** Tail) h := by
    simp only [hcur, legacyStartFrameAmbient, afterSaveFrameTyAmbient,
      Core, Tail] at hp ⊢
    xperm_hyp hp
  obtain ⟨ha, hb, hda, hua, hCoreX5, hTail⟩ := hp1
  obtain ⟨hc, hd', hdc, huc, hCore, hx5⟩ := hCoreX5
  have hx5' : regOwn .x5 hd' := ⟨(0 : Word), hx5⟩
  have hp2 : ((Core ** regOwn .x5) ** Tail) h :=
    ⟨ha, hb, hda, hua, ⟨hc, hd', hdc, huc, hCore, hx5'⟩, hTail⟩
  simp only [legStableAmbient, Core, Tail] at hp2 ⊢
  xperm_hyp hp2

set_option maxRecDepth 8000 in
/-- Legacy AfterSave → AfterLegacyWalk0Bne ambient under pure decode. -/
theorem extractLegacyToWalk0Ok_owned_of_decode_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (bs : List (BitVec 8)) (absOff0 : Nat)
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
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 absOff0) endPtr = true) :
    cpsTripleWithin (((1 + 1) + (1 + 1)) + ((1 + 87) + 1))
      AfterSaveCursor AfterLegacyWalk0Bne extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next0 len0 : Word,
        (leg0OkConcreteAmbient loadPtr regionBase lenW innerW endPtr next0 len0
          bs absOff0 **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have hBr := extractTypeBranchLegacy_framed_ambient loadPtr regionBase
    lenW innerW cursor endPtr bs
  have hBrF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) hBr
  have hBr' :
      cpsTripleWithin (1 + 1) AfterSaveCursor LegacyStart extractLinkedCode
        (afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
            cursor endPtr bs **
          (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
          midOwned spC s toBuf isCreationPtr s7)
        (legacyStartFrameAmbient loadPtr regionBase lenW innerW cursor endPtr bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        simp only [legacyStartFrameAmbient] at hq ⊢
        xperm_hyp hq) hBrF
  have hLoad := extractLegacyLoadArgs_framed_ambient loadPtr regionBase
    lenW innerW cursor endPtr bs
  have hLoadF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) hLoad
  have hBrLoad := cpsTripleWithin_seq_same_cr hBr' hLoadF
  have hBrLoad2 :
      cpsTripleWithin ((1 + 1) + (1 + 1)) AfterSaveCursor LegacyWalk0JalPc
        extractLinkedCode
        (afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
            cursor endPtr bs **
          (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
          midOwned spC s toBuf isCreationPtr s7)
        (legStableAmbient loadPtr lenW innerW endPtr
            (regionBase + BitVec.ofNat 64 absOff0) **
          (.x10 ↦ᵣ (regionBase + BitVec.ofNat 64 absOff0)) **
          (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs **
          midOwned spC s toBuf isCreationPtr s7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq =>
      legacyStartFrameAmbient_to_leg0CallPre spC s loadPtr regionBase
        lenW innerW cursor endPtr toBuf isCreationPtr s7 bs absOff0 hcur _ hq)
      hBrLoad
  have hCallOk := extractLegacyWalk0CallOk_owned_of_decode_ambient spC s
    loadPtr regionBase lenW innerW endPtr toBuf isCreationPtr s7 bs absOff0
    hsalign hoff0 hover0 hvalid0 hss0 hls0 hll0 hdec0 hinb0
  exact cpsTripleWithin_seq_same_cr hBrLoad2 hCallOk

#print axioms extractLegacyWalk0Call_a2_outcome_ambient
#print axioms extractLegacyWalk0CallOk_owned_of_decode_ambient
#print axioms extractLegacyToWalk0Ok_owned_of_decode_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
