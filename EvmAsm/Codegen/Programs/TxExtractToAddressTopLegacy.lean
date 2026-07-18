/-
  Extract mid: legacy (type 0) walk chain under ambient.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressLegacyWalk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeBranch
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext0

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

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

private theorem of_forall_regOwn7_leg
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

/-- Legacy start ambient (type=0 after branch). -/
def legacyStartFrame (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  afterSaveFrame txBase lenW innerW cursor endPtr txBytes **
    (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
theorem extractLegacyLoadArgs_framed
    (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) LegacyStart LegacyWalk0JalPc extractLinkedCode
      (legacyStartFrame txBase lenW innerW cursor endPtr txBytes)
      (legacyStartFrame txBase lenW innerW cursor endPtr txBytes) := by
  have h := extractLegacyLoadArgs cursor endPtr cursor endPtr
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion txBase txBytes **
      (.x12 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [legacyStartFrame, afterSaveFrame] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [legacyStartFrame, afterSaveFrame] at hq ⊢
    xperm_hyp hq) hF

/-- Stable ambient for legacy walks (s5/s6 hold cursor/end). -/
def legStable (txBase lenW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

private theorem legStable_pcFree (txBase lenW innerW endPtr cursor : Word) :
    (legStable txBase lenW innerW endPtr cursor).pcFree := by
  unfold legStable; pcf

def leg0Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk0) **
    bytesRegion txBase txBytes

def leg0OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    leg0Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg0OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  leg0OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractLegacyWalk0Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractLegacyWalk0Post txBase endPtr txBytes srcOff h →
      (leg0Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractLegacyWalk0Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : leg0Common txBase txBytes h1 := by
    simp only [leg0Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0Call_framed
    (txBase lenW innerW endPtr : Word)
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
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg0Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg0Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk0JalPc LinkLegacyWalk0 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk0Call txBase endPtr (0 : Word)
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
      have hok := wn0Outcome_to_okFail txBase endPtr txBytes srcOff _ hout
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hok⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      (leg0OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (leg0OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk0BneOk
  have hF := cpsTripleWithin_frameR
    (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk0) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [leg0OkRegs, legStable, leg0Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [leg0OkRegs, legStable, leg0Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk0BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg0OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [leg0OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractLegacyWalk0OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk0 AfterLegacyWalk0Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg0Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        leg0OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (legStable txBase lenW innerW endPtr cursor **
        leg0Common txBase txBytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (legStable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk0) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [leg0Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractLegacyWalk0BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [leg0OkRegs, leg0Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [leg0OkConcrete, leg0OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def leg1Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk1) **
    bytesRegion txBase txBytes

def leg1OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    leg1Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg1OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  leg1OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractLegacyWalk1Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractLegacyWalk1Post txBase endPtr txBytes srcOff h →
      (leg1Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractLegacyWalk1Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : leg1Common txBase txBytes h1 := by
    simp only [leg1Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractLegacyWalk1Prep_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk0Bne LegacyWalk1JalPc extractLinkedCode
      (leg0OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0)
      (legStable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractLegacyWalk1Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk0Bne LegacyWalk1JalPc extractLinkedCode
        (leg0OkRegs txBase lenW innerW endPtr next len txBytes srcOff0)
        (legStable txBase lenW innerW endPtr next **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [leg0OkRegs, legStable, leg0Common] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [legStable] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg0OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractLegacyWalk1Call_framed
    (txBase lenW innerW endPtr : Word)
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
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk1JalPc LinkLegacyWalk1 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg1Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk0) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg1Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk1JalPc LinkLegacyWalk1 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk1Call txBase endPtr (0 : Word)
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
      have hok := wn0Outcome_to_okFail txBase endPtr txBytes srcOff _ hout
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hok⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractLegacyWalk1BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk1 AfterLegacyWalk1Bne extractLinkedCode
      (leg1OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (leg1OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk1BneOk
  have hF := cpsTripleWithin_frameR
    (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk1) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [leg1OkRegs, legStable, leg1Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [leg1OkRegs, legStable, leg1Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractLegacyWalk1Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkLegacyWalk1 AfterLegacyWalk1Bne extractLinkedCode
      (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk1BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg1OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [leg1OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractLegacyWalk1OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk1 AfterLegacyWalk1Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg1Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        leg1OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (legStable txBase lenW innerW endPtr cursor **
        leg1Common txBase txBytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (legStable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk1) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [leg1Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractLegacyWalk1BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [leg1OkRegs, leg1Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [leg1OkConcrete, leg1OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def leg2Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk2) **
    bytesRegion txBase txBytes

def leg2OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    leg2Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg2OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  leg2OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractLegacyWalk2Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractLegacyWalk2Post txBase endPtr txBytes srcOff h →
      (leg2Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractLegacyWalk2Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : leg2Common txBase txBytes h1 := by
    simp only [leg2Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractLegacyWalk2Prep_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk1Bne LegacyWalk2JalPc extractLinkedCode
      (leg1OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0)
      (legStable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractLegacyWalk2Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk1Bne LegacyWalk2JalPc extractLinkedCode
        (leg1OkRegs txBase lenW innerW endPtr next len txBytes srcOff0)
        (legStable txBase lenW innerW endPtr next **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [leg1OkRegs, legStable, leg1Common] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [legStable] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg1OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractLegacyWalk2Call_framed
    (txBase lenW innerW endPtr : Word)
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
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk2JalPc LinkLegacyWalk2 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg2Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk1) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg2Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk2JalPc LinkLegacyWalk2 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk2Call txBase endPtr (0 : Word)
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
      have hok := wn0Outcome_to_okFail txBase endPtr txBytes srcOff _ hout
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hok⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractLegacyWalk2BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk2 AfterLegacyWalk2Bne extractLinkedCode
      (leg2OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (leg2OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk2BneOk
  have hF := cpsTripleWithin_frameR
    (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk2) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [leg2OkRegs, legStable, leg2Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [leg2OkRegs, legStable, leg2Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractLegacyWalk2Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkLegacyWalk2 AfterLegacyWalk2Bne extractLinkedCode
      (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk2BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg2OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [leg2OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractLegacyWalk2OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk2 AfterLegacyWalk2Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg2Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        leg2OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (legStable txBase lenW innerW endPtr cursor **
        leg2Common txBase txBytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (legStable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk2) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [leg2Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractLegacyWalk2BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [leg2OkRegs, leg2Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [leg2OkConcrete, leg2OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def leg3Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
    bytesRegion txBase txBytes

def leg3OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    leg3Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg3OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  leg3OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractLegacyWalk3Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractLegacyWalk3Post txBase endPtr txBytes srcOff h →
      (leg3Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractLegacyWalk3Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : leg3Common txBase txBytes h1 := by
    simp only [leg3Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractLegacyWalk3Prep_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk2Bne LegacyWalk3JalPc extractLinkedCode
      (leg2OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0)
      (legStable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractLegacyWalk3Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterLegacyWalk2Bne LegacyWalk3JalPc extractLinkedCode
        (leg2OkRegs txBase lenW innerW endPtr next len txBytes srcOff0)
        (legStable txBase lenW innerW endPtr next **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [leg2OkRegs, legStable, leg2Common] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [legStable] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg2OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractLegacyWalk3Call_framed
    (txBase lenW innerW endPtr : Word)
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
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ kk, kk < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + kk)) = true) :
    cpsTripleWithin (1 + 87) LegacyWalk3JalPc LinkLegacyWalk3 extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes)
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg3Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkLegacyWalk2) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      leg3Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) LegacyWalk3JalPc LinkLegacyWalk3 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_leg (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractLegacyWalk3Call txBase endPtr (0 : Word)
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
      have hok := wn0Outcome_to_okFail txBase endPtr txBytes srcOff _ hout
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hok⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
theorem extractLegacyWalk3BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk3 AfterLegacyWalk3Bne extractLinkedCode
      (leg3OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (leg3OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk3BneOk
  have hF := cpsTripleWithin_frameR
    (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [leg3OkRegs, legStable, leg3Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [leg3OkRegs, legStable, leg3Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractLegacyWalk3Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkLegacyWalk3 AfterLegacyWalk3Bne extractLinkedCode
      (leg3OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (leg3OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractLegacyWalk3BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg3OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [leg3OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractLegacyWalk3OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkLegacyWalk3 AfterLegacyWalk3Bne extractLinkedCode
      (legStable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        leg3Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        leg3OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (legStable txBase lenW innerW endPtr cursor **
        leg3Common txBase txBytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hSt, hCR⟩ := hp
      obtain ⟨hC, hR, hdc, huc, hCom, hOk⟩ := hCR
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hSt, hC, hR, hdc, huc, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (legStable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkLegacyWalk3) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [leg3Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractLegacyWalk3BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [leg3OkRegs, leg3Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [leg3OkConcrete, leg3OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractLegacyToHaveField_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff3 : Nat) :
    cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      (leg3OkConcrete txBase lenW innerW endPtr next len txBytes srcOff3)
      (legStable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff3) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len))) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff3
  let Pcore : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
      bytesRegion txBase txBytes **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)
  let Q : Assertion :=
    legStable txBase lenW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
      bytesRegion txBase txBytes **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
      (.x31 ↦ᵣ (next - len))
  have htemps : cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      (Pcore ** regOwn .x31) Q := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31) (fun t6Old => ?_)
    have h := extractLegacyToHaveField next len t6Old
    have hF := cpsTripleWithin_frameR
      (legStable txBase lenW innerW endPtr cursor **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
        bytesRegion txBase txBytes **
        (.x11 ↦ᵣ (0 : Word)))
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by dsimp only [Q] at hq ⊢; xperm_hyp hq) hF
  have hCore : cpsTripleWithin (1 + 1) AfterLegacyWalk3Bne HaveField extractLinkedCode
      (leg3OkRegs txBase lenW innerW endPtr next len txBytes srcOff3) Q := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, leg3OkRegs, leg3Common, legStable] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [Q] at hq ⊢; exact hq) htemps
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [leg3OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

#print axioms extractLegacyLoadArgs_framed
#print axioms extractLegacyWalk0Call_framed
#print axioms extractLegacyWalk0OkNested_bne
#print axioms extractLegacyWalk1Call_framed
#print axioms extractLegacyWalk2Call_framed
#print axioms extractLegacyWalk3Call_framed
#print axioms extractLegacyToHaveField_framed

end EvmAsm.Codegen.TxExtractToAddressSpec
