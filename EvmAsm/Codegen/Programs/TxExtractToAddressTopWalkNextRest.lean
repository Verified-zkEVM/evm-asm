/-
  Extract mid: type234 walk_next 2..5 under ambient after prior OK.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextRest
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext1

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

private theorem of_forall_regOwn7_wn
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


/-- Stable ambient for walk_next2. -/
def wn2Stable (txBase lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

private theorem wn2Stable_pcFree (txBase lenW typeW innerW endPtr cursor : Word) :
    (wn2Stable txBase lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn2Stable; pcf

def wn2Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext2) **
    bytesRegion txBase txBytes

def wn2OkConcrete (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  wn2Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    wn2Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

set_option maxRecDepth 8000 in
theorem extractWalkNext2Prep_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext1Bne WalkNext2JalPc extractLinkedCode
      (wn1OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0)
      (wn2Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext1) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractWalkNext2Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ typeW) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext1) ** bytesRegion txBase txBytes)
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn1OkConcrete, wn1Stable, wn1Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn2Stable] at hq ⊢
    xperm_hyp hq) hF

theorem extractWalkNext2Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractWalkNext2Post txBase endPtr txBytes srcOff h →
      (wn2Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractWalkNext2Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : wn2Common txBase txBytes h1 := by
    simp only [wn2Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractWalkNext2Call_type234
    (txBase lenW typeW innerW endPtr : Word)
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
    cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 extractLinkedCode
      (wn2Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext1) ** bytesRegion txBase txBytes)
      (wn2Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn2Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    wn2Stable txBase lenW typeW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext1) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    wn2Stable txBase lenW typeW innerW endPtr cursor **
      wn2Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_wn (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext2Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkWalkNext1
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (wn2Stable txBase lenW typeW innerW endPtr cursor)
      (wn2Stable_pcFree _ _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, wn2Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (wn2Stable txBase lenW typeW innerW endPtr cursor **
            extractWalkNext2Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractWalkNext2Post_to_commonOutcome
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
theorem extractWalkNext2BneOk_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne extractLinkedCode
      (wn2OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn2OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractWalkNext2BneOk
  have hF := cpsTripleWithin_frameR
    (wn2Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn2OkConcrete, wn2Stable, wn2Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn2OkConcrete, wn2Stable, wn2Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext2Ok_bne
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (_hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne extractLinkedCode
      (wn2OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn2OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) :=
  extractWalkNext2BneOk_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff

set_option maxRecDepth 8000 in
theorem extractWalkNext2OkNested_bne
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne extractLinkedCode
      (wn2Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn2Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        wn2OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (wn2Stable txBase lenW typeW innerW endPtr cursor **
        wn2Common txBase txBytes **
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
        (wn2Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext2) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [wn2Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractWalkNext2Ok_bne txBase lenW typeW innerW endPtr next len
    txBytes srcOff hdec
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [wn2OkConcrete, wn2Common] at hp ⊢
    xperm_hyp hp) (fun h hq => ⟨next, len, hq⟩) h0

/-- Stable ambient for walk_next3. -/
def wn3Stable (txBase lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

private theorem wn3Stable_pcFree (txBase lenW typeW innerW endPtr cursor : Word) :
    (wn3Stable txBase lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn3Stable; pcf

def wn3Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext3) **
    bytesRegion txBase txBytes

def wn3OkConcrete (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  wn3Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    wn3Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

set_option maxRecDepth 8000 in
theorem extractWalkNext3Prep_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext2Bne WalkNext3JalPc extractLinkedCode
      (wn2OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0)
      (wn3Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext2) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractWalkNext3Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ typeW) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext2) ** bytesRegion txBase txBytes)
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn2OkConcrete, wn2Stable, wn2Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn3Stable] at hq ⊢
    xperm_hyp hq) hF

theorem extractWalkNext3Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractWalkNext3Post txBase endPtr txBytes srcOff h →
      (wn3Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractWalkNext3Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : wn3Common txBase txBytes h1 := by
    simp only [wn3Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractWalkNext3Call_type234
    (txBase lenW typeW innerW endPtr : Word)
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
    cpsTripleWithin (1 + 87) WalkNext3JalPc LinkWalkNext3 extractLinkedCode
      (wn3Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext2) ** bytesRegion txBase txBytes)
      (wn3Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn3Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    wn3Stable txBase lenW typeW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext2) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    wn3Stable txBase lenW typeW innerW endPtr cursor **
      wn3Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) WalkNext3JalPc LinkWalkNext3 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_wn (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext3Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkWalkNext2
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (wn3Stable txBase lenW typeW innerW endPtr cursor)
      (wn3Stable_pcFree _ _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, wn3Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (wn3Stable txBase lenW typeW innerW endPtr cursor **
            extractWalkNext3Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractWalkNext3Post_to_commonOutcome
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
theorem extractWalkNext3BneOk_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne extractLinkedCode
      (wn3OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn3OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractWalkNext3BneOk
  have hF := cpsTripleWithin_frameR
    (wn3Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn3OkConcrete, wn3Stable, wn3Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn3OkConcrete, wn3Stable, wn3Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext3Ok_bne
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (_hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne extractLinkedCode
      (wn3OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn3OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) :=
  extractWalkNext3BneOk_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff

set_option maxRecDepth 8000 in
theorem extractWalkNext3OkNested_bne
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne extractLinkedCode
      (wn3Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn3Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        wn3OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (wn3Stable txBase lenW typeW innerW endPtr cursor **
        wn3Common txBase txBytes **
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
        (wn3Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext3) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [wn3Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractWalkNext3Ok_bne txBase lenW typeW innerW endPtr next len
    txBytes srcOff hdec
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [wn3OkConcrete, wn3Common] at hp ⊢
    xperm_hyp hp) (fun h hq => ⟨next, len, hq⟩) h0

/-- Stable ambient for walk_next4. -/
def wn4Stable (txBase lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

private theorem wn4Stable_pcFree (txBase lenW typeW innerW endPtr cursor : Word) :
    (wn4Stable txBase lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn4Stable; pcf

def wn4Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext4) **
    bytesRegion txBase txBytes

def wn4OkConcrete (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  wn4Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    wn4Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

set_option maxRecDepth 8000 in
theorem extractWalkNext4Prep_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext3Bne WalkNext4JalPc extractLinkedCode
      (wn3OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0)
      (wn4Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext3) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractWalkNext4Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ typeW) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext3) ** bytesRegion txBase txBytes)
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn3OkConcrete, wn3Stable, wn3Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn4Stable] at hq ⊢
    xperm_hyp hq) hF

theorem extractWalkNext4Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractWalkNext4Post txBase endPtr txBytes srcOff h →
      (wn4Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractWalkNext4Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : wn4Common txBase txBytes h1 := by
    simp only [wn4Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractWalkNext4Call_type234
    (txBase lenW typeW innerW endPtr : Word)
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
    cpsTripleWithin (1 + 87) WalkNext4JalPc LinkWalkNext4 extractLinkedCode
      (wn4Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext3) ** bytesRegion txBase txBytes)
      (wn4Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn4Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    wn4Stable txBase lenW typeW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext3) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    wn4Stable txBase lenW typeW innerW endPtr cursor **
      wn4Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) WalkNext4JalPc LinkWalkNext4 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_wn (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext4Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkWalkNext3
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (wn4Stable txBase lenW typeW innerW endPtr cursor)
      (wn4Stable_pcFree _ _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, wn4Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (wn4Stable txBase lenW typeW innerW endPtr cursor **
            extractWalkNext4Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractWalkNext4Post_to_commonOutcome
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
theorem extractWalkNext4BneOk_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne extractLinkedCode
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractWalkNext4BneOk
  have hF := cpsTripleWithin_frameR
    (wn4Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn4OkConcrete, wn4Stable, wn4Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn4OkConcrete, wn4Stable, wn4Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext4Ok_bne
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (_hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne extractLinkedCode
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) :=
  extractWalkNext4BneOk_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff

set_option maxRecDepth 8000 in
theorem extractWalkNext4OkNested_bne
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne extractLinkedCode
      (wn4Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn4Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        wn4OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (wn4Stable txBase lenW typeW innerW endPtr cursor **
        wn4Common txBase txBytes **
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
        (wn4Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext4) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [wn4Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractWalkNext4Ok_bne txBase lenW typeW innerW endPtr next len
    txBytes srcOff hdec
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [wn4OkConcrete, wn4Common] at hp ⊢
    xperm_hyp hp) (fun h hq => ⟨next, len, hq⟩) h0

/-- Stable ambient for walk_next5. -/
def wn5Stable (txBase lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

private theorem wn5Stable_pcFree (txBase lenW typeW innerW endPtr cursor : Word) :
    (wn5Stable txBase lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn5Stable; pcf

def wn5Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
    bytesRegion txBase txBytes

def wn5OkConcrete (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  wn5Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    wn5Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

set_option maxRecDepth 8000 in
theorem extractWalkNext5Prep_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext4Bne WalkNext5JalPc extractLinkedCode
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0)
      (wn5Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractWalkNext5Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ typeW) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes)
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn4OkConcrete, wn4Stable, wn4Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn5Stable] at hq ⊢
    xperm_hyp hq) hF

theorem extractWalkNext5Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractWalkNext5Post txBase endPtr txBytes srcOff h →
      (wn5Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractWalkNext5Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : wn5Common txBase txBytes h1 := by
    simp only [wn5Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractWalkNext5Call_type234
    (txBase lenW typeW innerW endPtr : Word)
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
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
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
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
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
    refine of_forall_regOwn7_wn (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext5Call txBase endPtr (0 : Word)
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
theorem extractWalkNext5BneOk_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne extractLinkedCode
      (wn5OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn5OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractWalkNext5BneOk
  have hF := cpsTripleWithin_frameR
    (wn5Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn5OkConcrete, wn5Stable, wn5Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn5OkConcrete, wn5Stable, wn5Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext5Ok_bne
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (_hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne extractLinkedCode
      (wn5OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn5OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) :=
  extractWalkNext5BneOk_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff

set_option maxRecDepth 8000 in
theorem extractWalkNext5OkNested_bne
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne extractLinkedCode
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn5Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        wn5OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (wn5Stable txBase lenW typeW innerW endPtr cursor **
        wn5Common txBase txBytes **
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
        (wn5Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext5) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [wn5Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractWalkNext5Ok_bne txBase lenW typeW innerW endPtr next len
    txBytes srcOff hdec
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [wn5OkConcrete, wn5Common] at hp ⊢
    xperm_hyp hp) (fun h hq => ⟨next, len, hq⟩) h0

#print axioms extractWalkNext2Prep_framed
#print axioms extractWalkNext2Call_type234
#print axioms extractWalkNext2OkNested_bne
#print axioms extractWalkNext3Prep_framed
#print axioms extractWalkNext3Call_type234
#print axioms extractWalkNext3OkNested_bne
#print axioms extractWalkNext4Prep_framed
#print axioms extractWalkNext4Call_type234
#print axioms extractWalkNext4OkNested_bne
#print axioms extractWalkNext5Prep_framed
#print axioms extractWalkNext5Call_type234
#print axioms extractWalkNext5OkNested_bne

end EvmAsm.Codegen.TxExtractToAddressSpec
