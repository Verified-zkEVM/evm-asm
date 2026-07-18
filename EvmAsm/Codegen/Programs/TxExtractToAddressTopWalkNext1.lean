/-
  Extract mid: type234 walk_next1 under ambient after wn0 OK.
  Prep + call + OkFail + OkNested BNE.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextArgs
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

/-- Stable ambient for walk_next1 (s5 holds current cursor after prep). -/
def wn1Stable (txBase lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

theorem wn1Stable_pcFree (txBase lenW typeW innerW endPtr cursor : Word) :
    (wn1Stable txBase lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn1Stable; pcf

/-- Common after walk_next1 (temps + ra link + bytes). -/
def wn1Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext1) **
    bytesRegion txBase txBytes

/-- OK concrete after wn1 BNE. -/
def wn1OkConcrete (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  wn1Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    wn1Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

set_option maxRecDepth 8000 in
/-- Frame after wn0 OK: prep MVs → WalkNext1JalPc with a0/a1 = next/end. -/
theorem extractWalkNext1Prep_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext0Bne WalkNext1JalPc extractLinkedCode
      (wn0OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0)
      (wn1Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractWalkNext1Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ typeW) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion txBase txBytes)
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn0OkConcrete, wn0Stable, wn0Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn1Stable] at hq ⊢
    xperm_hyp hq) hF

/-- Peel seven owned scratch registers. -/
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

/-- Leaf post → wn1Common ** wn0Outcome (reuse 6-way shape). -/
theorem extractWalkNext1Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractWalkNext1Post txBase endPtr txBytes srcOff h →
      (wn1Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractWalkNext1Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : wn1Common txBase txBytes h1 := by
    simp only [wn1Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
/-- walk_next1 call under jal-frame ambient (cursor = txBase+srcOff1). -/
theorem extractWalkNext1Call_type234
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff1 : Nat)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff1 < txBytes.length)
    (hover : txBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff1) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < txBytes.length ∧ txBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff1]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff1 + 1 +
          ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff1]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 extractLinkedCode
      (wn1Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff1) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff1)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion txBase txBytes)
      (wn1Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff1) **
        wn1Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff1) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff1
  let Pcore : Assertion :=
    wn1Stable txBase lenW typeW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    wn1Stable txBase lenW typeW innerW endPtr cursor **
      wn1Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff1
  have htemps :
      cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext1Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff1 LinkWalkNext0
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (wn1Stable txBase lenW typeW innerW endPtr cursor)
      (wn1Stable_pcFree _ _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, wn1Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (wn1Stable txBase lenW typeW innerW endPtr cursor **
            extractWalkNext1Post txBase endPtr txBytes srcOff1) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractWalkNext1Post_to_commonOutcome
        txBase endPtr txBytes srcOff1 _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      have hok := wn0Outcome_to_okFail txBase endPtr txBytes srcOff1 _ hout
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hok⟩) hF
  exact cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, Qassumed] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
/-- BNE a1=0 not-taken under wn1 ambient + concrete OK. -/
theorem extractWalkNext1BneOk_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne extractLinkedCode
      (wn1OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn1OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractWalkNext1BneOk
  have hF := cpsTripleWithin_frameR
    (wn1Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn1OkConcrete, wn1Stable, wn1Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn1OkConcrete, wn1Stable, wn1Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractWalkNext1Ok_bne
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (_hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne extractLinkedCode
      (wn1OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn1OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) :=
  extractWalkNext1BneOk_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff

set_option maxRecDepth 8000 in
/-- From ambient ** common ** `rlpWalkNextOk`, float ∃+pure and BNE. -/
theorem extractWalkNext1OkNested_bne
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne extractLinkedCode
      (wn1Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn1Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        wn1OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (wn1Stable txBase lenW typeW innerW endPtr cursor **
        wn1Common txBase txBytes **
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
        (wn1Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext1) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [wn1Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractWalkNext1Ok_bne txBase lenW typeW innerW endPtr next len
    txBytes srcOff hdec
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [wn1OkConcrete, wn1Common] at hp ⊢
    xperm_hyp hp) (fun h hq => ⟨next, len, hq⟩) h0

#print axioms extractWalkNext1Prep_framed
#print axioms extractWalkNext1Call_type234
#print axioms extractWalkNext1BneOk_framed
#print axioms extractWalkNext1OkNested_bne

end EvmAsm.Codegen.TxExtractToAddressSpec
