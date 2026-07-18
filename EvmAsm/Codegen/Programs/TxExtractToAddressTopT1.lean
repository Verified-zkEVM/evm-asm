/-
  Extract mid: type-1 walk chain under ambient (5 skips + SUB HaveField).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressT1Walk
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

theorem of_forall_regOwn7_t1
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

def t1StartFrame (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
    (.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
theorem extractT1LoadArgs_framed
    (txBase lenW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) T1Start T1Walk0JalPc extractLinkedCode
      (t1StartFrame txBase lenW innerW cursor endPtr txBytes)
      (t1StartFrame txBase lenW innerW cursor endPtr txBytes) := by
  have h := extractT1LoadArgs cursor endPtr cursor endPtr
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion txBase txBytes **
      (.x12 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t1StartFrame, afterSaveFrameTy] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t1StartFrame, afterSaveFrameTy] at hq ⊢
    xperm_hyp hq) hF

def t1Stable (txBase lenW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ (1 : Word)) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

theorem t1Stable_pcFree (txBase lenW innerW endPtr cursor : Word) :
    (t1Stable txBase lenW innerW endPtr cursor).pcFree := by
  unfold t1Stable; pcf

def t10Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk0) **
    bytesRegion txBase txBytes

def t10OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    t10Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t10OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t10OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractT1Walk0Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractT1Walk0Post txBase endPtr txBytes srcOff h →
      (t10Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractT1Walk0Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t10Common txBase txBytes h1 := by
    simp only [t10Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk0Call_framed
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
    cpsTripleWithin (1 + 87) T1Walk0JalPc LinkT1Walk0 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t10Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      t10Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk0JalPc LinkT1Walk0 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk0Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkWalkInit
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1Stable txBase lenW innerW endPtr cursor)
      (t1Stable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1Stable txBase lenW innerW endPtr cursor **
            extractT1Walk0Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk0Post_to_commonOutcome
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
theorem extractT1Walk0BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk0 AfterT1Walk0Bne extractLinkedCode
      (t10OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (t10OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk0BneOk
  have hF := cpsTripleWithin_frameR
    (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk0) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t10OkRegs, t1Stable, t10Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t10OkRegs, t1Stable, t10Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk0Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkT1Walk0 AfterT1Walk0Bne extractLinkedCode
      (t10OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (t10OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk0BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t10OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [t10OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk0OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk0 AfterT1Walk0Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t10Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        t10OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1Stable txBase lenW innerW endPtr cursor **
        t10Common txBase txBytes **
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
        (t1Stable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk0) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t10Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk0BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t10OkRegs, t10Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t10OkConcrete, t10OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def t11Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk1) **
    bytesRegion txBase txBytes

def t11OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    t11Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t11OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t11OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractT1Walk1Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractT1Walk1Post txBase endPtr txBytes srcOff h →
      (t11Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractT1Walk1Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t11Common txBase txBytes h1 := by
    simp only [t11Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk1Prep_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
      (t10OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractT1Walk1Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion txBase txBytes)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk0Bne T1Walk1JalPc extractLinkedCode
        (t10OkRegs txBase lenW innerW endPtr next len txBytes srcOff0)
        (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion txBase txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t10OkRegs, t1Stable, t10Common] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1Stable] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t10OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk1Call_framed
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
    cpsTripleWithin (1 + 87) T1Walk1JalPc LinkT1Walk1 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion txBase txBytes)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t11Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk0) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      t11Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk1JalPc LinkT1Walk1 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk1Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkT1Walk0
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1Stable txBase lenW innerW endPtr cursor)
      (t1Stable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1Stable txBase lenW innerW endPtr cursor **
            extractT1Walk1Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk1Post_to_commonOutcome
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
theorem extractT1Walk1BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      (t11OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (t11OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk1BneOk
  have hF := cpsTripleWithin_frameR
    (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk1) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t11OkRegs, t1Stable, t11Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t11OkRegs, t1Stable, t11Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk1Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      (t11OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (t11OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk1BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t11OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [t11OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk1OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk1 AfterT1Walk1Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t11Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        t11OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1Stable txBase lenW innerW endPtr cursor **
        t11Common txBase txBytes **
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
        (t1Stable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk1) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t11Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk1BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t11OkRegs, t11Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t11OkConcrete, t11OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def t12Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk2) **
    bytesRegion txBase txBytes

def t12OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    t12Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t12OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t12OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractT1Walk2Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractT1Walk2Post txBase endPtr txBytes srcOff h →
      (t12Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractT1Walk2Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t12Common txBase txBytes h1 := by
    simp only [t12Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk2Prep_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
      (t11OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractT1Walk2Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion txBase txBytes)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk1Bne T1Walk2JalPc extractLinkedCode
        (t11OkRegs txBase lenW innerW endPtr next len txBytes srcOff0)
        (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion txBase txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t11OkRegs, t1Stable, t11Common] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1Stable] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t11OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk2Call_framed
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
    cpsTripleWithin (1 + 87) T1Walk2JalPc LinkT1Walk2 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion txBase txBytes)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t12Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk1) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      t12Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk2JalPc LinkT1Walk2 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk2Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkT1Walk1
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1Stable txBase lenW innerW endPtr cursor)
      (t1Stable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1Stable txBase lenW innerW endPtr cursor **
            extractT1Walk2Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk2Post_to_commonOutcome
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
theorem extractT1Walk2BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      (t12OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (t12OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk2BneOk
  have hF := cpsTripleWithin_frameR
    (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk2) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t12OkRegs, t1Stable, t12Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t12OkRegs, t1Stable, t12Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk2Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      (t12OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (t12OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk2BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t12OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [t12OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk2OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk2 AfterT1Walk2Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t12Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        t12OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1Stable txBase lenW innerW endPtr cursor **
        t12Common txBase txBytes **
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
        (t1Stable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk2) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t12Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk2BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t12OkRegs, t12Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t12OkConcrete, t12OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def t13Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk3) **
    bytesRegion txBase txBytes

def t13OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    t13Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t13OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t13OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractT1Walk3Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractT1Walk3Post txBase endPtr txBytes srcOff h →
      (t13Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractT1Walk3Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t13Common txBase txBytes h1 := by
    simp only [t13Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk3Prep_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
      (t12OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractT1Walk3Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion txBase txBytes)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk2Bne T1Walk3JalPc extractLinkedCode
        (t12OkRegs txBase lenW innerW endPtr next len txBytes srcOff0)
        (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion txBase txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t12OkRegs, t1Stable, t12Common] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1Stable] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t12OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk3Call_framed
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
    cpsTripleWithin (1 + 87) T1Walk3JalPc LinkT1Walk3 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion txBase txBytes)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t13Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk2) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      t13Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk3JalPc LinkT1Walk3 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk3Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkT1Walk2
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1Stable txBase lenW innerW endPtr cursor)
      (t1Stable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1Stable txBase lenW innerW endPtr cursor **
            extractT1Walk3Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk3Post_to_commonOutcome
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
theorem extractT1Walk3BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      (t13OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (t13OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk3BneOk
  have hF := cpsTripleWithin_frameR
    (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk3) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t13OkRegs, t1Stable, t13Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t13OkRegs, t1Stable, t13Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk3Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      (t13OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (t13OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk3BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t13OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [t13OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk3OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk3 AfterT1Walk3Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t13Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        t13OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1Stable txBase lenW innerW endPtr cursor **
        t13Common txBase txBytes **
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
        (t1Stable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk3) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t13Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk3BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t13OkRegs, t13Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t13OkConcrete, t13OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

def t14Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
    bytesRegion txBase txBytes

def t14OkRegs (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    t14Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t14OkConcrete (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  t14OkRegs txBase lenW innerW endPtr next len txBytes srcOff **
    ⌜rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝

theorem extractT1Walk4Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractT1Walk4Post txBase endPtr txBytes srcOff h →
      (t14Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractT1Walk4Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : t14Common txBase txBytes h1 := by
    simp only [t14Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractT1Walk4Prep_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
      (t13OkConcrete txBase lenW innerW endPtr next len txBytes srcOff0)
      (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion txBase txBytes) := by
  let oldCursor := txBase + BitVec.ofNat 64 srcOff0
  have h := extractT1Walk4Prep next endPtr oldCursor (0 : Word)
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ (1 : Word)) **
      (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion txBase txBytes)
    (by pcf) h
  have hCore :
      cpsTripleWithin (1 + (1 + 1)) AfterT1Walk3Bne T1Walk4JalPc extractLinkedCode
        (t13OkRegs txBase lenW innerW endPtr next len txBytes srcOff0)
        (t1Stable txBase lenW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion txBase txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [t13OkRegs, t1Stable, t13Common] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [t1Stable] at hq ⊢
      xperm_hyp hq) hF
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t13OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

set_option maxRecDepth 8000 in
theorem extractT1Walk4Call_framed
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
    cpsTripleWithin (1 + 87) T1Walk4JalPc LinkT1Walk4 extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion txBase txBytes)
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t14Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  let Pcore : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkT1Walk3) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      t14Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) T1Walk4JalPc LinkT1Walk4 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_t1 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractT1Walk4Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkT1Walk3
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (t1Stable txBase lenW innerW endPtr cursor)
      (t1Stable_pcFree _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t1Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (t1Stable txBase lenW innerW endPtr cursor **
            extractT1Walk4Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractT1Walk4Post_to_commonOutcome
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
theorem extractT1Walk4BneOk_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      (t14OkRegs txBase lenW innerW endPtr next len txBytes srcOff)
      (t14OkRegs txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk4BneOk
  have hF := cpsTripleWithin_frameR
    (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk4) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t14OkRegs, t1Stable, t14Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t14OkRegs, t1Stable, t14Common] at hq ⊢
    xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1Walk4Ok_bne
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      (t14OkConcrete txBase lenW innerW endPtr next len txBytes srcOff)
      (t14OkConcrete txBase lenW innerW endPtr next len txBytes srcOff) := by
  have h0 := extractT1Walk4BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t14OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun st hq => by
    simp only [t14OkConcrete]
    exact (sepConj_pure_right st).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1Walk4OkNested_bne
    (txBase lenW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkT1Walk4 AfterT1Walk4Bne extractLinkedCode
      (t1Stable txBase lenW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        t14Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        t14OkConcrete txBase lenW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (t1Stable txBase lenW innerW endPtr cursor **
        t14Common txBase txBytes **
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
        (t1Stable txBase lenW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkT1Walk4) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      simp only [t14Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := extractT1Walk4BneOk_framed txBase lenW innerW endPtr next len
    txBytes srcOff
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [t14OkRegs, t14Common] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    simp only [t14OkConcrete, t14OkRegs]
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

set_option maxRecDepth 8000 in
theorem extractT1ToHaveField_framed
    (txBase lenW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff4 : Nat) :
    cpsTripleWithin 1 AfterT1Walk4Bne HaveField extractLinkedCode
      (t14OkConcrete txBase lenW innerW endPtr next len txBytes srcOff4)
      (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff4) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len))) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff4
  let Pcore : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
      bytesRegion txBase txBytes **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)
  let Q : Assertion :=
    t1Stable txBase lenW innerW endPtr cursor **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
      bytesRegion txBase txBytes **
      (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
      (.x31 ↦ᵣ (next - len))
  have htemps : cpsTripleWithin 1 AfterT1Walk4Bne HaveField extractLinkedCode
      (Pcore ** regOwn .x31) Q := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31) (fun t6Old => ?_)
    have h := extractT1ToHaveField next len t6Old
    have hF := cpsTripleWithin_frameR
      (t1Stable txBase lenW innerW endPtr cursor **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
        bytesRegion txBase txBytes **
        (.x11 ↦ᵣ (0 : Word)))
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore] at hp ⊢; xperm_hyp hp)
      (fun _ hq => by dsimp only [Q] at hq ⊢; xperm_hyp hq) hF
  have hCore :
      cpsTripleWithin 1 AfterT1Walk4Bne HaveField extractLinkedCode
        (t14OkRegs txBase lenW innerW endPtr next len txBytes srcOff4)
        (t1Stable txBase lenW innerW endPtr (txBase + BitVec.ofNat 64 srcOff4) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x31 ↦ᵣ (next - len))) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, t14OkRegs, t14Common, t1Stable] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [Q] at hq ⊢; exact hq) htemps
  refine cpsTripleWithin_weaken (fun st hp => by
    simp only [t14OkConcrete] at hp
    exact (sepConj_pure_right st).mp hp |>.1) (fun _ hq => hq) hCore

#print axioms extractT1LoadArgs_framed
#print axioms extractT1Walk0Call_framed
#print axioms extractT1Walk0OkNested_bne
#print axioms extractT1Walk4Call_framed
#print axioms extractT1ToHaveField_framed

end EvmAsm.Codegen.TxExtractToAddressSpec
