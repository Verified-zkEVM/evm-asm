/-
  Extract mid: first type234 walk_next under ambient.
  Call + 6-way→OkFail + BNE framed.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressTopType234

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

/-- Stable ambient walk_next0 does not touch (s5/s6 keep pre-call cursor/end). -/
def wn0Stable (txBase lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

theorem wn0Stable_pcFree (txBase lenW typeW innerW endPtr cursor : Word) :
    (wn0Stable txBase lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn0Stable; pcf

/-- Peel seven owned scratch registers (HeaderFields local mirror). -/
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

/-- Common after walk_next (temps regOwn + ra link + bytes). -/
def wn0Common (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext0) **
    bytesRegion txBase txBytes

/-- 6-way raw outcome (matches leaf post disjunct). -/
def wn0Outcome (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    Assertion := fun h =>
  rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
  (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
  (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len⌝) h)

/-- Normalized: OK (`rlpWalkNextOk`) or nonzero status fail. -/
def wn0OkFail (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    Assertion := fun h =>
  rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h ∨
  (∃ status : Word,
    (((.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ status) **
      (.x12 ↦ᵣ (0 : Word)) ** ⌜status ≠ (0 : Word)⌝) h))

/-- 6-way → OkFail (HeaderFields hesrNextOutcome_to_norm style). -/
theorem wn0Outcome_to_okFail (txBase endPtr : Word) (txBytes : List (BitVec 8))
    (srcOff : Nat) :
    ∀ h, wn0Outcome txBase endPtr txBytes srcOff h →
      wn0OkFail txBase endPtr txBytes srcOff h := by
  intro h hout
  unfold wn0Outcome at hout
  rcases hout with hOk | hb2 | hb3 | hb4 | hb5 | hb6
  · exact Or.inl hOk
  · refine Or.inr ⟨2, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb2
    exact fun h' ⟨he, _⟩ => ⟨he, by decide⟩
  · refine Or.inr ⟨3, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb3
    exact fun h' ⟨he, _⟩ => ⟨he, by decide⟩
  · refine Or.inr ⟨4, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb4
    exact fun h' ⟨he, _⟩ => ⟨he, by decide⟩
  · refine Or.inr ⟨5, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb5
    exact fun h' ⟨he, _⟩ => ⟨he, by decide⟩
  · refine Or.inr ⟨6, ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hb6
    exact fun h' ⟨he, _⟩ => ⟨he, by decide⟩

/-- Honest drop-fail on the 6-way outcome: pure decode + in-bounds kill
    status-2 OOB and status-3..6 `¬∃decode` arms. Prefer this over universal
    `hok : OkFail → Ok` (false as ∀h — OkFail strips the pure). -/
theorem wn0Outcome_drop_fail_of_decode
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hdec : ∃ next len : Word,
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (txBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    ∀ h, wn0Outcome txBase endPtr txBytes srcOff h →
      rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff h := by
  intro h hout
  unfold wn0Outcome at hout
  rcases hout with hOk | hb2 | hb3 | hb4 | hb5 | hb6
  · exact hOk
  · -- status 2: pure ¬ult; right-assoc A ** (B ** (C ** pure))
    obtain ⟨_, h2, _, _, _, hBC⟩ := hb2
    obtain ⟨_, h4, _, _, _, hCP⟩ := hBC
    exact absurd hinb ((sepConj_pure_right _).1 hCP).2
  · obtain ⟨_, h2, _, _, _, hBC⟩ := hb3
    obtain ⟨_, h4, _, _, _, hCP⟩ := hBC
    exact absurd hdec ((sepConj_pure_right _).1 hCP).2
  · obtain ⟨_, h2, _, _, _, hBC⟩ := hb4
    obtain ⟨_, h4, _, _, _, hCP⟩ := hBC
    exact absurd hdec ((sepConj_pure_right _).1 hCP).2
  · obtain ⟨_, h2, _, _, _, hBC⟩ := hb5
    obtain ⟨_, h4, _, _, _, hCP⟩ := hBC
    exact absurd hdec ((sepConj_pure_right _).1 hCP).2
  · obtain ⟨_, h2, _, _, _, hBC⟩ := hb6
    obtain ⟨_, h4, _, _, _, hCP⟩ := hBC
    exact absurd hdec ((sepConj_pure_right _).1 hCP).2

/-- Leaf post → wn0Common ** wn0Outcome. -/
theorem extractWalkNext0Post_to_commonOutcome
    (txBase endPtr : Word) (txBytes : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, extractWalkNext0Post txBase endPtr txBytes srcOff h →
      (wn0Common txBase txBytes ** wn0Outcome txBase endPtr txBytes srcOff) h := by
  intro h hp
  simp only [extractWalkNext0Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : wn0Common txBase txBytes h1 := by
    simp only [wn0Common]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
/-- walk_next0 call under type234StartFrame ambient (peel regOwn temps).
    Requires cursor = txBase + srcOff. -/
theorem extractWalkNext0Call_type234
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
    cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
      (type234StartFrame txBase lenW typeW innerW
        (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes)
      (wn0Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  -- Pre shape for of_forall7 (x5 as regOwn; type234 has x5↦1 → regOwn).
  let Pcore : Assertion :=
    (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ typeW) **
      (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion txBase txBytes
  let Qassumed : Assertion :=
    wn0Stable txBase lenW typeW innerW endPtr cursor **
      wn0Common txBase txBytes **
      wn0OkFail txBase endPtr txBytes srcOff
  have htemps :
      cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7 (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext0Call txBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 txBytes srcOff LinkWalkInit
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (wn0Stable txBase lenW typeW innerW endPtr cursor)
      (wn0Stable_pcFree _ _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, wn0Stable, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (wn0Stable txBase lenW typeW innerW endPtr cursor **
            extractWalkNext0Post txBase endPtr txBytes srcOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractWalkNext0Post_to_commonOutcome
        txBase endPtr txBytes srcOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      have hok := wn0Outcome_to_okFail txBase endPtr txBytes srcOff _ hout
      refine ⟨hA, hP, hd, hu, hamb, ?_⟩
      exact ⟨hC, hO, hdc, huc, hcom, hok⟩) hF
  -- type234StartFrame → Pcore ** regOwns (x5↦1 → regOwn)
  refine cpsTripleWithin_weaken (fun s hp => by
    dsimp only [Pcore, Qassumed, type234StartFrame, afterSaveFrameTy] at hp ⊢
    have hro : ∀ t, (.x5 ↦ᵣ (1 : Word)) t → regOwn .x5 t := fun _ hx => ⟨1, hx⟩
    -- reassoc hp to put x5 rightmost among a mono chain, convert, xperm to goal
    have hp1 :
        (Pcore ** (.x5 ↦ᵣ (1 : Word)) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) s := by
      dsimp only [Pcore] at hp ⊢
      xperm_hyp hp
    have hp2 :=
      sepConj_mono (fun _ x => x)
        (sepConj_mono hro (fun _ x => x)) s hp1
    dsimp only [Pcore] at hp2 ⊢
    xperm_hyp hp2) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

set_option maxRecDepth 8000 in
/-- BNE a1=0 not-taken under stable + common + concrete OK regs. -/
theorem extractWalkNext0BneOk_framed
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      (wn0Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len))
      (wn0Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)) := by
  have h0 := extractWalkNext0BneOk
  have hF := cpsTripleWithin_frameR
    (wn0Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [wn0Stable, wn0Common] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [wn0Stable, wn0Common] at hq ⊢
    xperm_hyp hq) hF

/-- OK concrete under ambient for exists_pre. -/
def wn0OkConcrete (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) : Assertion :=
  wn0Stable txBase lenW typeW innerW endPtr (txBase + BitVec.ofNat 64 srcOff) **
    wn0Common txBase txBytes **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

set_option maxRecDepth 8000 in
/-- From rlpWalkNextOk pure+regs, BNE under ambient.
    Needs pure decode dropped to expose x11=0. -/
theorem extractWalkNext0Ok_bne
    (txBase lenW typeW innerW endPtr next len : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (_hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      (wn0OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff)
      (wn0OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff) := by
  exact extractWalkNext0BneOk_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff

set_option maxRecDepth 8000 in
/-- From ambient ** common ** `rlpWalkNextOk`, float ∃+pure and BNE not-taken
    → AfterWalkNext0Bne with ∃ next,len concrete OK regs. -/
theorem extractWalkNext0OkNested_bne
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      (wn0Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        wn0OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff h) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff
  -- Float ∃ next,len out of rlpWalkNextOk.
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      (wn0Stable txBase lenW typeW innerW endPtr cursor **
        wn0Common txBase txBytes **
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
  -- pure front for pure_pre (HeaderFields style).
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode txBytes srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        (wn0Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len))))
    (fun h hp => by
      -- hp : stable ** common ** (x10 ** x11 ** x12 ** pure)
      simp only [wn0Common] at hp
      xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  -- Rest is wn0OkConcrete after xperm (x11/x0 with stable/common/regs).
  have h0 := extractWalkNext0Ok_bne txBase lenW typeW innerW endPtr next len
    txBytes srcOff hdec
  refine cpsTripleWithin_weaken (fun h hp => by
    simp only [wn0OkConcrete, wn0Common] at hp ⊢
    xperm_hyp hp) (fun h hq => ⟨next, len, hq⟩) h0

set_option maxRecDepth 8000 in
/-- Alias: OK arm of OkFail under ambient → BNE → After ∃. -/
theorem extractWalkNext0OkFail_ok_bne
    (txBase lenW typeW innerW endPtr : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      (wn0Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff)
      (fun h => ∃ next len : Word,
        wn0OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff h) :=
  extractWalkNext0OkNested_bne txBase lenW typeW innerW endPtr txBytes srcOff

#print axioms wn0Outcome_to_okFail
#print axioms wn0Outcome_drop_fail_of_decode
#print axioms extractWalkNext0Post_to_commonOutcome
#print axioms extractWalkNext0Call_type234
#print axioms extractWalkNext0BneOk_framed
#print axioms extractWalkNext0Ok_bne
#print axioms extractWalkNext0OkNested_bne
#print axioms extractWalkNext0OkFail_ok_bne

end EvmAsm.Codegen.TxExtractToAddressSpec
