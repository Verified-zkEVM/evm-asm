import EvmAsm.Codegen.Programs.HeaderValidatePostMergeLoopClose

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel

/-! A concrete, nonzero-index round for the K67 family.  The byte at offset
    seven is a canonical one-byte item, so this witness takes the difficulty
    station rather than relying on an abstract `True` exit predicate. -/

def WBase : Word := 0x20000
def WBytes : List (BitVec 8) := List.replicate 15 1
def WEnd : Word := WBase + BitVec.ofNat 64 WBytes.length
def WSp : Word := 0x10000
def WSpC : Word := WSp + signExtend12 (-48 : BitVec 12)
def WOm : Word := 0x30000
def WFrame : Assertion := frameSlotsSaved k67Frame WSpC (fun _ => 0)
def WOmBytes : List (BitVec 8) := List.replicate 32 0

def status0Pre : Assertion :=
  (.x1 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (0 : Word)) **
  (.x31 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
  bytesRegion WBase WBytes ** (.x2 ↦ᵣ WSpC) ** (.x8 ↦ᵣ WBase) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (WBase + BitVec.ofNat 64 7)) **
  (.x19 ↦ᵣ WEnd) ** (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
  WFrame ** bytesRegion WOm WOmBytes

theorem status0Item :
    ∃ next len, rlpItemDecode WBytes 7 (WBase + BitVec.ofNat 64 7) WEnd next len := by
  refine ⟨(WBase + BitVec.ofNat 64 7) + signExtend12 (1 : BitVec 12), (1 : Word), ?_⟩
  refine ⟨1, ?_, ?_⟩
  · simp [WBytes]
  · exact Or.inl ⟨by decide, by decide, by decide, by decide⟩

theorem status0NextOnly : ∀ h,
    k67NextOutcome WBase WEnd WBytes 7 h →
      rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7 h := by
  intro h hout
  unfold k67NextOutcome at hout
  rcases hout with hOk | h2 | h3 | h4 | h5 | h6
  · exact hOk
  · have hp := (sepConj_extract_pure_end3 (A := (.x10 ↦ᵣ (WBase + BitVec.ofNat 64 7)))
        (B := (.x11 ↦ᵣ (2 : Word))) (C := (.x12 ↦ᵣ (0 : Word))) h h2)
    exact False.elim (hp (by decide))
  · have hp := (sepConj_extract_pure_end3 (A := (.x10 ↦ᵣ (WBase + BitVec.ofNat 64 7)))
        (B := (.x11 ↦ᵣ (3 : Word))) (C := (.x12 ↦ᵣ (0 : Word))) h h3)
    exact False.elim (hp status0Item)
  · have hp := (sepConj_extract_pure_end3 (A := (.x10 ↦ᵣ (WBase + BitVec.ofNat 64 7)))
        (B := (.x11 ↦ᵣ (4 : Word))) (C := (.x12 ↦ᵣ (0 : Word))) h h4)
    exact False.elim (hp status0Item)
  · have hp := (sepConj_extract_pure_end3 (A := (.x10 ↦ᵣ (WBase + BitVec.ofNat 64 7)))
        (B := (.x11 ↦ᵣ (5 : Word))) (C := (.x12 ↦ᵣ (0 : Word))) h h5)
    exact False.elim (hp status0Item)
  · have hp := (sepConj_extract_pure_end3 (A := (.x10 ↦ᵣ (WBase + BitVec.ofNat 64 7)))
        (B := (.x11 ↦ᵣ (6 : Word))) (C := (.x12 ↦ᵣ (0 : Word))) h h6)
    exact False.elim (hp status0Item)

theorem status0Exact : ∀ h,
    rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7 h →
      ((.x10 ↦ᵣ (WBase + BitVec.ofNat 64 8)) **
       (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (1 : Word))) h := by
  intro h hout
  unfold rlpWalkNextOk at hout
  rcases hout with ⟨next, len, hout⟩
  have hdec := sepConj_extract_pure_end3
    (A := (.x10 ↦ᵣ next)) (B := (.x11 ↦ᵣ (0 : Word)))
    (C := (.x12 ↦ᵣ len)) h hout
  have hregs : ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len)) h := by
    have hout' : ((((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word))) **
        (.x12 ↦ᵣ len)) ** ⌜rlpItemDecode WBytes 7
          (WBase + BitVec.ofNat 64 7) WEnd next len⌝) h := by
      simpa [sepConj_assoc] using hout
    simpa [sepConj_assoc] using ((sepConj_pure_right h).1 hout').1
  rcases hdec with ⟨b, hb, hforms⟩
  have hb1 : b = 1 := by simpa [WBytes] using hb.symm
  subst b
  rcases hforms with hsingle | hshort | hlong | hlist | hlonglist
  · rcases hsingle with ⟨hlo, hinb, hn, hl⟩
    have hn' : next = WBase + BitVec.ofNat 64 8 := by
      simpa [WBase] using hn
    have hl' : len = (1 : Word) := by simpa using hl
    rw [hn', hl'] at hregs
    exact hregs
  · simp at hshort
  · simp at hlong
  · simp at hlist
  · simp at hlonglist

theorem status0Call :
    cpsTripleWithin (2 + (1 + 87)) (K + 56) (K + 68) fullCode
      status0Pre
      ((.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
       bytesRegion WBase WBytes ** (.x2 ↦ᵣ WSpC) ** (.x8 ↦ᵣ WBase) **
       (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (WBase + BitVec.ofNat 64 7)) **
       (.x19 ↦ᵣ WEnd) ** (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
       frameSlotsSaved k67Frame (WSp + signExtend12 (-48 : BitVec 12)) (fun _ => 0) **
       bytesRegion WOm WOmBytes **
       rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7) := by
  have hss : ¬ BitVec.ult ((WBytes[7]'(by simp [WBytes])).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((WBytes[7]'(by simp [WBytes])).zeroExtend 64) (0xb8 : Word) = true →
      BitVec.ult ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0x80 : Word))
        (WEnd - (WBase + BitVec.ofNat 64 7)) = true →
      ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0x80 : Word)) = (1 : Word) →
      7 + 1 < WBytes.length ∧ WBase.toNat + (7 + 1) < 2 ^ 64 ∧
      isValidByteAccess (WBase + BitVec.ofNat 64 (7 + 1)) = true := by
    simp [WBytes]
  have hls : ¬ BitVec.ult ((WBytes[7]'(by simp [WBytes])).zeroExtend 64) (0xb8 : Word) = true →
      BitVec.ult ((WBytes[7]'(by simp [WBytes])).zeroExtend 64) (0xc0 : Word) = true →
      ¬ BitVec.ult WEnd ((WBase + BitVec.ofNat 64 7) +
        (((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xb7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true →
      7 + 1 + ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xb7 : Word)).toNat ≤ WBytes.length ∧
      WBase.toNat + (7 + 1 + ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
      ∀ k, k < ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xb7 : Word)).toNat →
        isValidByteAccess (WBase + BitVec.ofNat 64 (7 + 1 + k)) = true := by
    simp [WBytes]
  have hll : ¬ BitVec.ult ((WBytes[7]'(by simp [WBytes])).zeroExtend 64) (0xf8 : Word) = true →
      ¬ BitVec.ult WEnd ((WBase + BitVec.ofNat 64 7) +
        (((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true →
      7 + 1 + ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xf7 : Word)).toNat ≤ WBytes.length ∧
      WBase.toNat + (7 + 1 + ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
      ∀ k, k < ((WBytes[7]'(by simp [WBytes])).zeroExtend 64 - (0xf7 : Word)).toNat →
        isValidByteAccess (WBase + BitVec.ofNat 64 (7 + 1 + k)) = true := by
    simp [WBytes]
  have hover : WBase.toNat + WBytes.length < 2 ^ 64 := by decide
  have hvalid : ∀ k, k < WBytes.length →
      isValidByteAccess (WBase + BitVec.ofNat 64 k) = true := by
    intro k hk
    have hk' : k ≤ 14 := by simp [WBytes] at hk; omega
    interval_cases k <;> decide
  have h := k67LoopCall WSp WBase WOm (0 : Word) (0 : Word) (0 : Word) WEnd (7 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      (fun _ => 0) WBytes 7
      (by decide) (by simp [WBytes]) hss hls hll hover hvalid
  refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [status0Pre, WFrame, WSpC, WOmBytes] at hp ⊢
      xperm_hyp hp) (fun h hp => ?_) h
  let rest : Assertion :=
    (.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
    bytesRegion WBase WBytes **
    (.x2 ↦ᵣ (WSp + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ WBase) **
    (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (WBase + BitVec.ofNat 64 7)) **
    (.x19 ↦ᵣ WEnd) ** (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
    frameSlotsSaved k67Frame (WSp + signExtend12 (-48 : BitVec 12)) (fun _ => 0) **
    bytesRegion WOm WOmBytes
  have hp' : (rest ** k67NextOutcome WBase WEnd WBytes 7) h := by
    unfold rest
    simp only [WOmBytes] at hp ⊢
    xperm_hyp hp
  have hq' := sepConj_mono_right status0NextOnly h hp'
  unfold rest at hq'
  simp only [K, WSpC, WOmBytes] at hq' ⊢
  xperm_hyp hq'

def diffBase : Assertion :=
  (.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ (WBase + BitVec.ofNat 64 8)) **
  (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (1 : Word)) ** (.x8 ↦ᵣ WBase) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (WBase + BitVec.ofNat 64 7)) **
  (.x19 ↦ᵣ WEnd) ** (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ (WSp + signExtend12 (-48 : BitVec 12))) **
  frameSlotsSaved k67Frame (WSp + signExtend12 (-48 : BitVec 12)) (fun _ => 0) **
  bytesRegion WBase WBytes ** bytesRegion WOm WOmBytes

def diffOwn : Assertion :=
  diffBase ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14

/-! These are the exact station posts reified as the round's three Q values.
    They retain frame, input regions, and live walker state; they are not
    `True` placeholders. -/

def qDiffState (spC base omConst cursor endPtr lenW next v21 v6 v7 v28 v29 v30 v31
    o8 o9 : Word) (svals : Reg → Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
  (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (7 : Word)) **
  (.x21 ↦ᵣ v21) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
  frameSlotsSaved k67Frame spC svals ** bytesRegion base bytes **
  bytesRegion omConst WOmBytes

def qFailState (spC base omConst cursor endPtr statusW iW v8 v9 v21 v5 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ statusW) **
  (.x12 ↦ᵣ (0 : Word)) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
  (.x18 ↦ᵣ cursor) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ iW) ** (.x21 ↦ᵣ v21) **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
  (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x13 ** regOwn .x14 ** frameSlotsSaved k67Frame spC svals **
  bytesRegion base bytes ** bytesRegion omConst WOmBytes

def qCleanState (spC base omConst next endPtr lenW v21 v6 v7 v28 v29 v30 v31 : Word)
    (svals : Reg → Word) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (15 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
  (.x12 ↦ᵣ lenW) ** (.x8 ↦ᵣ next) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ next) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
  (.x21 ↦ᵣ v21) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
  (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
  frameSlotsSaved k67Frame spC svals ** bytesRegion base bytes **
  bytesRegion omConst WOmBytes

def qDiff : Assertion := fun h => ∃ spC base omConst cursor endPtr lenW next v21 v6 v7 v28 v29 v30 v31 o8 o9 svals bytes,
  qDiffState spC base omConst cursor endPtr lenW next v21 v6 v7 v28 v29 v30 v31 o8 o9 svals bytes h

def qFail : Assertion := fun h => ∃ spC base omConst cursor endPtr statusW iW v8 v9 v21 v5 v6 v7 v28 v29 v30 v31 svals bytes,
  qFailState spC base omConst cursor endPtr statusW iW v8 v9 v21 v5 v6 v7 v28 v29 v30 v31 svals bytes h

def qClean : Assertion := fun h => ∃ spC base omConst next endPtr lenW v21 v6 v7 v28 v29 v30 v31 svals bytes,
  qCleanState spC base omConst next endPtr lenW v21 v6 v7 v28 v29 v30 v31 svals bytes h

theorem diffRealSpec :
    cpsNBranchWithin 5 (K + 72) fullCode diffOwn [(K + 604, qDiff)] := by
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn9
    (r1 := .x5) (r2 := .x6) (r3 := .x7) (r4 := .x28) (r5 := .x29)
    (r6 := .x30) (r7 := .x31) (r8 := .x13) (r9 := .x14) ?_
  intro v5 v6 v7 v28 v29 v30 v31 v13 v14
  have hd0 := cpsTripleWithin_as_cpsNBranchWithin
    (k67LoopDiff WSp WBase WOm (WBase + BitVec.ofNat 64 7) WEnd (1 : Word)
      (7 : Word) (WBase + BitVec.ofNat 64 8) 0 v6 v7 v28 v29 v30 v31
      WBase 0 v5 WBytes (fun _ => 0) rfl (by decide))
  have hd1 := cpsNBranchWithin_weaken_pre
    (P' := (diffBase ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)))
    (fun h hp => by
      let pfx : Assertion := diffBase ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
      have hp0 : ((pfx ** (.x13 ↦ᵣ v13)) ** (.x14 ↦ᵣ v14)) h := by
        dsimp [pfx]
        dsimp [diffBase] at hp ⊢
        xperm_hyp hp
      have hp1 := sepConj_mono_right
        (P := pfx ** (.x13 ↦ᵣ v13)) (regIs_implies_regOwn .x14) h hp0
      have hp2 := sepConj_mono_left
        (sepConj_mono_right (P := pfx) (regIs_implies_regOwn .x13)) h hp1
      dsimp [pfx] at hp2
      dsimp [diffBase] at hp2 ⊢
      simp [WOmBytes, List.replicate] at hp2 ⊢
      xperm_hyp hp2) hd0
  refine cpsNBranchWithin_weaken_posts (exits' := [(K + 604, qDiff)]) hd1 ?_
  intro ex hmem
  simp at hmem
  rcases hmem with rfl
  refine ⟨(K + 604, qDiff), by simp, rfl, ?_⟩
  intro h hp
  unfold qDiff qDiffState
  refine ⟨WSpC, WBase, WOm, WBase + BitVec.ofNat 64 7, WEnd, (1 : Word),
    WBase + BitVec.ofNat 64 8, (0 : Word), v6, v7, v28, v29, v30, v31,
    WBase, (0 : Word), (fun _ => 0), WBytes, ?_⟩
  simp [WSpC, WOmBytes, List.replicate] at hp ⊢
  xperm_hyp hp

def status0Rest : Assertion :=
  (.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 ** bytesRegion WBase WBytes **
  (.x2 ↦ᵣ (WSp + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ WBase) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x18 ↦ᵣ (WBase + BitVec.ofNat 64 7)) ** (.x19 ↦ᵣ WEnd) **
  (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
  frameSlotsSaved k67Frame (WSp + signExtend12 (-48 : BitVec 12)) (fun _ => 0) **
  bytesRegion WOm WOmBytes

def status0RestNoX0 : Assertion :=
  (.x1 ↦ᵣ (K + 68)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 **
  bytesRegion WBase WBytes **
  (.x2 ↦ᵣ (WSp + signExtend12 (-48 : BitVec 12))) ** (.x8 ↦ᵣ WBase) **
  (.x9 ↦ᵣ (0 : Word)) ** (.x18 ↦ᵣ (WBase + BitVec.ofNat 64 7)) **
  (.x19 ↦ᵣ WEnd) ** (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
  frameSlotsSaved k67Frame (WSp + signExtend12 (-48 : BitVec 12)) (fun _ => 0) **
  bytesRegion WOm WOmBytes

def status0Inv : Nat → Assertion := fun _ => status0Pre

theorem status0PostToDiff : ∀ h,
    (status0Rest ** rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7) h → diffOwn h := by
  intro h hp
  have hp' := sepConj_mono_right status0Exact h hp
  unfold status0Rest at hp'
  unfold diffOwn diffBase
  simp [WOmBytes, List.replicate] at hp' ⊢
  xperm_hyp hp'

def status0PointPre (next len : Word) : Assertion :=
  ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    (status0RestNoX0 ** (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      ⌜rlpItemDecode WBytes 7 (WBase + BitVec.ofNat 64 7) WEnd next len⌝)

set_option maxRecDepth 8000 in
theorem status0DispatchFrame (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (K + 68) (K + 72) k67Code
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F)
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F) := by
  have hbne := bne_spec_gen_within .x11 .x0 (560 : BitVec 13) (0 : Word) (0 : Word) (K + 68)
  rw [show (K + 68 : Word) + 4 = K + 72 from by bv_omega,
    show (K + 68 : Word) + signExtend13 (560 : BitVec 13) = K + 628 from by
      rw [show signExtend13 (560 : BitVec 13) = (560 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at K (K + 68) k67Prog 17 (.BNE .x11 .x0 (560 : BitVec 13))
      (by unfold K; bv_omega) (by rw [k67_length]; decide) rfl (by rw [k67_length]; decide)) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  exact cpsTripleWithin_frameR F hF hnt

theorem status0Dispatch :
    cpsNBranchWithin 1 (K + 68) fullCode
      (status0Rest ** rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7)
      [(K + 72, status0Rest ** rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7)] := by
  let target : Assertion := status0Rest ** rlpWalkNextOk
    (WBase + BitVec.ofNat 64 7) WEnd WBytes 7
  have hrlp : ∀ next len h,
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        ⌜rlpItemDecode WBytes 7 (WBase + BitVec.ofNat 64 7) WEnd next len⌝) h →
      rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7 h := by
    intro next len h hinner
    unfold rlpWalkNextOk
    exact ⟨next, len, hinner⟩
  have hpointN : ∀ next len, cpsNBranchWithin 1 (K + 68) fullCode
      (status0PointPre next len) [(K + 72, target)] := by
    intro next len
    let F : Assertion := status0RestNoX0 ** (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      ⌜rlpItemDecode WBytes 7 (WBase + BitVec.ofNat 64 7) WEnd next len⌝
    have hF : F.pcFree := by
      dsimp [F]
      repeat' first
        | exact pcFree_regIs | exact pcFree_regOwn | exact bytesRegion_pcFree _ _
        | exact pcFree_frameSlotsSaved _ _ _ | exact pcFree_pure | apply pcFree_sepConj
    have hpt := cpsTripleWithin_extend_code k67_mono (status0DispatchFrame F hF)
    have hpt' : cpsTripleWithin 1 (K + 68) (K + 72) fullCode
        (status0PointPre next len) target := by
      refine cpsTripleWithin_weaken (fun _ hp => by dsimp [status0PointPre, F] at hp ⊢; xperm_hyp hp)
        (fun h hp => ?_) hpt
      have hp0 : (status0Rest ** (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
          (.x12 ↦ᵣ len) ** ⌜rlpItemDecode WBytes 7 (WBase + BitVec.ofNat 64 7) WEnd next len⌝) h := by
        dsimp [F] at hp
        unfold status0Rest at ⊢
        unfold status0RestNoX0 at hp
        simp [WOmBytes, List.replicate, sepConj_assoc] at hp ⊢
        xperm_hyp hp
      exact sepConj_mono_right (hrlp next len) h hp0
    exact cpsNBranchWithin_of_triple (by simp [target]) hpt'
  have hlen : ∀ next, cpsNBranchWithin 1 (K + 68) fullCode
      (fun h => ∃ len, status0PointPre next len h) [(K + 72, target)] := by
    intro next
    exact cpsNBranchWithin_exists_pre (hpointN next)
  have hex : cpsNBranchWithin 1 (K + 68) fullCode
      (fun h => ∃ next len, status0PointPre next len h) [(K + 72, target)] :=
    cpsNBranchWithin_exists_pre hlen
  have hpre : ∀ h, (status0Rest ** rlpWalkNextOk
      (WBase + BitVec.ofNat 64 7) WEnd WBytes 7) h →
      (fun h => ∃ next len, status0PointPre next len h) h := by
    intro h hp
    unfold rlpWalkNextOk at hp
    obtain ⟨next, hnext⟩ := sepConj_exists_right h hp
    obtain ⟨len, hpoint⟩ := sepConj_exists_right h hnext
    have hpoint' : status0PointPre next len h := by
      unfold status0PointPre at ⊢
      unfold status0Rest at hpoint
      unfold status0RestNoX0 at ⊢
      simp [WOmBytes, List.replicate, sepConj_assoc] at hpoint ⊢
      xperm_hyp hpoint
    exact ⟨next, len, hpoint'⟩
  have hfinal := cpsNBranchWithin_weaken_pre hpre hex
  simpa [target] using hfinal

theorem status0RoundFuel (fuel : Nat) :
    cpsNBranchWithin 103 (K + 56) fullCode status0Pre
      [(K + 604, qDiff), (K + 628, qFail), (K + 116, qClean),
       (K + 56, fun h => ∃ child : Nat, child < fuel ∧ status0Inv child h)] := by
  have hcont : cpsNBranchWithin 5 (K + 72) fullCode diffOwn [(K + 604, qDiff)] := diffRealSpec
  have hcont' : cpsNBranchWithin 5 (K + 72) fullCode
      (status0Rest ** rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7) [(K + 604, qDiff)] := by
    exact cpsNBranchWithin_weaken_pre status0PostToDiff hcont
  have hcall : cpsTripleWithin 90 (K + 56) (K + 68) fullCode status0Pre
      (status0Rest ** rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) status0Call
    dsimp [status0Rest]
    simp [K, WSpC, WOmBytes, List.replicate] at hp ⊢
    xperm_hyp hp
  have hmid : cpsTripleWithin 6 (K + 68) (K + 604) fullCode
      (status0Rest ** rlpWalkNextOk (WBase + BitVec.ofNat 64 7) WEnd WBytes 7) qDiff := by
    have hcontTriple := cpsNBranchWithin_as_cpsTripleWithin hcont'
    refine cpsNBranchWithin_merge (nSteps1 := 1) (nSteps2 := 5)
      (exit_ := K + 604) status0Dispatch ?_
    intro ex hmem'
    simp at hmem'
    rcases hmem' with rfl
    exact hcontTriple
  have hseq0 := cpsTripleWithin_seq_same_cr hcall hmid
  have hseq := cpsTripleWithin_mono_nSteps (by decide : 96 ≤ 103) hseq0
  have hmem : (K + 604, qDiff) ∈
      [(K + 604, qDiff), (K + 628, qFail), (K + 116, qClean),
       (K + 56, fun h => ∃ child : Nat, child < fuel ∧ status0Inv child h)] := by simp
  have hseqN := cpsTripleWithin_as_cpsNBranchWithin hseq
  refine cpsNBranchWithin_weaken_exits
    [(K + 604, qDiff), (K + 628, qFail), (K + 116, qClean),
     (K + 56, fun h => ∃ child : Nat, child < fuel ∧ status0Inv child h)] ?_ hseqN
  intro ex hmem'
  simp at hmem'
  rcases hmem' with rfl
  exact hmem

theorem status0RoundReal :
    cpsNBranchWithin 103 (K + 56) fullCode status0Pre
      [(K + 604, qDiff), (K + 628, qFail), (K + 116, qClean),
       (K + 56, fun h => ∃ child : Nat, child < 16 ∧ status0Inv child h)] := by
  simpa using status0RoundFuel 16

def status0RoundContractFuel (fuel : Nat) :
    K67RoundContract fuel status0Inv qDiff qFail qClean :=
  { steps := 103, proof := status0RoundFuel fuel }

def status0RoundContract16Real :
    K67RoundContract 16 status0Inv qDiff qFail qClean :=
  { steps := 103, proof := status0RoundReal }

/-! Concrete composition of the three station exits over the reified adapter.
    This is intentionally scoped to the status-0/difficulty witness invariant;
    the general `k67LoopInv` family still needs its caller-state adapter. -/
theorem status0Arms8To10Concrete (j : Nat) :
    cpsNBranchWithin (103 * (j + 1)) (K + 56) fullCode (status0Inv j)
      [(K + 604, qDiff), (K + 628, qFail), (K + 116, qClean)] := by
  apply k67MeasureThreeExitLoop_of_round 103
    (fun fuel => status0RoundContractFuel fuel) (fun _ => by rfl) j

end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
