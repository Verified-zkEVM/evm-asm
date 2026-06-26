/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases

  Framed scratch case splits for fixed x19 case-post assertions.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCases

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTwoMulFixedIterPointerPost_eq_pointerFrame
    {ptr nextLimb : Word} :
    expTwoMulFixedIterPointerPost ptr nextLimb =
      expTwoMulFixedIterPointerFrame ptr nextLimb := by
  rw [expTwoMulFixedIterPointerFrame_unfold]

@[irreducible]
def expTwoMulFixedIterReloadPointerFrame
    (ptr nextLimb : Word) : Assertion :=
  (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
  ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)

theorem expTwoMulFixedIterReloadPointerFrame_unfold {ptr nextLimb : Word} :
    expTwoMulFixedIterReloadPointerFrame ptr nextLimb =
      ((.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) := by
  delta expTwoMulFixedIterReloadPointerFrame
  rfl

theorem expTwoMulFixedIterReloadPointerFrame_pcFree {ptr nextLimb : Word} :
    (expTwoMulFixedIterReloadPointerFrame ptr nextLimb).pcFree := by
  rw [expTwoMulFixedIterReloadPointerFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterReloadPointerFrame
    (ptr nextLimb : Word) :
    Assertion.PCFree (expTwoMulFixedIterReloadPointerFrame ptr nextLimb) :=
  ⟨expTwoMulFixedIterReloadPointerFrame_pcFree⟩

abbrev expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
    (e c6 ptr nextLimb base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  expTwoMulFixedIterSkipCondRestScratchSuffix base **
  (.x19 ↦ᵣ nextLimb) **
  (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New = 0⌝ **
  expTwoMulFixedIterReloadPointerFrame ptr nextLimb **
  ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝

theorem expTwoMulFixedIterReloadCondCountPostScratchSuffix_frame
    {e c6 ptr nextLimb base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadCondCountPostScratchSuffix
        e c6 ptr nextLimb base ps) :
    expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
      e c6 ptr nextLimb base ps := by
  unfold expTwoMulFixedIterReloadCondCountPostScratchSuffix
    expTwoMulFixedIterReloadCondFrame at h
  unfold expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
  rw [expTwoMulFixedIterReloadPointerFrame_unfold]
  sep_perm h

abbrev expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
    (e c6 ptr nextLimb evmSp a0 a1 a2 a3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
  (.x19 ↦ᵣ nextLimb) **
  (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New = 0⌝ **
  expTwoMulFixedIterReloadPointerFrame ptr nextLimb **
  ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
  expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3

theorem expTwoMulFixedIterReloadSkipCountPostScratchSuffix_frame
    {e c6 ptr nextLimb evmSp a0 a1 a2 a3 base : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadSkipCountPostScratchSuffix
        e c6 ptr nextLimb evmSp a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
      e c6 ptr nextLimb evmSp a0 a1 a2 a3 base ps := by
  unfold expTwoMulFixedIterReloadSkipCountPostScratchSuffix
    expTwoMulFixedIterReloadSkipRestScratchSuffix at h
  unfold expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
  rw [expTwoMulFixedIterReloadPointerFrame_unfold]
  sep_perm h

theorem expTwoMulFixedIterCaseLoopPost_scratch_cases_pointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseLoopPost_scratch_cases_frame h with
    hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨v6, v7, v10, v11, d0, d1, d2, d3,
        by
          simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨v6, v7, v10, v11, d0, d1, d2, d3,
          by
            simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))

theorem expTwoMulFixedIterCaseLoopPost_scratch_cases_reloadPointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseLoopPost_scratch_cases_pointerFrame h with
    hSkipCond | hRest
  · exact Or.inl hSkipCond
  · rcases hRest with hSkip | hRest
    · exact Or.inr (Or.inl hSkip)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        obtain ⟨psMain, psFrame, hDisjoint, hUnion, hMain, hFrame⟩ :=
          hScratch
        obtain ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix,
          hPrefix, hTail⟩ := hMain
        obtain ⟨psScratch, psSuffix, hDisjointScratch, hUnionScratch,
          hScratchIs, hSuffix⟩ := hTail
        have hSuffixFrame :=
          expTwoMulFixedIterReloadCondCountPostScratchSuffix_frame hSuffix
        have hMainFrame :
            (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
              r0 r1 r2 r3 a0 a1 a2 a3
              (expTwoMulIterCountNew iterCount ≠ 0) **
              expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
              expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
                e c6 ptr nextLimb base) psMain :=
          ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix, hPrefix,
            psScratch, psSuffix, hDisjointScratch, hUnionScratch,
            hScratchIs, hSuffixFrame⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psMain, psFrame, hDisjoint, hUnion, hMainFrame, hFrame⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        obtain ⟨psMain, psFrame, hDisjoint, hUnion, hMain, hFrame⟩ :=
          hScratch
        obtain ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix,
          hPrefix, hTail⟩ := hMain
        obtain ⟨psScratch, psSuffix, hDisjointScratch, hUnionScratch,
          hScratchIs, hSuffix⟩ := hTail
        have hSuffixFrame :=
          expTwoMulFixedIterReloadSkipCountPostScratchSuffix_frame hSuffix
        have hMainFrame :
            (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
              r0 r1 r2 r3 (expTwoMulIterCountNew iterCount ≠ 0) **
              expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
              expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
                e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) psMain :=
          ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix, hPrefix,
            psScratch, psSuffix, hDisjointScratch, hUnionScratch,
            hScratchIs, hSuffixFrame⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psMain, psFrame, hDisjoint, hUnion, hMainFrame, hFrame⟩))

theorem expTwoMulFixedIterCaseExitPost_scratch_cases_frame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  obtain ⟨psCase, psFrame, hDisjoint, hUnion, hCase, hFrame⟩ := h
  rcases expTwoMulFixedIterCaseExitPost_scratch_cases hCase with hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨v6, v7, v10, v11, d0, d1, d2, d3,
        psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨v6, v7, v10, v11, d0, d1, d2, d3,
          psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩))

theorem expTwoMulFixedIterCaseExitPost_scratch_cases_pointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseExitPost_scratch_cases_frame h with
    hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨v6, v7, v10, v11, d0, d1, d2, d3,
        by
          simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨v6, v7, v10, v11, d0, d1, d2, d3,
          by
            simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))

theorem expTwoMulFixedIterCaseExitPost_scratch_cases_reloadPointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseExitPost_scratch_cases_pointerFrame h with
    hSkipCond | hRest
  · exact Or.inl hSkipCond
  · rcases hRest with hSkip | hRest
    · exact Or.inr (Or.inl hSkip)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        obtain ⟨psMain, psFrame, hDisjoint, hUnion, hMain, hFrame⟩ :=
          hScratch
        obtain ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix,
          hPrefix, hTail⟩ := hMain
        obtain ⟨psScratch, psSuffix, hDisjointScratch, hUnionScratch,
          hScratchIs, hSuffix⟩ := hTail
        have hSuffixFrame :=
          expTwoMulFixedIterReloadCondCountPostScratchSuffix_frame hSuffix
        have hMainFrame :
            (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
              r0 r1 r2 r3 a0 a1 a2 a3
              (expTwoMulIterCountNew iterCount = 0) **
              expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
              expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
                e c6 ptr nextLimb base) psMain :=
          ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix, hPrefix,
            psScratch, psSuffix, hDisjointScratch, hUnionScratch,
            hScratchIs, hSuffixFrame⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psMain, psFrame, hDisjoint, hUnion, hMainFrame, hFrame⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        obtain ⟨psMain, psFrame, hDisjoint, hUnion, hMain, hFrame⟩ :=
          hScratch
        obtain ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix,
          hPrefix, hTail⟩ := hMain
        obtain ⟨psScratch, psSuffix, hDisjointScratch, hUnionScratch,
          hScratchIs, hSuffix⟩ := hTail
        have hSuffixFrame :=
          expTwoMulFixedIterReloadSkipCountPostScratchSuffix_frame hSuffix
        have hMainFrame :
            (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
              r0 r1 r2 r3 (expTwoMulIterCountNew iterCount = 0) **
              expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
              expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
                e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) psMain :=
          ⟨psPrefix, psTail, hDisjointPrefix, hUnionPrefix, hPrefix,
            psScratch, psSuffix, hDisjointScratch, hUnionScratch,
            hScratchIs, hSuffixFrame⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psMain, psFrame, hDisjoint, hUnion, hMainFrame, hFrame⟩))

theorem expTwoMulFixedIterSkipCondScratchFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterSkipCondCountPostScratchSuffix
    expTwoMulFixedIterSkipCondFrame at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffixPtr, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffixPtr⟩ := hTail
  obtain ⟨_psSuffix, _psPtr, _hDisjointSuffix, _hUnionSuffix,
    hSuffix, _hPtr⟩ := hSuffixPtr
  obtain ⟨_psRet, _psSkipCondFrame, _hDisjointRet, _hUnionRet,
    _hRet, hSkipCondFrame⟩ := hSuffix
  obtain ⟨_, _, _, _, _, hX20Tail⟩ := hSkipCondFrame
  obtain ⟨_, _, _, _, _, hFrameTail⟩ := hX20Tail
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hFrameTail
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, h_bit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨h_exit, h_c6, h_bit⟩

theorem expTwoMulFixedIterSkipScratchFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterSkipCountPostScratchSuffix
    expTwoMulFixedIterSkipRestScratchSuffix at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffixPtr, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffixPtr⟩ := hTail
  obtain ⟨_psSuffix, _psPtr, _hDisjointSuffix, _hUnionSuffix,
    hSuffix, _hPtr⟩ := hSuffixPtr
  obtain ⟨_psSkipRest, _psBaseFrame, _hDisjointSkipRest, _hUnionSkipRest,
    hSkipRest, _hBaseFrame⟩ := hSuffix
  obtain ⟨_, _, _, _, _, hSkipRestTail⟩ := hSkipRest
  obtain ⟨_, _, _, _, _, hX20Tail⟩ := hSkipRestTail
  obtain ⟨_, _, _, _, _, hX18Tail⟩ := hX20Tail
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hX18Tail
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, h_bit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨h_exit, h_c6, h_bit⟩

theorem expTwoMulFixedIterReloadCondScratchFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterReloadCondCountPostScratchSuffix
    expTwoMulFixedIterReloadCondFrame at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffix, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffix⟩ := hTail
  obtain ⟨_psRet, _psReloadCondFrame, _hDisjointRet, _hUnionRet,
    _hRet, hReloadCondFrame⟩ := hSuffix
  obtain ⟨_, _, _, _, _, hX20Tail⟩ := hReloadCondFrame
  obtain ⟨_, _, _, _, _, hReloadCondTail⟩ := hX20Tail
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hReloadCondTail
  have hC6Tail := ((sepConj_pure_left _).1 hPureTail)
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) = 0 := hC6Tail.1
  obtain ⟨_, _, _, _, _, hMemBit⟩ := hC6Tail.2
  obtain ⟨_, _, _, _, _, hBitPure⟩ := hMemBit
  have h_bit :
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 :=
    hBitPure.2
  exact ⟨h_exit, h_c6, h_bit⟩

theorem expTwoMulFixedIterReloadSkipScratchFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterReloadSkipCountPostScratchSuffix
    expTwoMulFixedIterReloadSkipRestScratchSuffix at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffix, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffix⟩ := hTail
  obtain ⟨_psReloadSkip, _psBaseFrame, _hDisjointReloadSkip, _hUnionReloadSkip,
    hReloadSkip, _hBaseFrame⟩ := hSuffix
  obtain ⟨_, _, _, _, _, hReloadSkipTail1⟩ := hReloadSkip
  obtain ⟨_, _, _, _, _, hReloadSkipTail2⟩ := hReloadSkipTail1
  obtain ⟨_, _, _, _, _, hReloadSkipTail3⟩ := hReloadSkipTail2
  obtain ⟨_, _, _, _, _, hReloadSkipTail4⟩ := hReloadSkipTail3
  obtain ⟨_, _, _, _, hC6Pure, hPtrMemBit⟩ := hReloadSkipTail4
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) = 0 :=
    hC6Pure.2
  obtain ⟨_, _, _, _, _, hMemBit⟩ := hPtrMemBit
  obtain ⟨_, _, _, _, _, hBitPure⟩ := hMemBit
  have h_bit :
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 :=
    hBitPure.2
  exact ⟨h_exit, h_c6, h_bit⟩

/-- Weaken the per-iteration scratch frame's `x6` value slot to ownership.
    After the counter moved to `x20`, the next `IterPre` keeps `x6` only as
    `regOwn` scratch, so the loop-back post's concrete `x6` value is dropped. -/
theorem expTwoMulFixedIterScratchIs_x6_to_regOwn
    {evmSp v6 v7 v10 v11 d0 d1 d2 d3 : Word} :
    ∀ ps, expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 ps →
      (regOwn .x6 ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (evmSp ↦ₘ d0) ** ((evmSp + 8) ↦ₘ d1) ** ((evmSp + 16) ↦ₘ d2) **
       ((evmSp + 24) ↦ₘ d3)) ps := by
  intro ps h
  unfold expTwoMulFixedIterScratchIs at h
  exact sepConj_mono_left (regIs_implies_regOwn .x6) _ h

theorem expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    ((expTwoMulFixedIterPre
      (e <<< (1 : BitVec 6).toNat)
      (c6 + signExtend12 (-1 : BitVec 12))
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      ptr nextLimb sp evmSp
      (rw.getLimbN 3)
      (((base + 44) + 140) + 68)
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      d0 d1 d2 d3
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      a0 a1 a2 a3 v7 v11) **
      frame) ps := by
  intro squareW rw
  have h_pures := expTwoMulFixedIterSkipCondScratchFrame_pures h
  rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ h
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterSkipCondRestScratchPrefix
    expTwoMulFixedIterSkipCondCountPostScratchSuffix
    expTwoMulFixedIterSkipCondRestScratchSuffix
    expTwoMulFixedIterSkipCondFrame at h
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) ≠ 0⌝ : Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at h
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0⌝ :
        Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  rw [expTwoMulFixedIterPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  simp only [evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    BitVec.add_assoc] at h ⊢
  sep_perm h

theorem expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    ((expTwoMulFixedIterPre
      (e <<< (1 : BitVec 6).toNat)
      (c6 + signExtend12 (-1 : BitVec 12))
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      ptr nextLimb sp evmSp
      (squareW.getLimbN 3)
      (((base + 44) + 32) + 68)
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      d0 d1 d2 d3
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      a0 a1 a2 a3 v7 v11) **
      frame) ps := by
  intro squareW
  have h_pures := expTwoMulFixedIterSkipScratchFrame_pures h
  rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ h
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterSkipRestScratchPrefix
    expTwoMulFixedIterSkipCountPostScratchSuffix
    expTwoMulFixedIterSkipRestScratchSuffix
    expTwoMulFixedIterBaseFrame at h
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) ≠ 0⌝ : Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at h
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0⌝ :
        Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  rw [expTwoMulFixedIterPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  simp only [evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    BitVec.add_assoc] at h ⊢
  sep_perm h

end EvmAsm.Evm64.Exp.Compose
