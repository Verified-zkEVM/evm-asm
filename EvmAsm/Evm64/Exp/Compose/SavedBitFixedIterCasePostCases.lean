/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCases

  Case-splitting lemmas for fixed x19 named case-post assertions.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

abbrev expTwoMulFixedIterScratchOwn (evmSp : Word) : Assertion :=
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24)

abbrev expTwoMulFixedIterScratchIs
    (evmSp v6 v7 v10 v11 d0 d1 d2 d3 : Word) : Assertion :=
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
  (evmSp ↦ₘ d0) ** (evmSp + 8 ↦ₘ d1) **
  (evmSp + 16 ↦ₘ d2) ** (evmSp + 24 ↦ₘ d3)

theorem expTwoMulFixedIterScratchOwn_pcFree {evmSp : Word} :
    (expTwoMulFixedIterScratchOwn evmSp).pcFree := by
  unfold expTwoMulFixedIterScratchOwn
  pcFree

theorem expTwoMulFixedIterScratchIs_pcFree
    {evmSp v6 v7 v10 v11 d0 d1 d2 d3 : Word} :
    (expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11
      d0 d1 d2 d3).pcFree := by
  unfold expTwoMulFixedIterScratchIs
  pcFree

instance pcFreeInst_expTwoMulFixedIterScratchOwn (evmSp : Word) :
    Assertion.PCFree (expTwoMulFixedIterScratchOwn evmSp) :=
  ⟨expTwoMulFixedIterScratchOwn_pcFree⟩

instance pcFreeInst_expTwoMulFixedIterScratchIs
    (evmSp v6 v7 v10 v11 d0 d1 d2 d3 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11
        d0 d1 d2 d3) :=
  ⟨expTwoMulFixedIterScratchIs_pcFree⟩

theorem expTwoMulFixedIterScratchOwn_choose
    {evmSp : Word} {ps : PartialState}
    (h : expTwoMulFixedIterScratchOwn evmSp ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 ps := by
  unfold expTwoMulFixedIterScratchOwn at h
  obtain ⟨v6, h_v6_chain⟩ := sepConj_choose_regOwn h
  obtain ⟨ps_v6, ps_rest1, h_disjoint_v6, h_union_v6, h_v6, h_rest1⟩ :=
    h_v6_chain
  obtain ⟨v7, h_v7_chain⟩ := sepConj_choose_regOwn h_rest1
  obtain ⟨ps_v7, ps_rest2, h_disjoint_v7, h_union_v7, h_v7, h_rest2⟩ :=
    h_v7_chain
  obtain ⟨v10, h_v10_chain⟩ := sepConj_choose_regOwn h_rest2
  obtain ⟨ps_v10, ps_rest3, h_disjoint_v10, h_union_v10, h_v10, h_rest3⟩ :=
    h_v10_chain
  obtain ⟨v11, h_v11_chain⟩ := sepConj_choose_regOwn h_rest3
  obtain ⟨ps_v11, ps_rest4, h_disjoint_v11, h_union_v11, h_v11, h_rest4⟩ :=
    h_v11_chain
  obtain ⟨d0, h_d0_chain⟩ := sepConj_choose_memOwn h_rest4
  obtain ⟨ps_d0, ps_rest5, h_disjoint_d0, h_union_d0, h_d0, h_rest5⟩ :=
    h_d0_chain
  obtain ⟨d1, h_d1_chain⟩ := sepConj_choose_memOwn h_rest5
  obtain ⟨ps_d1, ps_rest6, h_disjoint_d1, h_union_d1, h_d1, h_rest6⟩ :=
    h_d1_chain
  obtain ⟨d2, h_d2_chain⟩ := sepConj_choose_memOwn h_rest6
  obtain ⟨ps_d2, ps_rest7, h_disjoint_d2, h_union_d2, h_d2, h_rest7⟩ :=
    h_d2_chain
  obtain ⟨d3, h_d3⟩ := h_rest7
  refine ⟨v6, v7, v10, v11, d0, d1, d2, d3, ?_⟩
  unfold expTwoMulFixedIterScratchIs
  refine ⟨ps_v6, ps_rest1, h_disjoint_v6, h_union_v6, h_v6, ?_⟩
  refine ⟨ps_v7, ps_rest2, h_disjoint_v7, h_union_v7, h_v7, ?_⟩
  refine ⟨ps_v10, ps_rest3, h_disjoint_v10, h_union_v10, h_v10, ?_⟩
  refine ⟨ps_v11, ps_rest4, h_disjoint_v11, h_union_v11, h_v11, ?_⟩
  refine ⟨ps_d0, ps_rest5, h_disjoint_d0, h_union_d0, h_d0, ?_⟩
  refine ⟨ps_d1, ps_rest6, h_disjoint_d1, h_union_d1, h_d1, ?_⟩
  refine ⟨ps_d2, ps_rest7, h_disjoint_d2, h_union_d2, h_d2, ?_⟩
  exact h_d3

theorem expTwoMulFixedIterScratchOwn_choose_frame
    {evmSp : Word} {B : Assertion} {ps : PartialState}
    (h : (expTwoMulFixedIterScratchOwn evmSp ** B) ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 ** B) ps := by
  obtain ⟨psScratch, psRest, h_disjoint, h_union, hScratch, hRest⟩ := h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratchIs⟩ :=
    expTwoMulFixedIterScratchOwn_choose hScratch
  exact ⟨v6, v7, v10, v11, d0, d1, d2, d3,
    psScratch, psRest, h_disjoint, h_union, hScratchIs, hRest⟩

theorem expTwoMulFixedIterScratchOwn_choose_two_frame
    {evmSp : Word} {A B : Assertion} {ps : PartialState}
    (h : (A ** expTwoMulFixedIterScratchOwn evmSp ** B) ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (A ** expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 ** B) ps := by
  have hFront :
      (expTwoMulFixedIterScratchOwn evmSp ** (A ** B)) ps := by
    sep_perm h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hChosen⟩ :=
    expTwoMulFixedIterScratchOwn_choose_frame hFront
  refine ⟨v6, v7, v10, v11, d0, d1, d2, d3, ?_⟩
  sep_perm hChosen

abbrev expTwoMulFixedIterSkipCondRestScratchPrefix
    (sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 : Word) : Assertion :=
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ rw.getLimbN 3) **
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
  evmWordIs sp rw ** evmWordIs (evmSp + 32) rw

abbrev expTwoMulFixedIterSkipCondRestScratchSuffix (base : Word) : Assertion :=
  (.x1 ↦ᵣ (((base + 44) + 140) + 68))

theorem expTwoMulFixedIterSkipCondRest_scratch_decomp
    {sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3
        a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondRestScratchPrefix sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 **
      expTwoMulFixedIterScratchOwn evmSp **
      expTwoMulFixedIterSkipCondRestScratchSuffix base) ps := by
  unfold expTwoMulFixedIterSkipCondRest
    expTwoMulFixedIterSkipCondRestScratchPrefix
    expTwoMulFixedIterScratchOwn
    expTwoMulFixedIterSkipCondRestScratchSuffix at *
  sep_perm h

abbrev expTwoMulFixedIterSkipRestScratchPrefix
    (sp evmSp r0 r1 r2 r3 : Word) : Assertion :=
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ squareW.getLimbN 3) **
  evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW

abbrev expTwoMulFixedIterSkipRestScratchSuffix
    (e c6 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
  (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
  (.x20 ↦ᵣ c6New) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝

theorem expTwoMulFixedIterSkipRest_scratch_decomp
    {e c6 sp evmSp r0 r1 r2 r3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipRest e c6 sp evmSp
        r0 r1 r2 r3 base ps) :
    (expTwoMulFixedIterSkipRestScratchPrefix sp evmSp r0 r1 r2 r3 **
      expTwoMulFixedIterScratchOwn evmSp **
      expTwoMulFixedIterSkipRestScratchSuffix e c6 base) ps := by
  unfold expTwoMulFixedIterSkipRest
    expTwoMulFixedIterSkipRestScratchPrefix
    expTwoMulFixedIterScratchOwn
    expTwoMulFixedIterSkipRestScratchSuffix at *
  sep_perm h

abbrev expTwoMulFixedIterReloadSkipRestScratchSuffix
    (e c6 ptr nextLimb base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
  (.x19 ↦ᵣ nextLimb) **
  (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New = 0⌝ **
  (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
  ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
  ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝

theorem expTwoMulFixedIterReloadSkipRest_scratch_decomp
    {e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 base : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadSkipRest e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 base ps) :
    (expTwoMulFixedIterSkipRestScratchPrefix sp evmSp r0 r1 r2 r3 **
      expTwoMulFixedIterScratchOwn evmSp **
      expTwoMulFixedIterReloadSkipRestScratchSuffix e c6 ptr nextLimb base) ps := by
  unfold expTwoMulFixedIterReloadSkipRest
    expTwoMulFixedIterSkipRestScratchPrefix
    expTwoMulFixedIterScratchOwn
    expTwoMulFixedIterReloadSkipRestScratchSuffix at *
  sep_perm h

theorem expTwoMulFixedIterSkipCondRest_choose_scratch
    {sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3
        a0 a1 a2 a3 base ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondRestScratchPrefix sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipCondRestScratchSuffix base) ps := by
  have hDecomp := expTwoMulFixedIterSkipCondRest_scratch_decomp h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

theorem expTwoMulFixedIterSkipRest_choose_scratch
    {e c6 sp evmSp r0 r1 r2 r3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipRest e c6 sp evmSp
        r0 r1 r2 r3 base ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipRestScratchPrefix sp evmSp r0 r1 r2 r3 **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipRestScratchSuffix e c6 base) ps := by
  have hDecomp := expTwoMulFixedIterSkipRest_scratch_decomp h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

theorem expTwoMulFixedIterReloadSkipRest_choose_scratch
    {e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 base : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadSkipRest e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 base ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipRestScratchPrefix sp evmSp r0 r1 r2 r3 **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipRestScratchSuffix e c6 ptr nextLimb base) ps := by
  have hDecomp := expTwoMulFixedIterReloadSkipRest_scratch_decomp h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

abbrev expTwoMulFixedIterSkipCondCountPostScratchPrefix
    (iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (exitCond : Prop) : Assertion :=
  ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipCondRestScratchPrefix sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3

abbrev expTwoMulFixedIterSkipCondCountPostScratchSuffix
    (e c6 base : Word) : Assertion :=
  expTwoMulFixedIterSkipCondRestScratchSuffix base **
    expTwoMulFixedIterSkipCondFrame e c6

theorem expTwoMulFixedIterSkipCondCountPost_choose_scratch
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base) ps := by
  have hDecomp :
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchOwn evmSp **
        expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base) ps := by
    unfold expTwoMulFixedIterSkipCondCountPost
      expTwoMulFixedIterSkipCondRest
      expTwoMulFixedIterSkipCondCountPostScratchPrefix
      expTwoMulFixedIterSkipCondRestScratchPrefix
      expTwoMulFixedIterScratchOwn
      expTwoMulFixedIterSkipCondCountPostScratchSuffix
      expTwoMulFixedIterSkipCondRestScratchSuffix at *
    sep_perm h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

abbrev expTwoMulFixedIterSkipCountPostScratchPrefix
    (iterCount sp evmSp r0 r1 r2 r3 : Word)
    (exitCond : Prop) : Assertion :=
  ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipRestScratchPrefix sp evmSp r0 r1 r2 r3

abbrev expTwoMulFixedIterSkipCountPostScratchSuffix
    (e c6 evmSp a0 a1 a2 a3 base : Word) : Assertion :=
  expTwoMulFixedIterSkipRestScratchSuffix e c6 base **
    expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3

theorem expTwoMulFixedIterSkipCountPost_choose_scratch
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base) ps := by
  have hDecomp :
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchOwn evmSp **
        expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base) ps := by
    unfold expTwoMulFixedIterSkipCountPost
      expTwoMulFixedIterSkipRest
      expTwoMulFixedIterSkipCountPostScratchPrefix
      expTwoMulFixedIterSkipRestScratchPrefix
      expTwoMulFixedIterScratchOwn
      expTwoMulFixedIterSkipCountPostScratchSuffix
      expTwoMulFixedIterSkipRestScratchSuffix at *
    sep_perm h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

abbrev expTwoMulFixedIterReloadCondCountPostScratchSuffix
    (e c6 ptr nextLimb base : Word) : Assertion :=
  expTwoMulFixedIterSkipCondRestScratchSuffix base **
    expTwoMulFixedIterReloadCondFrame e c6 ptr nextLimb

theorem expTwoMulFixedIterReloadCondCountPost_choose_scratch
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) ps := by
  have hDecomp :
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchOwn evmSp **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) ps := by
    unfold expTwoMulFixedIterReloadCondCountPost
      expTwoMulFixedIterSkipCondRest
      expTwoMulFixedIterSkipCondCountPostScratchPrefix
      expTwoMulFixedIterSkipCondRestScratchPrefix
      expTwoMulFixedIterScratchOwn
      expTwoMulFixedIterReloadCondCountPostScratchSuffix
      expTwoMulFixedIterSkipCondRestScratchSuffix at *
    sep_perm h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

abbrev expTwoMulFixedIterReloadSkipCountPostScratchSuffix
    (e c6 ptr nextLimb evmSp a0 a1 a2 a3 base : Word) : Assertion :=
  expTwoMulFixedIterReloadSkipRestScratchSuffix e c6 ptr nextLimb base **
    expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3

theorem expTwoMulFixedIterReloadSkipCountPost_choose_scratch
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) ps := by
  have hDecomp :
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchOwn evmSp **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) ps := by
    unfold expTwoMulFixedIterReloadSkipCountPost
      expTwoMulFixedIterReloadSkipRest
      expTwoMulFixedIterSkipCountPostScratchPrefix
      expTwoMulFixedIterSkipRestScratchPrefix
      expTwoMulFixedIterScratchOwn
      expTwoMulFixedIterReloadSkipCountPostScratchSuffix
      expTwoMulFixedIterReloadSkipRestScratchSuffix at *
    sep_perm h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

theorem expTwoMulFixedIterSkipCondCountPost_choose_scratch_frame
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
        frame) ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          frame)) ps := by
  have hDecomp :
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchOwn evmSp **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          frame)) ps := by
    unfold expTwoMulFixedIterSkipCondCountPost
      expTwoMulFixedIterSkipCondRest
      expTwoMulFixedIterSkipCondCountPostScratchPrefix
      expTwoMulFixedIterSkipCondRestScratchPrefix
      expTwoMulFixedIterScratchOwn
      expTwoMulFixedIterSkipCondCountPostScratchSuffix
      expTwoMulFixedIterSkipCondRestScratchSuffix at *
    sep_perm h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

theorem expTwoMulFixedIterSkipCountPost_choose_scratch_frame
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
        frame) ps) :
    ∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          frame)) ps := by
  have hDecomp :
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchOwn evmSp **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          frame)) ps := by
    unfold expTwoMulFixedIterSkipCountPost
      expTwoMulFixedIterSkipRest
      expTwoMulFixedIterSkipCountPostScratchPrefix
      expTwoMulFixedIterSkipRestScratchPrefix
      expTwoMulFixedIterScratchOwn
      expTwoMulFixedIterSkipCountPostScratchSuffix
      expTwoMulFixedIterSkipRestScratchSuffix at *
    sep_perm h
  exact expTwoMulFixedIterScratchOwn_choose_two_frame hDecomp

theorem expTwoMulFixedIterCaseLoopPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  rfl

theorem expTwoMulFixedIterCaseExitPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  rfl

theorem expTwoMulFixedIterReloadLoopPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps := by
  rfl

theorem expTwoMulFixedIterReloadExitPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps := by
  rfl

theorem expTwoMulFixedIterCaseLoopPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps :=
  expTwoMulFixedIterCaseLoopPost_iff.mp h

theorem expTwoMulFixedIterCaseExitPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps :=
  expTwoMulFixedIterCaseExitPost_iff.mp h

theorem expTwoMulFixedIterReloadLoopPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps :=
  expTwoMulFixedIterReloadLoopPost_iff.mp h

theorem expTwoMulFixedIterReloadExitPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps :=
  expTwoMulFixedIterReloadExitPost_iff.mp h

theorem expTwoMulFixedIterSkipLoopPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps := by
  obtain ⟨psLeft, psRight, hDisjoint, hUnion, hCases, hPtr⟩ := h
  rcases hCases with hCond | hSkip
  · exact Or.inl ⟨psLeft, psRight, hDisjoint, hUnion, hCond, hPtr⟩
  · exact Or.inr ⟨psLeft, psRight, hDisjoint, hUnion, hSkip, hPtr⟩

theorem expTwoMulFixedIterSkipExitPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps := by
  obtain ⟨psLeft, psRight, hDisjoint, hUnion, hCases, hPtr⟩ := h
  rcases hCases with hCond | hSkip
  · exact Or.inl ⟨psLeft, psRight, hDisjoint, hUnion, hCond, hPtr⟩
  · exact Or.inr ⟨psLeft, psRight, hDisjoint, hUnion, hSkip, hPtr⟩

theorem expTwoMulFixedIterCaseLoopPost_count_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps := by
  rcases expTwoMulFixedIterCaseLoopPost_cases h with hSkip | hReload
  · rcases expTwoMulFixedIterSkipLoopPost_cases hSkip with hCond | hSkipCount
    · exact Or.inl hCond
    · exact Or.inr (Or.inl hSkipCount)
  · rcases expTwoMulFixedIterReloadLoopPost_cases hReload with hCond | hSkipCount
    · exact Or.inr (Or.inr (Or.inl hCond))
    · exact Or.inr (Or.inr (Or.inr hSkipCount))

theorem expTwoMulFixedIterCaseExitPost_count_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps := by
  rcases expTwoMulFixedIterCaseExitPost_cases h with hSkip | hReload
  · rcases expTwoMulFixedIterSkipExitPost_cases hSkip with hCond | hSkipCount
    · exact Or.inl hCond
    · exact Or.inr (Or.inl hSkipCount)
  · rcases expTwoMulFixedIterReloadExitPost_cases hReload with hCond | hSkipCount
    · exact Or.inr (Or.inr (Or.inl hCond))
    · exact Or.inr (Or.inr (Or.inr hSkipCount))

theorem expTwoMulFixedIterCaseLoopPost_scratch_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) ps) := by
  rcases expTwoMulFixedIterCaseLoopPost_count_cases h with hSkipCond | hRest
  · exact Or.inl
      (expTwoMulFixedIterSkipCondCountPost_choose_scratch_frame hSkipCond)
  · rcases hRest with hSkip | hRest
    · exact Or.inr (Or.inl
        (expTwoMulFixedIterSkipCountPost_choose_scratch_frame hSkip))
    · rcases hRest with hReloadCond | hReloadSkip
      · exact Or.inr (Or.inr (Or.inl
          (expTwoMulFixedIterReloadCondCountPost_choose_scratch hReloadCond)))
      · exact Or.inr (Or.inr (Or.inr
          (expTwoMulFixedIterReloadSkipCountPost_choose_scratch hReloadSkip)))

theorem expTwoMulFixedIterCaseExitPost_scratch_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) ps) := by
  rcases expTwoMulFixedIterCaseExitPost_count_cases h with hSkipCond | hRest
  · exact Or.inl
      (expTwoMulFixedIterSkipCondCountPost_choose_scratch_frame hSkipCond)
  · rcases hRest with hSkip | hRest
    · exact Or.inr (Or.inl
        (expTwoMulFixedIterSkipCountPost_choose_scratch_frame hSkip))
    · rcases hRest with hReloadCond | hReloadSkip
      · exact Or.inr (Or.inr (Or.inl
          (expTwoMulFixedIterReloadCondCountPost_choose_scratch hReloadCond)))
      · exact Or.inr (Or.inr (Or.inr
          (expTwoMulFixedIterReloadSkipCountPost_choose_scratch hReloadSkip)))

theorem expTwoMulFixedIterCaseLoopPost_scratch_cases_frame
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
          expTwoMulFixedIterPointerPost ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) **
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
  obtain ⟨psCase, psFrame, hDisjoint, hUnion, hCase, hFrame⟩ := h
  rcases expTwoMulFixedIterCaseLoopPost_scratch_cases hCase with hSkipCond | hRest
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

theorem expTwoMulFixedIterSkipCondCountPost_pures
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterSkipCondCountPost
    expTwoMulFixedIterSkipCondFrame at h
  obtain ⟨_, _, _, _, hMain, hFrame⟩ := h
  obtain ⟨_, _, _, _, hCount, _⟩ := hMain
  obtain ⟨_, _, _, _, _, hCountTail⟩ := hCount
  have hExit : exitCond := ((sepConj_pure_right _).1 hCountTail).2
  obtain ⟨_, _, _, _, _, hFrameTail⟩ := hFrame
  obtain ⟨_, _, _, _, _, hFrameTailB⟩ := hFrameTail
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hFrameTailB
  have hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, hBit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨hExit, hC6, hBit⟩

theorem expTwoMulFixedIterSkipCountPost_pures
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  unfold expTwoMulFixedIterSkipCountPost
    expTwoMulFixedIterSkipRest at h
  obtain ⟨_, _, _, _, hMain, _hBaseFrame⟩ := h
  obtain ⟨_, _, _, _, hCount, hRest⟩ := hMain
  obtain ⟨_, _, _, _, _, hCountTail⟩ := hCount
  have hExit : exitCond := ((sepConj_pure_right _).1 hCountTail).2
  obtain ⟨_, _, _, _, _, hRest1⟩ := hRest
  obtain ⟨_, _, _, _, _, hRest2⟩ := hRest1
  obtain ⟨_, _, _, _, _, hRest3⟩ := hRest2
  obtain ⟨_, _, _, _, _, hRest4⟩ := hRest3
  obtain ⟨_, _, _, _, _, hRest5⟩ := hRest4
  obtain ⟨_, _, _, _, _, hRest6⟩ := hRest5
  obtain ⟨_, _, _, _, _, hRest7⟩ := hRest6
  obtain ⟨_, _, _, _, _, hRest8⟩ := hRest7
  obtain ⟨_, _, _, _, _, hRest9⟩ := hRest8
  obtain ⟨_, _, _, _, _, hRest10⟩ := hRest9
  obtain ⟨_, _, _, _, _, hRest11⟩ := hRest10
  obtain ⟨_, _, _, _, _, hRest12⟩ := hRest11
  obtain ⟨_, _, _, _, _, hRest13⟩ := hRest12
  obtain ⟨_, _, _, _, _, hRest14⟩ := hRest13
  obtain ⟨_, _, _, _, _, hRest15⟩ := hRest14
  obtain ⟨_, _, _, _, _, hRest15b⟩ := hRest15
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hRest15b
  have hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, hBit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨hExit, hC6, hBit⟩

theorem expTwoMulFixedIterReloadCondCountPost_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterReloadCondCountPost
    expTwoMulFixedIterReloadCondFrame at h
  obtain ⟨_, _, _, _, hMain, hFrame⟩ := h
  obtain ⟨_, _, _, _, hCount, _⟩ := hMain
  obtain ⟨_, _, _, _, _, hCountTail⟩ := hCount
  have hExit : exitCond := ((sepConj_pure_right _).1 hCountTail).2
  obtain ⟨_, _, _, _, _, hFrame1⟩ := hFrame
  obtain ⟨_, _, _, _, _, hFrame1b⟩ := hFrame1
  obtain ⟨_, _, _, _, _, hFrame2⟩ := hFrame1b
  have hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0 :=
    ((sepConj_pure_left _).1 hFrame2).1
  have hAfterC6 := ((sepConj_pure_left _).1 hFrame2).2
  obtain ⟨_, _, _, _, _, hFrame3⟩ := hAfterC6
  obtain ⟨_, _, _, _, _, hBitPure⟩ := hFrame3
  obtain ⟨_, hBit⟩ := hBitPure
  exact ⟨hExit, hC6, hBit⟩

theorem expTwoMulFixedIterReloadSkipCountPost_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  unfold expTwoMulFixedIterReloadSkipCountPost
    expTwoMulFixedIterReloadSkipRest at h
  obtain ⟨_, _, _, _, hMain, _hBaseFrame⟩ := h
  obtain ⟨_, _, _, _, hCount, hRest⟩ := hMain
  obtain ⟨_, _, _, _, _, hCountTail⟩ := hCount
  have hExit : exitCond := ((sepConj_pure_right _).1 hCountTail).2
  obtain ⟨_, _, _, _, _, hRest1⟩ := hRest
  obtain ⟨_, _, _, _, _, hRest2⟩ := hRest1
  obtain ⟨_, _, _, _, _, hRest3⟩ := hRest2
  obtain ⟨_, _, _, _, _, hRest4⟩ := hRest3
  obtain ⟨_, _, _, _, _, hRest5⟩ := hRest4
  obtain ⟨_, _, _, _, _, hRest6⟩ := hRest5
  obtain ⟨_, _, _, _, _, hRest7⟩ := hRest6
  obtain ⟨_, _, _, _, _, hRest8⟩ := hRest7
  obtain ⟨_, _, _, _, _, hRest9⟩ := hRest8
  obtain ⟨_, _, _, _, _, hRest10⟩ := hRest9
  obtain ⟨_, _, _, _, _, hRest11⟩ := hRest10
  obtain ⟨_, _, _, _, _, hRest12⟩ := hRest11
  obtain ⟨_, _, _, _, _, hRest13⟩ := hRest12
  obtain ⟨_, _, _, _, _, hRest14⟩ := hRest13
  obtain ⟨_, _, _, _, _, hRest15⟩ := hRest14
  obtain ⟨_, _, _, _, _, hRest16⟩ := hRest15
  obtain ⟨_, _, _, _, _, hRest16b⟩ := hRest16
  have hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0 :=
    ((sepConj_pure_left _).1 hRest16b).1
  have hAfterC6 := ((sepConj_pure_left _).1 hRest16b).2
  obtain ⟨_, _, _, _, _, hRest17⟩ := hAfterC6
  have hBit :
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 :=
    ((sepConj_pure_right _).1 hRest17).2
  exact ⟨hExit, hC6, hBit⟩

theorem expTwoMulFixedIterCaseLoopPost_pure_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) ∨
    (expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) := by
  rcases expTwoMulFixedIterCaseLoopPost_count_cases h with hSkipCond | hRest
  · obtain ⟨_, _, _, _, hSkipCondPost, _⟩ := hSkipCond
    obtain ⟨hExit, hC6, hBit⟩ :=
      expTwoMulFixedIterSkipCondCountPost_pures hSkipCondPost
    exact Or.inl ⟨hExit, hC6, hBit⟩
  · rcases hRest with hSkip | hRest
    · obtain ⟨_, _, _, _, hSkipPost, _⟩ := hSkip
      obtain ⟨hExit, hC6, hBit⟩ :=
        expTwoMulFixedIterSkipCountPost_pures hSkipPost
      exact Or.inr (Or.inl ⟨hExit, hC6, hBit⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · obtain ⟨hExit, hC6, hBit⟩ :=
          expTwoMulFixedIterReloadCondCountPost_pures hReloadCond
        exact Or.inr (Or.inr (Or.inl ⟨hExit, hC6, hBit⟩))
      · obtain ⟨hExit, hC6, hBit⟩ :=
          expTwoMulFixedIterReloadSkipCountPost_pures hReloadSkip
        exact Or.inr (Or.inr (Or.inr ⟨hExit, hC6, hBit⟩))

theorem expTwoMulFixedIterCaseExitPost_pure_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) ∨
    (expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) := by
  rcases expTwoMulFixedIterCaseExitPost_count_cases h with hSkipCond | hRest
  · obtain ⟨_, _, _, _, hSkipCondPost, _⟩ := hSkipCond
    obtain ⟨hExit, hC6, hBit⟩ :=
      expTwoMulFixedIterSkipCondCountPost_pures hSkipCondPost
    exact Or.inl ⟨hExit, hC6, hBit⟩
  · rcases hRest with hSkip | hRest
    · obtain ⟨_, _, _, _, hSkipPost, _⟩ := hSkip
      obtain ⟨hExit, hC6, hBit⟩ :=
        expTwoMulFixedIterSkipCountPost_pures hSkipPost
      exact Or.inr (Or.inl ⟨hExit, hC6, hBit⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · obtain ⟨hExit, hC6, hBit⟩ :=
          expTwoMulFixedIterReloadCondCountPost_pures hReloadCond
        exact Or.inr (Or.inr (Or.inl ⟨hExit, hC6, hBit⟩))
      · obtain ⟨hExit, hC6, hBit⟩ :=
          expTwoMulFixedIterReloadSkipCountPost_pures hReloadSkip
        exact Or.inr (Or.inr (Or.inr ⟨hExit, hC6, hBit⟩))

end EvmAsm.Evm64.Exp.Compose
