/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePosts

  Named case postconditions for the fixed x19 merged EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

abbrev expTwoMulFixedIterBaseFrame (evmSp a0 a1 a2 a3 : Word) : Assertion :=
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)

abbrev expTwoMulFixedIterPointerPost (ptr nextLimb : Word) : Assertion :=
  (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)

abbrev expTwoMulFixedIterSkipCondFrame (e c6 : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
  (.x20 ↦ᵣ c6New) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝

abbrev expTwoMulFixedIterSkipRest
    (e c6 sp evmSp r0 r1 r2 r3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ squareW.getLimbN 3) **
  evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
  (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
  (.x20 ↦ᵣ c6New) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝

abbrev expTwoMulFixedIterSkipCondRest
    (sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ rw.getLimbN 3) **
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
  evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ (((base + 44) + 140) + 68))

abbrev expTwoMulFixedIterReloadCondFrame
    (e c6 ptr nextLimb : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  (.x19 ↦ᵣ nextLimb) **
  (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New = 0⌝ **
  (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
  ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
  ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝

abbrev expTwoMulFixedIterReloadSkipRest
    (e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ squareW.getLimbN 3) **
  evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
  (.x19 ↦ᵣ nextLimb) **
  (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜c6New = 0⌝ **
  (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
  ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
  ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝

abbrev expTwoMulFixedIterSkipCondCountPost
    (iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3
      a0 a1 a2 a3 base) **
    expTwoMulFixedIterSkipCondFrame e c6

abbrev expTwoMulFixedIterSkipCountPost
    (iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipRest e c6 sp evmSp r0 r1 r2 r3 base) **
    expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3

abbrev expTwoMulFixedIterReloadCondCountPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) (exitCond : Prop) :
    Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3
      a0 a1 a2 a3 base) **
    expTwoMulFixedIterReloadCondFrame e c6 ptr nextLimb

abbrev expTwoMulFixedIterReloadSkipCountPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) (exitCond : Prop) :
    Assertion :=
  (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜exitCond⌝) **
    expTwoMulFixedIterReloadSkipRest e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 base) **
    expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3

abbrev expTwoMulFixedIterSkipLoopPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  (fun ps =>
    expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps) **
  expTwoMulFixedIterPointerPost ptr nextLimb

abbrev expTwoMulFixedIterReloadLoopPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps

abbrev expTwoMulFixedIterSkipExitPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  (fun ps =>
    expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps) **
  expTwoMulFixedIterPointerPost ptr nextLimb

abbrev expTwoMulFixedIterReloadExitPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps

abbrev expTwoMulFixedIterCaseLoopPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps

abbrev expTwoMulFixedIterCaseExitPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  fun ps =>
    expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps

private theorem pcFree_disj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    Assertion.pcFree (fun ps => P ps ∨ Q ps) := by
  intro h hp
  rcases hp with hp | hp
  · exact hP h hp
  · exact hQ h hp

theorem expTwoMulFixedIterBaseFrame_pcFree {evmSp a0 a1 a2 a3 : Word} :
    (expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3).pcFree := by
  unfold expTwoMulFixedIterBaseFrame
  pcFree

theorem expTwoMulFixedIterPointerPost_pcFree {ptr nextLimb : Word} :
    (expTwoMulFixedIterPointerPost ptr nextLimb).pcFree := by
  unfold expTwoMulFixedIterPointerPost
  pcFree

theorem expTwoMulFixedIterSkipCondFrame_pcFree {e c6 : Word} :
    (expTwoMulFixedIterSkipCondFrame e c6).pcFree := by
  unfold expTwoMulFixedIterSkipCondFrame
  pcFree

theorem expTwoMulFixedIterSkipRest_pcFree
    {e c6 sp evmSp r0 r1 r2 r3 base : Word} :
    (expTwoMulFixedIterSkipRest e c6 sp evmSp r0 r1 r2 r3 base).pcFree := by
  unfold expTwoMulFixedIterSkipRest
  pcFree

theorem expTwoMulFixedIterSkipCondRest_pcFree
    {sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    (expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3
      a0 a1 a2 a3 base).pcFree := by
  unfold expTwoMulFixedIterSkipCondRest
  pcFree

theorem expTwoMulFixedIterReloadCondFrame_pcFree
    {e c6 ptr nextLimb : Word} :
    (expTwoMulFixedIterReloadCondFrame e c6 ptr nextLimb).pcFree := by
  unfold expTwoMulFixedIterReloadCondFrame
  pcFree

theorem expTwoMulFixedIterReloadSkipRest_pcFree
    {e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 base : Word} :
    (expTwoMulFixedIterReloadSkipRest e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 base).pcFree := by
  unfold expTwoMulFixedIterReloadSkipRest
  pcFree

theorem expTwoMulFixedIterSkipCondCountPost_pcFree
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base exitCond).pcFree := by
  unfold expTwoMulFixedIterSkipCondCountPost expTwoMulFixedIterSkipCondRest
    expTwoMulFixedIterSkipCondFrame
  pcFree

theorem expTwoMulFixedIterSkipCountPost_pcFree
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} :
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base exitCond).pcFree := by
  unfold expTwoMulFixedIterSkipCountPost expTwoMulFixedIterSkipRest
    expTwoMulFixedIterBaseFrame
  pcFree

theorem expTwoMulFixedIterReloadCondCountPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {exitCond : Prop} :
    (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base exitCond).pcFree := by
  unfold expTwoMulFixedIterReloadCondCountPost expTwoMulFixedIterSkipCondRest
    expTwoMulFixedIterReloadCondFrame
  pcFree

theorem expTwoMulFixedIterReloadSkipCountPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {exitCond : Prop} :
    (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base exitCond).pcFree := by
  unfold expTwoMulFixedIterReloadSkipCountPost expTwoMulFixedIterReloadSkipRest
    expTwoMulFixedIterBaseFrame
  pcFree

theorem expTwoMulFixedIterSkipLoopPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    (expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base).pcFree := by
  unfold expTwoMulFixedIterSkipLoopPost
  exact pcFree_sepConj
    (pcFree_disj
      expTwoMulFixedIterSkipCondCountPost_pcFree
      expTwoMulFixedIterSkipCountPost_pcFree)
    expTwoMulFixedIterPointerPost_pcFree

theorem expTwoMulFixedIterReloadLoopPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    (expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base).pcFree := by
  unfold expTwoMulFixedIterReloadLoopPost
  exact pcFree_disj
    expTwoMulFixedIterReloadCondCountPost_pcFree
    expTwoMulFixedIterReloadSkipCountPost_pcFree

theorem expTwoMulFixedIterSkipExitPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    (expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base).pcFree := by
  unfold expTwoMulFixedIterSkipExitPost
  exact pcFree_sepConj
    (pcFree_disj
      expTwoMulFixedIterSkipCondCountPost_pcFree
      expTwoMulFixedIterSkipCountPost_pcFree)
    expTwoMulFixedIterPointerPost_pcFree

theorem expTwoMulFixedIterReloadExitPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    (expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base).pcFree := by
  unfold expTwoMulFixedIterReloadExitPost
  exact pcFree_disj
    expTwoMulFixedIterReloadCondCountPost_pcFree
    expTwoMulFixedIterReloadSkipCountPost_pcFree

theorem expTwoMulFixedIterCaseLoopPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base).pcFree := by
  unfold expTwoMulFixedIterCaseLoopPost
  exact pcFree_disj
    expTwoMulFixedIterSkipLoopPost_pcFree
    expTwoMulFixedIterReloadLoopPost_pcFree

theorem expTwoMulFixedIterCaseExitPost_pcFree
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base).pcFree := by
  unfold expTwoMulFixedIterCaseExitPost
  exact pcFree_disj
    expTwoMulFixedIterSkipExitPost_pcFree
    expTwoMulFixedIterReloadExitPost_pcFree

instance pcFreeInst_expTwoMulFixedIterCaseLoopPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  ⟨expTwoMulFixedIterCaseLoopPost_pcFree⟩

instance pcFreeInst_expTwoMulFixedIterCaseExitPost
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  ⟨expTwoMulFixedIterCaseExitPost_pcFree⟩

end EvmAsm.Evm64.Exp.Compose
