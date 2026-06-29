/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

  Boundary-block sequence helpers for the corrected two-MUL saved-bit EXP
  code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologue
import EvmAsm.Rv64.Tactics.XCancelStruct

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

@[irreducible]
def expTwoMulLoopExitControl (iterCountNew : Word) (exitCond : Prop) : Assertion :=
  (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝

theorem expTwoMulLoopExitControl_unfold
    {iterCountNew : Word} {exitCond : Prop} :
    expTwoMulLoopExitControl iterCountNew exitCond =
      ((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝) := by
  delta expTwoMulLoopExitControl
  rfl

theorem expTwoMulLoopExitControl_pcFree
    {iterCountNew : Word} {exitCond : Prop} :
    (expTwoMulLoopExitControl iterCountNew exitCond).pcFree := by
  rw [expTwoMulLoopExitControl_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopExitControl
    (iterCountNew : Word) (exitCond : Prop) :
    Assertion.PCFree (expTwoMulLoopExitControl iterCountNew exitCond) :=
  ⟨expTwoMulLoopExitControl_pcFree⟩

@[irreducible]
def expTwoMulPointerRestoreEpiloguePreFrame
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) : Assertion :=
  (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
  ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
   ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
   ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
   ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
   ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
   ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
   ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
   ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
   ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))

theorem expTwoMulPointerRestoreEpiloguePreFrame_unfold
    {sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word} :
    expTwoMulPointerRestoreEpiloguePreFrame
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 =
      ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
       ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))) := by
  delta expTwoMulPointerRestoreEpiloguePreFrame
  rfl

theorem expTwoMulPointerRestoreEpiloguePreFrame_pcFree
    {sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word} :
    (expTwoMulPointerRestoreEpiloguePreFrame
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3).pcFree := by
  rw [expTwoMulPointerRestoreEpiloguePreFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulPointerRestoreEpiloguePreFrame
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) :
    Assertion.PCFree
      (expTwoMulPointerRestoreEpiloguePreFrame
        sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3) :=
  ⟨expTwoMulPointerRestoreEpiloguePreFrame_pcFree⟩

@[irreducible]
def expTwoMulPointerRestoreEpiloguePostFrame
    (sp evmSp r0 r1 r2 r3 : Word) : Assertion :=
  (.x2 ↦ᵣ sp) **
  (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
  (.x5 ↦ᵣ r3) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
  evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)

theorem expTwoMulPointerRestoreEpiloguePostFrame_unfold
    {sp evmSp r0 r1 r2 r3 : Word} :
    expTwoMulPointerRestoreEpiloguePostFrame sp evmSp r0 r1 r2 r3 =
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  delta expTwoMulPointerRestoreEpiloguePostFrame
  rfl

theorem expTwoMulPointerRestoreEpiloguePostFrame_pcFree
    {sp evmSp r0 r1 r2 r3 : Word} :
    (expTwoMulPointerRestoreEpiloguePostFrame
      sp evmSp r0 r1 r2 r3).pcFree := by
  rw [expTwoMulPointerRestoreEpiloguePostFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulPointerRestoreEpiloguePostFrame
    (sp evmSp r0 r1 r2 r3 : Word) :
    Assertion.PCFree
      (expTwoMulPointerRestoreEpiloguePostFrame sp evmSp r0 r1 r2 r3) :=
  ⟨expTwoMulPointerRestoreEpiloguePostFrame_pcFree⟩

@[irreducible]
def expTwoMulLoopExitFullStackPreFrame
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) : Assertion :=
  expTwoMulLoopExitControl iterCountNew exitCond **
  ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
   ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
  evmStackIs evmSp (baseWord :: expResultWord d0 d1 d2 d3 :: rest)

theorem expTwoMulLoopExitFullStackPreFrame_unfold
    {sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expTwoMulLoopExitFullStackPreFrame
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
      baseWord rest exitCond =
      (expTwoMulLoopExitControl iterCountNew exitCond **
       ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
       evmStackIs evmSp (baseWord :: expResultWord d0 d1 d2 d3 :: rest)) := by
  delta expTwoMulLoopExitFullStackPreFrame
  rfl

theorem expTwoMulLoopExitFullStackPreFrame_pcFree
    {sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    (expTwoMulLoopExitFullStackPreFrame
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
      baseWord rest exitCond).pcFree := by
  rw [expTwoMulLoopExitFullStackPreFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopExitFullStackPreFrame
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) :
    Assertion.PCFree
      (expTwoMulLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond) :=
  ⟨expTwoMulLoopExitFullStackPreFrame_pcFree⟩

@[irreducible]
def expTwoMulLoopExitFullStackPostFrame
    (sp evmSp iterCountNew r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) : Assertion :=
  expTwoMulLoopExitControl iterCountNew exitCond **
  ((.x2 ↦ᵣ sp) **
   (.x12 ↦ᵣ (evmSp + 32)) **
   (.x5 ↦ᵣ r3) **
   ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
   ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
   ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
   ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
   evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))

theorem expTwoMulLoopExitFullStackPostFrame_unfold
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expTwoMulLoopExitFullStackPostFrame
      sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond =
      (expTwoMulLoopExitControl iterCountNew exitCond **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  delta expTwoMulLoopExitFullStackPostFrame
  rfl

/-- Visible-stack view of the full-stack post frame: after the epilogue,
    `x12` points at the result slot, so consumers can read the live stack as
    `expResultWord r0 r1 r2 r3 :: rest` at `evmSp + 32`, while the consumed base
    word remains framed below the live pointer. -/
theorem expTwoMulLoopExitFullStackPostFrame_stack_unfold
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expTwoMulLoopExitFullStackPostFrame
      sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond =
      (expTwoMulLoopExitControl iterCountNew exitCond **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs evmSp baseWord **
        evmStackIs (evmSp + 32) (expResultWord r0 r1 r2 r3 :: rest))) := by
  rw [expTwoMulLoopExitFullStackPostFrame_unfold, evmStackIs_cons]

theorem expTwoMulLoopExitFullStackPostFrame_pcFree
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    (expTwoMulLoopExitFullStackPostFrame
      sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond).pcFree := by
  rw [expTwoMulLoopExitFullStackPostFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopExitFullStackPostFrame
    (sp evmSp iterCountNew r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) :
    Assertion.PCFree
      (expTwoMulLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) :=
  ⟨expTwoMulLoopExitFullStackPostFrame_pcFree⟩

/-- Pointer-restore followed by the EXP epilogue in the two-MUL saved-bit
    EXP+MUL code bundle. This packages the loop-exit boundary from
    `base + 264` through the final stack-facing writeback at `base + 304`. -/
theorem exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
       ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  let epilogueFrame : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
    ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
    ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
    ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
    ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)
  have hRestore :=
    exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      (evmSp + signExtend12 (64 : BitVec 12))
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hRestoreFramed := cpsTripleWithin_frameR epilogueFrame (by
    dsimp [epilogueFrame]
    pcFree) hRestore
  have hPtr := expTwoMulPointerRestoreBackToEvmSp evmSp
  have hRestoreFramed' :
      cpsTripleWithin 1 (base + 264) (base + 268)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) ** epilogueFrame)
        ((.x12 ↦ᵣ evmSp) ** epilogueFrame) := by
    rw [hPtr] at hRestoreFramed
    exact hRestoreFramed
  have hEpilogue :=
    exp_epilogue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        dsimp [epilogueFrame] at hp ⊢
        xperm_hyp hp)
      hRestoreFramed' hEpilogue
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [epilogueFrame] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => hp)
    hSeq

/-- Exit-control framed view of pointer-restore followed by the EXP epilogue.
    The one-iteration branch exits carry `x9`, `x0`, and a pure loop-exit
    condition; this adapter preserves that control frame through final
    writeback. -/
theorem exp_pointer_restore_then_epilogue_exit_control_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (exitControl **
       ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
         ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
         ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
         ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
         ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))))
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3))) := by
  intro exitControl
  have hBase :=
    exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR exitControl (by
    dsimp [exitControl]
    pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [exitControl] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Stack-tail framed view of pointer-restore followed by the EXP epilogue.
    This keeps the base operand and caller stack tail around the final
    writeback, and folds the produced result word into the visible post stack
    rooted at `evmSp + 32`. -/
theorem exp_pointer_restore_then_epilogue_stack_tail_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    let stackTail : Assertion :=
      expTwoMulLoopExitStackTailFrame evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs evmSp baseWord **
        evmStackIs (evmSp + 32) (expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  have hBase :=
    exp_pointer_restore_then_epilogue_exit_control_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR stackTail (by pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [expTwoMulLoopExitStackTailFrame_unfold] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [expTwoMulLoopExitStackTailFrame_unfold] at hp
      rw [evmStackIs_cons]
      rw [expTwoMulBoundaryResultTailWord_symm] at hp
      xcancel_struct hp)
    hFramed

/-- Full visible-post-stack view of pointer-restore followed by the EXP
    epilogue. This folds the preserved base operand and produced result word
    into the ordinary stack prefix at `evmSp`. -/
theorem exp_pointer_restore_then_epilogue_full_post_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    let stackTail : Assertion :=
      expTwoMulLoopExitStackTailFrame evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      exact hp)
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [evmStackIs_cons]
      xperm_hyp hp)
    (exp_pointer_restore_then_epilogue_stack_tail_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget)

/-- Full visible-post-stack view with the final EVM stack pointer exposed in
    plain consumer-facing form. -/
theorem exp_pointer_restore_then_epilogue_full_post_stack_clean_pointer_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    let stackTail : Assertion :=
      expTwoMulLoopExitStackTailFrame evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  rw [← expTwoMulBoundaryResultEvmSpWord]
  exact exp_pointer_restore_then_epilogue_full_post_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
    squaringMulOff condMulOff skipOff backOff base mulTarget

/-- Full visible-stack view of pointer-restore followed by the EXP epilogue.
    The precondition exposes the preserved base operand, the old destination
    stack word, and the caller tail as one `evmStackIs` prefix; the
    postcondition replaces the destination word with the assembled result. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (expTwoMulLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond)
      (expTwoMulLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [expTwoMulLoopExitFullStackPreFrame_unfold] at hp
      rw [expTwoMulLoopExitControl_unfold] at hp
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [← exp_epilogue_result_word_right evmSp d0 d1 d2 d3
        (evmStackIs (evmSp + 32 + 32) rest)] at hp
      rw [expTwoMulBoundaryResultTailWord] at hp
      rw [expTwoMulLoopExitStackTailFrame_unfold]
      xcancel_struct hp)
    (fun _ hp => by
      rw [expTwoMulLoopExitFullStackPostFrame_unfold]
      rw [expTwoMulLoopExitControl_unfold]
      exact hp)
    (exp_pointer_restore_then_epilogue_full_post_stack_clean_pointer_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget)

/-- Canonical-code view of the loop-exit boundary: pointer restore followed by
    EXP epilogue over `evmExpMsbSavedBitTwoMulCanonicalWithMulCode`. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (expTwoMulLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond)
      (expTwoMulLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) := by
  exact
    exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base mulTarget

/-- Appended-MUL canonical-code view of the loop-exit boundary: pointer restore
    followed by EXP epilogue over the canonical combined code shape. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (base : Word) :
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond)
      (expTwoMulLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) :=
  exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base (base + 304)

end EvmAsm.Evm64.Exp.Compose
