/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEpilogueBase

  Base pointer-restore and epilogue adapters for the corrected two-MUL
  saved-bit EXP code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologue
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Rv64.Tactics.XCancelStruct

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

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
  have hPtr : (evmSp + signExtend12 (64 : BitVec 12)) +
      signExtend12 ((-64) : BitVec 12) = evmSp := by
    rw [signExtend12_64, EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64]
    bv_omega
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
      rw [show evmSp + 64 = evmSp + 32#64 + 32#64 from by bv_addr] at hp
      xperm_hyp hp)
    hFramed

end EvmAsm.Evm64.Exp.Compose
