/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterLoop

  Continuation compositions for the fixed x19 two-MUL saved-bit EXP iteration.
  This file extends `SavedBitBaseTwoMulFixedIter` without pushing that module
  over the Compose file-size cap.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIter
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds
import EvmAsm.Evm64.Exp.TwoMulCondShared

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Fixed x19 no-reload path through the saved-bit BEQ zero branch, followed by
    the loop-back counter update. The nonzero conditional-multiply path remains
    the first exit. -/
theorem exp_msb_bit_test_fixed_skip_save_squaring_beq_skip_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hskip : (base + 136 : Word) + signExtend13 skipOff = base + 244)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 32) + 68)) **
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    cpsNBranchWithin ((((4 + 1) + (17 + 64 + 9)) + 1) + 2) base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ iterCount)))
      [(base + 140,
          (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
            (.x5 ↦ᵣ squareW.getLimbN 3) **
            evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
            regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
            memOwn evmSp ** memOwn (evmSp + 8) **
            memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
            (.x1 ↦ᵣ ((base + 32) + 68)) **
            (.x0 ↦ᵣ (0 : Word)) **
            (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
            (.x20 ↦ᵣ c6New) **
            (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
            ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝) **
            (.x9 ↦ᵣ iterCount))),
        (loopTarget,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest),
        (base + 252,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest)] := by
  intro bit c6New squareW skipRest
  have hBranch :=
    exp_msb_bit_test_fixed_skip_save_squaring_then_cond_mul_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget (base + 244) squaringMulOff condMulOff
      skipOff backOff base hc6 hbase hmt hskip hd
  have hBranchFramed := cpsBranchWithin_frameR (.x9 ↦ᵣ iterCount) (by pcFree) hBranch
  have hBranchSwapped := cpsBranchWithin_swap hBranchFramed
  have hLoop := exp_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
    iterCount squaringMulOff condMulOff skipOff backOff base loopTarget mulTarget hback
  have hLoopFramed := cpsBranchWithin_frameR skipRest (by
    dsimp [skipRest]
    pcFree) hLoop
  have hLoopN := cpsBranchWithin_as_cpsNBranchWithin hLoopFramed
  have hSeq :
      cpsNBranchWithin ((((4 + 1) + (17 + 64 + 9)) + 1) + 2) base
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        _ _ :=
    cpsBranchWithin_cons_cpsNBranchWithin_with_perm_same_cr
      (fun _ hp => by
        dsimp [skipRest, bit, c6New] at hp ⊢
        xperm_hyp hp)
      hBranchSwapped hLoopN
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by xperm_hyp hp) hSeq

/-- Fixed x19 reload path through the saved-bit BEQ zero branch, followed by
    the loop-back counter update. The nonzero conditional-multiply path remains
    the first exit. -/
theorem exp_msb_bit_test_fixed_reload_save_squaring_beq_skip_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hskip : (base + 136 : Word) + signExtend13 skipOff = base + 244)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    cpsNBranchWithin ((((7 + 1) + (17 + 64 + 9)) + 1) + 2) base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ iterCount)))
      [(base + 140,
          (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
            (.x5 ↦ᵣ squareW.getLimbN 3) **
            evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
            regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
            memOwn evmSp ** memOwn (evmSp + 8) **
            memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
            (.x1 ↦ᵣ ((base + 32) + 68)) **
            (.x0 ↦ᵣ (0 : Word)) **
            (.x19 ↦ᵣ nextLimb) **
            (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
            (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
            ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
            (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
            ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
            ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝) **
            (.x9 ↦ᵣ iterCount))),
        (loopTarget,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest),
        (base + 252,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest)] := by
  intro bit squareW skipRest
  have hBranch :=
    exp_msb_bit_test_fixed_reload_save_squaring_then_cond_mul_beq_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget (base + 244) squaringMulOff condMulOff
      skipOff backOff base hc6 hbase hmt hskip hd
  have hBranchFramed := cpsBranchWithin_frameR (.x9 ↦ᵣ iterCount) (by pcFree) hBranch
  have hBranchSwapped := cpsBranchWithin_swap hBranchFramed
  have hLoop := exp_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
    iterCount squaringMulOff condMulOff skipOff backOff base loopTarget mulTarget hback
  have hLoopFramed := cpsBranchWithin_frameR skipRest (by
    dsimp [skipRest]
    pcFree) hLoop
  have hLoopN := cpsBranchWithin_as_cpsNBranchWithin hLoopFramed
  have hSeq :
      cpsNBranchWithin ((((7 + 1) + (17 + 64 + 9)) + 1) + 2) base
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        _ _ :=
    cpsBranchWithin_cons_cpsNBranchWithin_with_perm_same_cr
      (fun _ hp => by
        dsimp [skipRest, bit] at hp ⊢
        xperm_hyp hp)
      hBranchSwapped hLoopN
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by xperm_hyp hp) hSeq

/-- Fixed conditional-multiply call block followed by the loop-back counter
    update. This is the concrete-limb continuation for the saved-bit nonzero
    branch before later owned-scratch adapters. -/
theorem exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    let rw := r * aw
    let rest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    let exitLoop : Assertion :=
      ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest
    let exitDone : Assertion :=
      ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest
    let exits : List (Word × Assertion) :=
      [(loopTarget, exitLoop), (base + 252, exitDone)]
    (cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 140)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x1 ↦ᵣ vOld)) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))))
      exits) := by
  intro r aw rw rest exitLoop exitDone exits
  have hCond :=
    exp_cond_mul_call_block_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget squaringMulOff condMulOff skipOff backOff
      base hbase hmt hd
  have hCondFramed :=
    cpsTripleWithin_frameR
      ((.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) hCond
  have hLoop := exp_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_union_mul_spec_within
    iterCount squaringMulOff condMulOff skipOff backOff base loopTarget mulTarget hback
  have hLoopFramed := cpsBranchWithin_frameR rest (by
    dsimp [rest]
    pcFree) hLoop
  have hSeq :
      cpsBranchWithin ((17 + 64 + 9) + 2) (base + 140)
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        _ loopTarget _ (base + 252) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        dsimp [rest, rw] at hp ⊢
        xperm_hyp hp)
      hCondFramed hLoopFramed
  have hSeqN := cpsBranchWithin_as_cpsNBranchWithin hSeq
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by xperm_hyp hp) hSeqN

/-- Owned-scratch variant of the fixed conditional-multiply call plus
    loop-back continuation. The value limbs stay concrete; only call-clobbered
    scratch registers and memory cells are existentially owned. -/
theorem exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_call_scratch_owned_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3
      e0 e1 e2 e3 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    let rw := r * aw
    let preCore : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))
    let rest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    let exits : List (Word × Assertion) :=
      [(loopTarget,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest),
        (base + 252,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest)]
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 140)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (preCore **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
      exits := by
  intro r aw rw preCore rest exits
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x6)
    (P := preCore ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v6
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x7)
    (P := preCore ** (.x6 ↦ᵣ v6) ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v7
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x10)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v10
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x11)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
      memOwn evmSp ** memOwn (evmSp + 8) ** memOwn (evmSp + 16) **
      memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro v11
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      memOwn (evmSp + 8) ** memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d0
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 8)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d1
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 16)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      ((evmSp + 8) ↦ₘ d1) ** memOwn (evmSp + 24))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d2
  refine cpsNBranchWithin_of_forall_memIs_to_memOwn_perm
    (a := evmSp + 24)
    (P := preCore ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (evmSp ↦ₘ d0) **
      ((evmSp + 8) ↦ₘ d1) ** ((evmSp + 16) ↦ₘ d2))
    (hpre := fun _ hp => by xperm_hyp hp) ?_
  intro d3
  have hConcrete :=
    exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hbase hmt hback hd
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      dsimp [preCore] at hp ⊢
      have hSp0 : (sp + signExtend12 0#12 : Word) = sp := EvmAsm.Evm64.Exp.AddrNorm.expAddr0 sp
      have hSp8 : (sp + signExtend12 8#12 : Word) = sp + 8 := EvmAsm.Evm64.Exp.AddrNorm.expAddr8 sp
      have hSp16 : (sp + signExtend12 16#12 : Word) = sp + 16 := EvmAsm.Evm64.Exp.AddrNorm.expAddr16 sp
      have hSp24 : (sp + signExtend12 24#12 : Word) = sp + 24 := EvmAsm.Evm64.Exp.AddrNorm.expAddr24 sp
      have hEvm0 : (evmSp + signExtend12 0#12 : Word) = evmSp := EvmAsm.Evm64.Exp.AddrNorm.expAddr0 evmSp
      have hEvm8 : (evmSp + signExtend12 8#12 : Word) = evmSp + 8#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr8 evmSp
      have hEvm16 : (evmSp + signExtend12 16#12 : Word) = evmSp + 16#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr16 evmSp
      have hEvm24 : (evmSp + signExtend12 24#12 : Word) = evmSp + 24#64 := EvmAsm.Evm64.Exp.AddrNorm.expAddr24 evmSp
      have hEvm32 : (evmSp + signExtend12 32#12 : Word) = evmSp + 32 := EvmAsm.Evm64.Exp.AddrNorm.expAddr32 evmSp
      have hEvm40 : (evmSp + signExtend12 40#12 : Word) = evmSp + 40 := EvmAsm.Evm64.Exp.AddrNorm.expAddr40 evmSp
      have hEvm48 : (evmSp + signExtend12 48#12 : Word) = evmSp + 48 := EvmAsm.Evm64.Exp.AddrNorm.expAddr48 evmSp
      have hEvm56 : (evmSp + signExtend12 56#12 : Word) = evmSp + 56 := EvmAsm.Evm64.Exp.AddrNorm.expAddr56 evmSp
      rw [hSp0, hSp8, hSp16, hSp24, hEvm32, hEvm40, hEvm48, hEvm56] at hp ⊢
      rw [hEvm0, hEvm8, hEvm16, hEvm24]
      xperm_hyp hp)
    hConcrete

/-- Branch-interface view of
    `exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_call_scratch_owned_spec_within`.
    This keeps downstream composition on the ordinary two-exit branch API. -/
theorem exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_call_scratch_owned_branch_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3
      e0 e1 e2 e3 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    let rw := r * aw
    let preCore : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))
    let rest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    cpsBranchWithin ((17 + 64 + 9) + 2) (base + 140)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (preCore **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24))
      loopTarget
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest)
      (base + 252)
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest) := by
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_call_scratch_owned_spec_within
      iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 e0 e1 e2 e3
      mulTarget loopTarget squaringMulOff condMulOff skipOff backOff base hbase hmt hback hd)

/-- Folded-word variant of the fixed conditional-multiply call plus loop-back
    adapter. The precondition consumes the current result as `evmWordIs` at
    both the stack scratch and EVM stack result slots, matching the squaring
    prefix postcondition. -/
theorem exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_folded_owned_spec_within
    (iterCount sp evmSp vOld a0 a1 a2 a3 mulTarget loopTarget : Word)
    (r : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let rw := expTwoMulCondRw r a0 a1 a2 a3
    let rest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 140)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (expCondMulFoldedPre sp evmSp iterCount vOld a0 a1 a2 a3 r)
      [(loopTarget,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest),
        (base + 252,
          ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest)] := by
  intro rw rest
  let concretePre : Assertion :=
    let preCore : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r.getLimbN 3) **
      ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r.getLimbN 0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r.getLimbN 1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r.getLimbN 2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r.getLimbN 3) **
      ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r.getLimbN 0) **
      ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r.getLimbN 1) **
      ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r.getLimbN 2) **
      ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x1 ↦ᵣ vOld) ** (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word))
    preCore **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24)
  have hConcrete :
      cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 140)
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        concretePre
        [(loopTarget,
            ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest),
          (base + 252,
            ((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest)] := by
    dsimp [concretePre, rest]
    simpa [rw, expTwoMulCondRw, expTwoMulIterAw,
      expResultWord_getLimbN_self r] using
      exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_call_scratch_owned_spec_within
        iterCount sp evmSp (r.getLimbN 3) vOld
        (r.getLimbN 0) (r.getLimbN 1) (r.getLimbN 2) (r.getLimbN 3)
        a0 a1 a2 a3
        (r.getLimbN 0) (r.getLimbN 1) (r.getLimbN 2) (r.getLimbN 3)
        mulTarget loopTarget squaringMulOff condMulOff skipOff backOff
        base hbase hmt hback hd
  refine cpsNBranchWithin_weaken_pre ?_ hConcrete
  intro h hp
  simp only [expCondMulFoldedPre_unfold] at hp
  simpa [concretePre] using
    exp_cond_mul_folded_pre_to_call_scratch_owned_pre
      sp evmSp iterCount vOld a0 a1 a2 a3 r h hp

/-- Branch-interface view of the fixed folded-word conditional-multiply
    adapter. -/
theorem exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_folded_owned_branch_spec_within
    (iterCount sp evmSp vOld a0 a1 a2 a3 mulTarget loopTarget : Word)
    (r : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let rw := expTwoMulCondRw r a0 a1 a2 a3
    let rest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    cpsBranchWithin ((17 + 64 + 9) + 2) (base + 140)
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (expCondMulFoldedPre sp evmSp iterCount vOld a0 a1 a2 a3 r)
      loopTarget
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest)
      (base + 252)
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest) := by
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_folded_owned_spec_within
      iterCount sp evmSp vOld a0 a1 a2 a3 mulTarget loopTarget r
      squaringMulOff condMulOff skipOff backOff base hbase hmt hback hd)

/-- Fixed x19 no-reload full-iteration slice. This composes the no-reload
    prefix through squaring and saved-bit BEQ with the folded conditional
    multiply continuation, leaving the reload entry branch for a later merge. -/
theorem exp_msb_bit_test_fixed_skip_full_iter_four_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hskip : (base + 136 : Word) + signExtend13 skipOff = base + 244)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let condFrame : Assertion :=
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 32) + 68)) **
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let condRest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    cpsNBranchWithin
      expTwoMulFixedSkipIterStepBound
      base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ iterCount)) ** baseFrame))
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
        (base + 252,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame),
        (loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame),
        (base + 252,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame)] := by
  intro bit c6New squareW rw baseFrame condFrame skipRest condRest
  have hSkipRaw :=
    exp_msb_bit_test_fixed_skip_save_squaring_beq_skip_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget loopTarget squaringMulOff condMulOff
      skipOff backOff base hc6 hbase hsqmt hskip hback hd
  have hSkip := cpsNBranchWithin_frameR (F := baseFrame) (by
    dsimp [baseFrame]
    pcFree) hSkipRaw
  have hCondRaw :=
    exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_folded_owned_spec_within
      iterCount sp evmSp ((base + 32) + 68) a0 a1 a2 a3 mulTarget loopTarget
      squareW squaringMulOff condMulOff skipOff backOff base hbase hcondmt hback hd
  have hCondFramed := cpsNBranchWithin_frameR (F := condFrame) (by
    dsimp [condFrame]
    pcFree) hCondRaw
  have hCondHead :
      cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 140)
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        ((((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
          (.x5 ↦ᵣ squareW.getLimbN 3) **
          evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
          regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
          memOwn evmSp ** memOwn (evmSp + 8) **
          memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
          (.x1 ↦ᵣ ((base + 32) + 68)) **
          (.x0 ↦ᵣ (0 : Word)) ** condFrame) **
          (.x9 ↦ᵣ iterCount)) ** baseFrame)
        [(loopTarget,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
          (base + 252,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame)] := by
    exact cpsNBranchWithin_weaken_pre
      (fun _ hp => by
        simp only [expCondMulFoldedPre_unfold] at hp ⊢
        dsimp [baseFrame, condFrame, condRest, rw] at hp ⊢
        xperm_hyp hp)
      hCondFramed
  have hFull :=
    cpsNBranchWithin_extend_head_nbranch hSkip hCondHead
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      dsimp [baseFrame] at hp ⊢
      xperm_hyp hp)
    hFull

/-- Two-exit view of the fixed x19 no-reload full-iteration slice, merging
    the conditional-multiply and zero-bit skip outcomes that land at the same
    loop/exit PCs. -/
theorem exp_msb_bit_test_fixed_skip_full_iter_merged_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hskip : (base + 136 : Word) + signExtend13 skipOff = base + 244)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let condFrame : Assertion :=
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 32) + 68)) **
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let condRest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    cpsNBranchWithin
      expTwoMulFixedSkipIterStepBound
      base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ iterCount)) ** baseFrame))
      [(loopTarget,
          fun h =>
            ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
            ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h),
        (base + 252,
          fun h =>
            ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
            ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h)] := by
  intro bit c6New squareW rw baseFrame condFrame skipRest condRest
  have hFour :=
    exp_msb_bit_test_fixed_skip_full_iter_four_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hc6 hbase hsqmt hcondmt
      hskip hback hd
  refine cpsNBranchWithin_weaken_posts hFour ?_
  intro ex hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · subst ex
    refine ⟨(loopTarget, fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      left
      exact hp
  · subst ex
    refine ⟨(base + 252, fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      left
      exact hp
  · subst ex
    refine ⟨(loopTarget, fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      right
      exact hp
  · subst ex
    refine ⟨(base + 252, fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      right
      exact hp

/-- Fixed x19 reload full-iteration slice. This mirrors the no-reload slice
    while carrying the reloaded exponent limb and pointer state through the
    conditional-multiply continuation. -/
theorem exp_msb_bit_test_fixed_reload_full_iter_four_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 32) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 140) + 64) + signExtend21 condMulOff)
    (hskip : (base + 136 : Word) + signExtend13 skipOff = base + 244)
    (hback : ((base + 244) + 4 : Word) + signExtend13 backOff = loopTarget)
    (hd : CodeReq.Disjoint
            (expIterBodyFullMsbSavedBitTwoMulFixedCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let condFrame : Assertion :=
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let condRest : Assertion :=
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
      (.x1 ↦ᵣ ((base + 140) + 68))
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ iterCount)) ** baseFrame))
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
        (base + 252,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame),
        (loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame),
        (base + 252,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame)] := by
  intro bit squareW rw baseFrame condFrame skipRest condRest
  have hReloadRaw :=
    exp_msb_bit_test_fixed_reload_save_squaring_beq_skip_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hc6 hbase hsqmt hskip hback hd
  have hReload := cpsNBranchWithin_frameR (F := baseFrame) (by
    dsimp [baseFrame]
    pcFree) hReloadRaw
  have hCondRaw :=
    exp_cond_mul_call_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_folded_owned_spec_within
      iterCount sp evmSp ((base + 32) + 68) a0 a1 a2 a3 mulTarget loopTarget
      squareW squaringMulOff condMulOff skipOff backOff base hbase hcondmt hback hd
  have hCondFramed := cpsNBranchWithin_frameR (F := condFrame) (by
    dsimp [condFrame]
    pcFree) hCondRaw
  have hCondHead :
      cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 140)
        ((expIterBodyFullMsbSavedBitTwoMulFixedCode
          base squaringMulOff condMulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        ((((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
          (.x5 ↦ᵣ squareW.getLimbN 3) **
          evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
          regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
          memOwn evmSp ** memOwn (evmSp + 8) **
          memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
          (.x1 ↦ᵣ ((base + 32) + 68)) **
          (.x0 ↦ᵣ (0 : Word)) ** condFrame) **
          (.x9 ↦ᵣ iterCount)) ** baseFrame)
        [(loopTarget,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
          (base + 252,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
              ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame)] := by
    exact cpsNBranchWithin_weaken_pre
      (fun _ hp => by
        simp only [expCondMulFoldedPre_unfold] at hp ⊢
        dsimp [baseFrame, condFrame, condRest, rw] at hp ⊢
        xperm_hyp hp)
      hCondFramed
  have hFull :=
    cpsNBranchWithin_extend_head_nbranch hReload hCondHead
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      dsimp [baseFrame] at hp ⊢
      xperm_hyp hp)
    hFull

end EvmAsm.Evm64.Exp.Compose
