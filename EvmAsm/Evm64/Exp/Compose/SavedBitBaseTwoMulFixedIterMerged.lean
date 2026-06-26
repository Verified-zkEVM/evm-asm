/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterMerged

  Merged-exit views for the fixed x19 two-MUL saved-bit EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Branch-interface view of the fixed x19 no-reload full-iteration
    merged-exit slice. -/
theorem exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
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
    cpsBranchWithin
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
      loopTarget
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h)
      (base + 252)
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) := by
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_msb_bit_test_fixed_skip_full_iter_merged_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hc6 hbase hsqmt hcondmt
      hskip hback hd)

/-- Fixed x19 no-reload merged branch at the reload-path bound. This gives
    the later skip/reload branch merge a uniform step budget. -/
theorem exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
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
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
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
      loopTarget
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h)
      (base + 252)
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) := by
  exact cpsBranchWithin_mono_nSteps
    expTwoMulFixedSkipIterStepBound_le_reload
    (exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hc6 hbase hsqmt hcondmt
      hskip hback hd)

/-- Fixed x19 no-reload merged branch at the reload-path bound, preserving the
    exponent pointer state that the reload path consumes. -/
theorem exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_pointer_frame_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 mulTarget loopTarget : Word)
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
    let ptrFrame : Assertion :=
      (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame)) ** ptrFrame)
      loopTarget
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame)
      (base + 252)
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame) := by
  intro bit c6New squareW rw baseFrame condFrame skipRest condRest ptrFrame
  exact cpsBranchWithin_frameR ptrFrame (by
    dsimp [ptrFrame]
    pcFree)
    (exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hc6 hbase hsqmt hcondmt
      hskip hback hd)

/-- Two-exit view of the fixed x19 reload full-iteration slice, merging
    the conditional-multiply and zero-bit skip outcomes that land at the same
    loop/exit PCs. -/
theorem exp_msb_bit_test_fixed_reload_full_iter_merged_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
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
  intro bit squareW rw baseFrame condFrame skipRest condRest
  have hFour :=
    exp_msb_bit_test_fixed_reload_full_iter_four_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 mulTarget loopTarget squaringMulOff condMulOff skipOff backOff
      base hc6 hbase hsqmt hcondmt hskip hback hd
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

/-- Branch-interface view of the fixed x19 reload full-iteration merged-exit
    slice. -/
theorem exp_msb_bit_test_fixed_reload_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
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
    cpsBranchWithin
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
      loopTarget
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h)
      (base + 252)
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) := by
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_msb_bit_test_fixed_reload_full_iter_merged_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 mulTarget loopTarget squaringMulOff condMulOff skipOff backOff
      base hc6 hbase hsqmt hcondmt hskip hback hd)

/-- Reload merged branch with the input exponent pointer state grouped in the
    same `ptrFrame` shape used by the no-reload framed skip wrapper. -/
theorem exp_msb_bit_test_fixed_reload_full_iter_merged_exit_branch_pointer_frame_pre_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
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
    let ptrFrame : Assertion :=
      (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame)) ** ptrFrame)
      loopTarget
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h)
      (base + 252)
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) := by
  intro bit squareW rw baseFrame condFrame skipRest condRest ptrFrame
  refine cpsBranchWithin_weaken ?_ (fun _ hp => hp) (fun _ hp => hp)
    (exp_msb_bit_test_fixed_reload_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 mulTarget loopTarget squaringMulOff condMulOff skipOff backOff
      base hc6 hbase hsqmt hcondmt hskip hback hd)
  intro h hp
  dsimp [ptrFrame, baseFrame] at hp ⊢
  xperm_hyp hp

/-- Fixed x19 full-iteration branch with the no-reload and reload x6 cases
    merged under a shared pointer-frame precondition. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 mulTarget loopTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
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
    let ptrFrame : Assertion :=
      (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
    let skipCondFrame : Assertion :=
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
    let skipCondRest : Assertion :=
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
    let reloadCondFrame : Assertion :=
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let reloadSkipRest : Assertion :=
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
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let reloadCondRest : Assertion := skipCondRest
    let skipLoopPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let skipExitPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let reloadLoopPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadSkipRest) ** baseFrame) h
    let reloadExitPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadSkipRest) ** baseFrame) h
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      base
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame)) ** ptrFrame)
      loopTarget
      (fun h => skipLoopPost h ∨ reloadLoopPost h)
      (base + 252)
      (fun h => skipExitPost h ∨ reloadExitPost h) := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  by_cases h_c6 : c6New = 0
  · have hReload :=
      exp_msb_bit_test_fixed_reload_full_iter_merged_exit_branch_pointer_frame_pre_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
        e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 mulTarget loopTarget squaringMulOff condMulOff skipOff backOff
        base h_c6 hbase hsqmt hcondmt hskip hback hd
    refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hReload
    · intro h hp
      right
      exact hp
    · intro h hp
      right
      exact hp
  · have hSkip :=
      exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_pointer_frame_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
        e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 mulTarget loopTarget squaringMulOff condMulOff skipOff backOff
        base h_c6 hbase hsqmt hcondmt hskip hback hd
    refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hSkip
    · intro h hp
      left
      exact hp
    · intro h hp
      left
      exact hp

end EvmAsm.Evm64.Exp.Compose
