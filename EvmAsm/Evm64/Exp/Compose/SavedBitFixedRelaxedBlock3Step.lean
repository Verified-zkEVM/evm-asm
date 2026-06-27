/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Step

  Relaxed (block-3) variant of the merged fixed-x19 EXP per-iteration body.

  In the final exponent block (k = 192..255) the loop never reloads, so the
  limb pointer register `x16` is never dereferenced.  But `x16` has walked down
  to `evmSp + 24`, which is exactly where the base operand's high limb `a3`
  lives (`expTwoMulIterBaseFrame` puts `a3` at `evmSp_iter - 40`).  The standard
  `IterPre` carries a pointer *cell* `(x16 ↦ ptr) ** (ptr ↦ nextLimb)`, which
  would collide with that `a3` cell.  So block 3 must use a *relaxed*
  precondition that owns `x16` as a register only (`regOwn .x16`) with no
  pointer memory cell.

  This file builds the relaxed body engine (skip-only, since block 3 never
  reloads) by framing `regOwn .x16` onto the pointer-frame-free skip branch
  `exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_…`
  (`SavedBitBaseTwoMulFixedIterMerged.lean:113`), exactly mirroring how the
  `…_pointer_frame_…` variant (`:211`) frames the pointer frame.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterMerged
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3StepBase

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Block-3 final-iteration four-exit reload spec with `a3`-aliasing: at block 3
    the limb pointer `x16 = evmSp + signExtend12 (-40)` is exactly base operand
    `a3`'s address, so the reload-source cell IS the base-frame `a3` cell (listed
    once, no collision).  Mirrors
    `exp_msb_bit_test_fixed_reload_full_iter_four_exit_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within`
    (`SavedBitBaseTwoMulFixedIterLoop.lean:944`) with `ptr := evmSp+se(-40)`,
    `nextLimb := a3`, and the separate source cell dropped (it is base `a3`). -/
theorem exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_spec_within
    (e c6 v6 iterCount v10 v18 sp evmSp tOld vOld
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
    let ptr : Word := evmSp + signExtend12 (-40 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let condFrame : Assertion :=
      (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 32) + 68)) **
      (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
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
        (.x16 ↦ᵣ ptr) **
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
  intro bit ptr squareW rw baseFrame condFrame skipRest condRest
  let baseFrame3 : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2)
  -- the base-frame a3 cell at evmSp+se(-40) IS the reload-source cell at ptr+se0
  have ha3 : (ptr + signExtend12 (0 : BitVec 12)) = evmSp + signExtend12 (-40 : BitVec 12) := by
    show (evmSp + signExtend12 (-40 : BitVec 12)) + signExtend12 (0 : BitVec 12)
        = evmSp + signExtend12 (-40 : BitVec 12)
    bv_addr
  have ha3' : (evmSp + signExtend12 (-40 : BitVec 12)) + signExtend12 (0 : BitVec 12)
      = evmSp + signExtend12 (-40 : BitVec 12) := by bv_addr
  have hReloadRaw :=
    exp_msb_bit_test_fixed_reload_save_squaring_beq_skip_then_loop_back_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 ptr a3 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 v7 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hc6 hbase hsqmt hskip hback hd
  have hReload := cpsNBranchWithin_frameR (F := baseFrame3) (by
    dsimp [baseFrame3]
    pcFree) hReloadRaw
  -- regroup each exit from source form (source cell + baseFrame3) to clean
  -- baseFrame form: the source cell at ptr+se0 = base a3 (via ha3).
  have hReloadClean := cpsNBranchWithin_weaken_posts
    (exits' :=
      [(base + 140,
          ((((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
            (.x5 ↦ᵣ squareW.getLimbN 3) **
            evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
            regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
            memOwn evmSp ** memOwn (evmSp + 8) **
            memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
            (.x1 ↦ᵣ ((base + 32) + 68)) **
            (.x0 ↦ᵣ (0 : Word)) ** condFrame) **
            (.x9 ↦ᵣ iterCount)) ** baseFrame)),
        (loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame),
        (base + 252,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame)])
    hReload (by
      intro ex hex
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hex
      rcases hex with rfl | rfl | rfl
      · exact ⟨_, .head _, rfl, fun h hp => by
          rw [ha3] at hp
          dsimp [bit, squareW, baseFrame, baseFrame3, condFrame] at hp ⊢
          xperm_hyp hp⟩
      · exact ⟨_, .tail _ (.head _), rfl, fun h hp => by
          rw [ha3] at hp
          dsimp [bit, squareW, baseFrame, baseFrame3, skipRest] at hp ⊢
          xperm_hyp hp⟩
      · exact ⟨_, .tail _ (.tail _ (.head _)), rfl, fun h hp => by
          rw [ha3] at hp
          dsimp [bit, squareW, baseFrame, baseFrame3, skipRest] at hp ⊢
          xperm_hyp hp⟩)
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
    cpsNBranchWithin_extend_head_nbranch hReloadClean hCondHead
  refine cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      rw [ha3]
      dsimp [baseFrame, baseFrame3, condFrame] at hp ⊢
      xperm_hyp hp)
    hFull

/-- Canonical-appended whole-code view of the block-3 `a3`-aliased reload
    four-exit spec.  Mirrors the skip canonical lift
    (`exp_msb_bit_test_fixed_skip_relaxed_x16_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within`)
    but for the reload four-exit: instantiate the raw four-exit at `base + 44`
    with canonical offsets/targets, fold the union into the canonical-appended
    iter-body code, then lift to the 336-byte wrapper code. `x6` is abstracted
    to `regOwn`. -/
theorem exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_canonical_spec_within
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let ptr : Word := evmSp + signExtend12 (-40 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let condFrame : Assertion :=
      (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) **
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame) ** regOwn .x6)
      [((base + 44),
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
        (base + 296,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame),
        ((base + 44),
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame),
        (base + 296,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame)] := by
  intro bit ptr squareW rw baseFrame condFrame skipRest condRest
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  exact cpsNBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
    (P :=
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) **
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame)
    (fun v6 => by
      have h :=
        exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_spec_within
          e c6 v6 iterCount v10 v18 sp evmSp tOld vOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 (base + 336) (base + 44)
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
          (base + 44) hc6 hbase
          (EvmAsm.Evm64.canonicalExpFixedSquaringMul_target base).symm
          (EvmAsm.Evm64.canonicalExpFixedCondMul_target base).symm
          (EvmAsm.Evm64.canonicalExpFixedCondMulSkip_target base)
          (EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBack_target base)
          (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)
      rw [hExit] at h
      rw [← expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq base] at h
      have h' :=
        cpsNBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
          h
      refine cpsNBranchWithin_weaken_pre ?_ h'
      intro st hp
      dsimp only [] at hp ⊢
      xperm_hyp hp)

/-- Block-3 final-iteration (reload) merged-exit post: the disjunction of the
    cond/skip exit branches of the canonical `a3`-aliased reload four-exit at
    `iterCountNew = 0`. -/
abbrev expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload
    (e c6 iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let ptr : Word := evmSp + signExtend12 (-40 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let condFrame : Assertion :=
    (.x19 ↦ᵣ a3) **
    (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let skipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ a3) **
    (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
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
    (.x1 ↦ᵣ (((base + 44) + 140) + 68))
  fun h =>
    ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
      ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
    ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
      ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h

/-- Block-3 final-iteration (k=255, reload) framed step: the loop-back edge is
    vacuous (`iterCountNew = 0`), so only the exit branches survive.  Mirrors
    `exp_fixed_loop_body_final_succ_step_framed` for the block-3 reload pre. -/
theorem exp_fixed_loop_body_final_succ_step_relaxed_block3_framed
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R F : Assertion)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F) ps →
        R ps) :
    cpsTripleWithin expTwoMulFixedReloadIterStepBound (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      ((((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))) **
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
        (.x9 ↦ᵣ iterCount)) **
        (((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
         ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
         ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
         ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))) ** regOwn .x6) ** F)
      R := by
  have hFour :=
    exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_canonical_spec_within
      e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hc6 hbase
  have hFourF := cpsNBranchWithin_frameR hF hFour
  have hm := cpsNBranchWithin_merge (exit_ := base + 296) (R := R) hFourF (by
    intro ex hmem
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · -- cond loop-back at base+44: vacuous (iterCountNew ≠ 0 contradicts hzero)
      intro Rf _ s _ hPR _
      exfalso
      have hne := holdsFor_pure.mp (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left
          (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left
            (holdsFor_sepConj_elim_left hPR))))))
      exact hne hzero
    · -- cond exit at base+296: → R via hExit (left disjunct)
      refine cpsTripleWithin_extend_code (hmono := by intro a i h; cases h)
        (cpsTripleWithin_refl ?_)
      intro ps hp
      exact hExit ps (sepConj_mono_left (fun _ h => Or.inl h) ps hp)
    · -- skip loop-back at base+44: vacuous
      intro Rf _ s _ hPR _
      exfalso
      have hne := holdsFor_pure.mp (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left
          (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left
            (holdsFor_sepConj_elim_left hPR))))))
      exact hne hzero
    · -- skip exit at base+296: → R via hExit (right disjunct)
      refine cpsTripleWithin_extend_code (hmono := by intro a i h; cases h)
        (cpsTripleWithin_refl ?_)
      intro ps hp
      exact hExit ps (sepConj_mono_left (fun _ h => Or.inr h) ps hp))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hm

/-- PATH-A body-only twin of `exp_fixed_relaxed_block3_merged_with_continuations_framed_spec_within`:
    same merge, over the body-only code req (no canonical prologue/epilogue), using the
    body-only leaf twin. -/
theorem exp_fixed_relaxed_block3_merged_with_continuations_framed_bodyonly_spec_within
    {nCont : Nat} {exit_ : Word} {R F : Assertion}
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree) :
    (cpsTripleWithin nCont (base + 44) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPostRelaxedBlock3 e c6 iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin nCont (base + 296) exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPostRelaxedBlock3 e c6 iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin
      (expTwoMulFixedReloadIterStepBound + nCont)
      (base + 44)
      exit_
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreRelaxedBlock3 e c6 iterCount v10 v18 sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  have hbr :=
    cpsBranchWithin_as_cpsNBranchWithin
      (exp_msb_bit_test_fixed_skip_relaxed_x16_bodyonly_spec_within
        e c6 iterCount v10 v18 sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hc6 hbase)
  have hbrF := cpsNBranchWithin_frameR hF hbr
  refine cpsNBranchWithin_merge hbrF ?_
  intro ex hmem
  simp only [List.map] at hmem
  cases hmem with
  | head => exact hLoop
  | tail _ htail =>
      cases htail with
      | head => exact hExit
      | tail _ hnil => cases hnil

/-- PATH-A body-only twin of `exp_fixed_loop_body_succ_step_relaxed_block3_framed`. -/
theorem exp_fixed_loop_body_succ_step_relaxed_block3_bodyonly_framed
    (n : Nat)
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R F : Assertion)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hExit :
      ∀ ps,
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3 e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F) ps →
        R ps)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedLoopPostRelaxedBlock3 e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreRelaxedBlock3 e c6 iterCount v10 v18 sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  rw [← expTwoMulFixedIterationsBodyBound_eq n] at hLoop
  have hExitTriple :
      cpsTripleWithin (expTwoMulFixedIterationsBodyBound n) (base + 296) (base + 296)
        (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3 e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
        R :=
    cpsTripleWithin_mono_nSteps (Nat.zero_le _)
      (cpsTripleWithin_extend_code
        (hmono := by intro a i h; cases h)
        (cpsTripleWithin_refl hExit))
  have hmain :=
    exp_fixed_relaxed_block3_merged_with_continuations_framed_bodyonly_spec_within
      (nCont := expTwoMulFixedIterationsBodyBound n) (exit_ := base + 296)
      (R := R) (F := F)
      e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hc6 hbase hF hLoop hExitTriple
  have hbound :
      expTwoMulFixedReloadIterStepBound + expTwoMulFixedIterationsBodyBound n
        = (n + 1) * 193 := by
    rw [expTwoMulFixedReloadIterStepBound_eq, expTwoMulFixedIterationsBodyBound_eq]
    ring
  rw [hbound] at hmain
  exact hmain

/-- PATH-A body-only twin of
    `exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_canonical_spec_within`:
    same four-exit reload spec but over the body-only code req, proved by SKIPPING the
    final body-only→full lift and using the body-only `h` directly. -/
theorem exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_canonical_bodyonly_spec_within
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let ptr : Word := evmSp + signExtend12 (-40 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let condFrame : Assertion :=
      (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) **
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame) ** regOwn .x6)
      [((base + 44),
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
        (base + 296,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame),
        ((base + 44),
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame),
        (base + 296,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
            ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame)] := by
  intro bit ptr squareW rw baseFrame condFrame skipRest condRest
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  exact cpsNBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
    (P :=
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ ptr) **
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame)
    (fun v6 => by
      have h :=
        exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_spec_within
          e c6 v6 iterCount v10 v18 sp evmSp tOld vOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 (base + 336) (base + 44)
          EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
          (base + 44) hc6 hbase
          (EvmAsm.Evm64.canonicalExpFixedSquaringMul_target base).symm
          (EvmAsm.Evm64.canonicalExpFixedCondMul_target base).symm
          (EvmAsm.Evm64.canonicalExpFixedCondMulSkip_target base)
          (EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBack_target base)
          (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)
      rw [hExit] at h
      rw [← expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq base] at h
      refine cpsNBranchWithin_weaken_pre ?_ h
      intro st hp
      dsimp only [] at hp ⊢
      xperm_hyp hp)

/-- PATH-A body-only twin of `exp_fixed_loop_body_final_succ_step_relaxed_block3_framed`. -/
theorem exp_fixed_loop_body_final_succ_step_relaxed_block3_bodyonly_framed
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R F : Assertion)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F) ps →
        R ps) :
    cpsTripleWithin expTwoMulFixedReloadIterStepBound (base + 44) (base + 296)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      ((((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))) **
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
        (.x9 ↦ᵣ iterCount)) **
        (((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
         ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
         ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
         ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))) ** regOwn .x6) ** F)
      R := by
  have hFour :=
    exp_msb_bit_test_fixed_reload_full_iter_four_exit_block3_a3_canonical_bodyonly_spec_within
      e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hc6 hbase
  have hFourF := cpsNBranchWithin_frameR hF hFour
  have hm := cpsNBranchWithin_merge (exit_ := base + 296) (R := R) hFourF (by
    intro ex hmem
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · intro Rf _ s _ hPR _
      exfalso
      have hne := holdsFor_pure.mp (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left
          (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left
            (holdsFor_sepConj_elim_left hPR))))))
      exact hne hzero
    · refine cpsTripleWithin_extend_code (hmono := by intro a i h; cases h)
        (cpsTripleWithin_refl ?_)
      intro ps hp
      exact hExit ps (sepConj_mono_left (fun _ h => Or.inl h) ps hp)
    · intro Rf _ s _ hPR _
      exfalso
      have hne := holdsFor_pure.mp (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left
          (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left
            (holdsFor_sepConj_elim_left hPR))))))
      exact hne hzero
    · refine cpsTripleWithin_extend_code (hmono := by intro a i h; cases h)
        (cpsTripleWithin_refl ?_)
      intro ps hp
      exact hExit ps (sepConj_mono_left (fun _ h => Or.inr h) ps hp))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hm

end EvmAsm.Evm64.Exp.Compose
