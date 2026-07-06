/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3StepBase

  First half of `EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Step`,
  split out to keep each file under the file-size guardrail
  (`scripts/check-file-size.sh`). The parent module imports this and
  re-exports it transitively, so importers are unaffected.

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

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Relaxed (block-3) raw skip branch: the pointer-frame-free skip branch
    (`SavedBitBaseTwoMulFixedIterMerged.lean:113`) framed with `regOwn .x16`
    (register only, no pointer cell), mirroring the `_pointer_frame` variant
    (`:211`) which frames the full pointer frame instead. -/
theorem exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_relaxed_x16_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
    (e c6 v6 iterCount v10 v18 sp evmSp tOld vOld
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
    let relaxedFrame : Assertion := (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))
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
        (.x9 ↦ᵣ iterCount)) ** baseFrame)) ** relaxedFrame)
      loopTarget
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        relaxedFrame)
      (base + 252)
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        relaxedFrame) := by
  intro bit c6New squareW rw baseFrame condFrame skipRest condRest relaxedFrame
  exact cpsBranchWithin_frameR relaxedFrame (by
    dsimp [relaxedFrame]
    pcFree)
    (exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
      e c6 v6 iterCount v10 v18 sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget loopTarget
      squaringMulOff condMulOff skipOff backOff base hc6 hbase hsqmt hcondmt
      hskip hback hd)

/-- Canonical-appended-code relaxed (block-3) skip branch: lifts the raw
    relaxed skip branch to `base+44`→`base+296`/`base+44` over the canonical
    appended-mul code, mirroring
    `exp_msb_bit_test_fixed_full_iter_merged_exit_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within`
    (`SavedBitFixedWithMul.lean:852`) but with `regOwn .x16` (relaxed pointer)
    and skip-only posts (block 3 never reloads, so `hc6 : c6New ≠ 0`). -/
theorem exp_msb_bit_test_fixed_skip_relaxed_x16_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let relaxedFrame : Assertion := (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
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
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
        (.x9 ↦ᵣ iterCount) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) ** regOwn .x6)
      (base + 44)
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        relaxedFrame)
      (base + 296)
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        relaxedFrame) := by
  intro bit c6New squareW rw baseFrame relaxedFrame condFrame skipRest condRest
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  exact cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
    (P :=
      (.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
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
      (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
      (.x9 ↦ᵣ iterCount) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))))
    (fun v6 => by
      have h :=
        exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_relaxed_x16_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
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
        cpsBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
          h
      refine cpsBranchWithin_weaken ?_ (fun _ hp => hp) (fun _ hp => hp) h'
      intro st hp
      dsimp only [] at hp ⊢
      xperm_hyp hp)

/-- PATH-A FEASIBILITY TEST: body-only-code-req twin of the leaf skip spec.
    Identical statement/proof but over `expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode`
    (loop body + mul, NO canonical prologue/epilogue), proved by SKIPPING the
    final body-only→full lift (lines using `h'`) and returning `h` directly. -/
theorem exp_msb_bit_test_fixed_skip_relaxed_x16_bodyonly_spec_within
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let relaxedFrame : Assertion := (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
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
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
        (.x9 ↦ᵣ iterCount) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) ** regOwn .x6)
      (base + 44)
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        relaxedFrame)
      (base + 296)
      ((fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        relaxedFrame) := by
  intro bit c6New squareW rw baseFrame relaxedFrame condFrame skipRest condRest
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  exact cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
    (P :=
      (.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
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
      (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
      (.x9 ↦ᵣ iterCount) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))))
    (fun v6 => by
      have h :=
        exp_msb_bit_test_fixed_skip_full_iter_merged_exit_branch_reload_bound_relaxed_x16_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
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
      refine cpsBranchWithin_weaken ?_ (fun _ hp => hp) (fun _ hp => hp) h
      intro st hp
      dsimp only [] at hp ⊢
      xperm_hyp hp)

/-- Relaxed (block-3) merged loop-back post: skip-only, `regOwn .x16` in place
    of the pointer frame (block 3 never reloads). -/
abbrev expTwoMulFixedIterMergedLoopPostRelaxedBlock3
    (e c6 iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let relaxedFrame : Assertion := (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))
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
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
    (.x1 ↦ᵣ (((base + 44) + 140) + 68))
  (fun h =>
    ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
      ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame) h ∨
    ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
      ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
    relaxedFrame

/-- Relaxed (block-3) merged loop-exit post: skip-only, `regOwn .x16`. -/
abbrev expTwoMulFixedIterMergedExitPostRelaxedBlock3
    (e c6 iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let relaxedFrame : Assertion := (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))
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
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
    (.x1 ↦ᵣ (((base + 44) + 140) + 68))
  (fun h =>
    ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
      ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame) h ∨
    ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
      ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
    relaxedFrame

/-- Relaxed (block-3) iteration precondition: the full fixed `IterPre` core with
    the pointer frame replaced by `regOwn .x16` (block 3 never dereferences x16,
    whose value collides with the base operand `a3` cell). -/
abbrev expTwoMulFixedIterPreRelaxedBlock3
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) : Assertion :=
  ((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
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
    (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
    (.x9 ↦ᵣ iterCount) **
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
    (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) ** regOwn .x6

/-- Relaxed (block-3) merged one-iteration cpsTriple with continuations and a
    pcFree frame `F` threaded through (mirrors
    `exp_two_mul_fixed_iter_merged_with_continuations_framed_spec_within`). -/
theorem exp_fixed_relaxed_block3_merged_with_continuations_framed_spec_within
    {nCont : Nat} {exit_ : Word} {R F : Assertion}
    (e c6 iterCount v10 v18 sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hc6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hF : F.pcFree) :
    (cpsTripleWithin nCont (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPostRelaxedBlock3 e c6 iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    (cpsTripleWithin nCont (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPostRelaxedBlock3 e c6 iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
      R) →
    cpsTripleWithin
      (expTwoMulFixedReloadIterStepBound + nCont)
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreRelaxedBlock3 e c6 iterCount v10 v18 sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  intro hLoop hExit
  have hbr :=
    cpsBranchWithin_as_cpsNBranchWithin
      (exp_msb_bit_test_fixed_skip_relaxed_x16_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
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

/-- Relaxed (block-3) framed merged-loop succ step (mirrors
    `exp_fixed_loop_body_succ_step_framed`). -/
theorem exp_fixed_loop_body_succ_step_relaxed_block3_framed
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
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedLoopPostRelaxedBlock3 e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreRelaxedBlock3 e c6 iterCount v10 v18 sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 ** F)
      R := by
  rw [← expTwoMulFixedIterationsBodyBound_eq n] at hLoop
  have hExitTriple :
      cpsTripleWithin (expTwoMulFixedIterationsBodyBound n) (base + 296) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedExitPostRelaxedBlock3 e c6 iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ** F)
        R :=
    cpsTripleWithin_mono_nSteps (Nat.zero_le _)
      (cpsTripleWithin_extend_code
        (hmono := by intro a i h; cases h)
        (cpsTripleWithin_refl hExit))
  have hmain :=
    exp_fixed_relaxed_block3_merged_with_continuations_framed_spec_within
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


end EvmAsm.Evm64.Exp.Compose
