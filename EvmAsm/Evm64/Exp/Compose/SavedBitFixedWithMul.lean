/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

  Code-bundle helpers for the fixed x19 two-MUL saved-bit EXP program plus
  the out-of-line `mul_callable` body.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologueFixed
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPostDefs
import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterMerged
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMulBase

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Lift a fixed iteration-body N-branch spec into the whole fixed EXP+MUL
    code bundle. -/
theorem cpsNBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exits : List (Word × Assertion)}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget))
    (h : cpsNBranchWithin nSteps entry
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44) squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exits :=
  cpsNBranchWithin_extend_code
    (h := h)
    (hmono :=
      evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
        (base := base) (mulTarget := mulTarget)
        (squaringMulOff := squaringMulOff) (condMulOff := condMulOff)
        (skipOff := skipOff) (backOff := backOff) hd)

/-- The fixed canonical saved-bit EXP wrapper is disjoint from a `mul_callable`
    body appended immediately after the 336-byte wrapper. -/
theorem expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul
    (base : Word) :
    CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      (mul_callable_code (base + 336)) := by
  unfold expMsbSavedBitTwoMulFixedCode
  rw [mul_callable_code_eq_ofProg]
  exact CodeReq.ofProg_disjoint_range_len
    base
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
    84
    (base + 336)
    EvmAsm.Evm64.mul_callable
    64
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
    EvmAsm.Evm64.mul_callable_length
    (fun _ _ hk1 hk2 => by bv_omega)

theorem evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_mul_sub
    {base : Word} :
    ∀ a i, (mul_callable_code (base + 336)) a = some i →
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base) a = some i := by
  unfold evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    evmExpMsbSavedBitTwoMulFixedCanonicalWithMulCode
    evmExpMsbSavedBitTwoMulFixedWithMulCode
  exact CodeReq.mono_union_right
    (expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)
    (fun _ _ h => h)

theorem expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_sub
    {base : Word} :
    ∀ a i,
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        a = some i →
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq]
  exact
    evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
      (base := base) (mulTarget := base + 336)
      (squaringMulOff := EvmAsm.Evm64.canonicalExpSquaringMulOff)
      (condMulOff := EvmAsm.Evm64.canonicalExpCondMulOff)
      (skipOff := EvmAsm.Evm64.canonicalExpCondMulSkipOff)
      (backOff := EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      (expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)

/-- Lift a fixed canonical iteration-body branch spec plus appended
    `mul_callable` into the whole fixed canonical appended EXP+MUL code. -/
theorem cpsBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    {nSteps : Nat} {entry exit_t exit_f base : Word}
    {P Q_t Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (h := h)
    (hmono := expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_sub)

/-- Lift a fixed canonical iteration-body N-branch spec plus appended
    `mul_callable` into the whole fixed canonical appended EXP+MUL code. -/
theorem cpsNBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    {nSteps : Nat} {entry base : Word}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exits :=
  cpsNBranchWithin_extend_code
    (h := h)
    (hmono := expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_sub)

/-- The fixed canonical iteration body inside the 336-byte wrapper is disjoint
    from the appended `mul_callable` body. -/
theorem expIterBodyFullMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul
    (base : Word) :
    CodeReq.Disjoint
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44)
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      (mul_callable_code (base + 336)) :=
  expIterBodyFullMsbSavedBitTwoMulFixedCode_disjoint_mul_of_fixed_disjoint
    (expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)

/-- Canonical-appended whole-code view of the fixed x19 merged full-iteration
    branch. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (fun h => skipLoopPost h ∨ reloadLoopPost h)
      (base + 296)
      (fun h => skipExitPost h ∨ reloadExitPost h) := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
        expTwoMulFixedIterPointerFrame_unfold] at hp
      xperm_hyp hp)
    (fun _ hp => hp) (fun _ hp => hp)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
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
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      (fun v6 => by
        have h :=
          exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
            e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
            r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
            v7 v11 (base + 336) (base + 44)
            EvmAsm.Evm64.canonicalExpSquaringMulOff
            EvmAsm.Evm64.canonicalExpCondMulOff
            EvmAsm.Evm64.canonicalExpCondMulSkipOff
            EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
            (base + 44) hbase
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
        xperm_hyp hp))

/-- N-branch view of the canonical-appended whole-code fixed x19 merged
    full-iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_nbranch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      [((base + 44), (fun h => skipLoopPost h ∨ reloadLoopPost h)),
       ((base + 296), (fun h => skipExitPost h ∨ reloadExitPost h))] := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  exact cpsBranchWithin_as_cpsNBranchWithin
    (exp_msb_bit_test_fixed_full_iter_merged_exit_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)


/-- Body-only-code-req twin of the merged-exit BRANCH spec (path A, bug fjivz). -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (fun h => skipLoopPost h ∨ reloadLoopPost h)
      (base + 296)
      (fun h => skipExitPost h ∨ reloadExitPost h) := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
        expTwoMulFixedIterPointerFrame_unfold] at hp
      xperm_hyp hp)
    (fun _ hp => hp) (fun _ hp => hp)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
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
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      (fun v6 => by
        have h :=
          exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
            e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
            r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
            v7 v11 (base + 336) (base + 44)
            EvmAsm.Evm64.canonicalExpSquaringMulOff
            EvmAsm.Evm64.canonicalExpCondMulOff
            EvmAsm.Evm64.canonicalExpCondMulSkipOff
            EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
            (base + 44) hbase
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
        xperm_hyp hp))

/-- Body-only-code-req twin of the merged-exit NBRANCH spec (path A, bug fjivz). -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_nbranch_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
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
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
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
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      [((base + 44), (fun h => skipLoopPost h ∨ reloadLoopPost h)),
       ((base + 296), (fun h => skipExitPost h ∨ reloadExitPost h))] := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  exact cpsBranchWithin_as_cpsNBranchWithin
    (exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)

end EvmAsm.Evm64.Exp.Compose
