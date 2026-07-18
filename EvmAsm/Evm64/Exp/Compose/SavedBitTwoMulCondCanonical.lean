/-
  EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCondCanonical

  Canonical-code views of the saved-bit two-MUL conditional-multiply path.
-/

import EvmAsm.Evm64.Exp.TwoMulCondShared

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Canonical-code view of the taken conditional-multiply block followed by
    the loop-back counter update. The loop branch returns to `base + 28`. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget)) :
    let rw := expTwoMulCondRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
       (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word)))
      [(base + 28,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] := by
  have hback :
      ((base + 256) + 4 : Word) +
          signExtend13 EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff =
        base + 28 := by
    exact EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBack_target base
  simpa [expTwoMulIterCountNew] using
    (exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 mulTarget squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base (base + 28) hbase hmt hd hback)

/-- Appended-MUL canonical-code view of the taken conditional-multiply block
    followed by the loop-back counter update. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
      e0 e1 e2 e3 v6 v7 v10 v11 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    let rw := expTwoMulCondRwFromLimbs r0 r1 r2 r3 a0 a1 a2 a3
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
       (.x9 ↦ᵣ iterCount) ** (.x0 ↦ᵣ (0 : Word)))
      [(base + 28,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] :=
  exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    iterCount sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3
    e0 e1 e2 e3 v6 v7 v10 v11 (base + 304)
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base hbase (EvmAsm.Evm64.canonicalExpCondMul_target base).symm
    (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

/-- Canonical-code view of the folded-word conditional-multiply path followed
    by loop-back to the saved-bit iteration entry. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_folded_owned_spec_within
    (iterCount sp evmSp vOld a0 a1 a2 a3 mulTarget : Word) (r : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget)) :
    let rw := expTwoMulCondRw r a0 a1 a2 a3
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (expCondMulFoldedPre sp evmSp iterCount vOld a0 a1 a2 a3 r)
      [(base + 28,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] := by
  have hback :
      ((base + 256) + 4 : Word) +
          signExtend13 EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff =
        base + 28 := by
    exact EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBack_target base
  simpa [expCondMulLoopRest_unfold, expTwoMulIterCountNew, expCondMulFoldedPre_unfold] using
    (exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_folded_owned_spec_within
      iterCount sp evmSp vOld a0 a1 a2 a3 mulTarget r
      squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base (base + 28) hbase hmt hd hback)

/-- Appended-MUL canonical-code view of the folded-word conditional-multiply
    path followed by loop-back to the saved-bit iteration entry. -/
theorem exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_folded_owned_spec_within
    (iterCount sp evmSp vOld a0 a1 a2 a3 : Word) (r : EvmWord)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    let rw := expTwoMulCondRw r a0 a1 a2 a3
    cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expCondMulFoldedPre sp evmSp iterCount vOld a0 a1 a2 a3 r)
      [(base + 28,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw))] :=
  exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_folded_owned_spec_within
    iterCount sp evmSp vOld a0 a1 a2 a3 (base + 304) r
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base hbase
    (EvmAsm.Evm64.canonicalExpCondMul_target base).symm
    (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

end EvmAsm.Evm64.Exp.Compose
