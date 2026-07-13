/-
  EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulSkipCanonical

  Canonical-code views of the saved-bit two-MUL zero-bit skip path.
-/

import EvmAsm.Evm64.Exp.TwoMulCondShared

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Canonical-code view of the saved-bit loop-back block. -/
theorem exp_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (c : Word) (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    cpsBranchWithin 2 (base + 256)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 28)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c ≠ 0⌝)
      (base + 264)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c = 0⌝) := by
  have htarget :
      ((base + 256) + 4 : Word) +
          signExtend13 EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff =
        base + 28 := by
    exact EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBack_target base
  simpa [expTwoMulIterCountNew] using
    (exp_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      c squaringMulOff condMulOff EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base mulTarget (base + 28) htarget)

/-- Appended-MUL canonical-code view of the saved-bit loop-back block. -/
theorem exp_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (c : Word) (base : Word) :
    cpsBranchWithin 2 (base + 256)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 28)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c ≠ 0⌝)
      (base + 264)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c = 0⌝) :=
  exp_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    c EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff base (base + 304)

/-- Canonical-code view of the zero-bit path through the saved-bit BEQ and
    loop-back update. The nonzero branch remains the conditional-multiply
    handoff at `base + 152`; the loop branch returns to `base + 28`. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCanonicalCode
              base squaringMulOff condMulOff)
            (mul_callable_code mulTarget)) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
       (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount))
      [((base + 152),
          ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)),
        (base + 28,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3))] := by
  have hskip :
      (base + 148 : Word) + signExtend13 EvmAsm.Evm64.canonicalExpCondMulSkipOff =
        base + 256 := by
    exact EvmAsm.Evm64.canonicalExpCondMulSkip_target base
  have hback :
      ((base + 256) + 4 : Word) +
          signExtend13 EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff =
        base + 28 := by
    exact EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBack_target base
  dsimp only
  simpa [expTwoMulIterCountNew, expTwoMulSkipLoopRest_unfold, expTwoMulSkipIterRest_unfold] using
    (exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base (base + 28) hbase hmt hd hskip hback)

/-- Appended-MUL canonical-code view of the zero-bit saved-bit path through
    BEQ and loop-back. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
       (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount))
      [((base + 152),
          ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)),
        (base + 28,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3))] :=
  exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
    e0 e1 e2 e3 v7 v11 (base + 304)
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base hbase
    (EvmAsm.Evm64.canonicalExpSquaringMul_target base).symm
    (evmExpMsbSavedBitTwoMulCanonicalCode_disjoint_appended_mul base)

end EvmAsm.Evm64.Exp.Compose
