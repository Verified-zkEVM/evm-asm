/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopCanonicalPrefix

  Canonical-code views of saved-bit EXP full-loop prefix and BEQ gate blocks.
  These wrappers pin the skip and loop-back branches to the canonical offsets
  used by `evmExpMsbSavedBitTwoMulCanonicalWithMulCode`.
-/

import EvmAsm.Evm64.Exp.FullLoopShared

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Canonical-code view of the saved-bit MSB bit-test block. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (e c v10 : Word) (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) :=
  exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base mulTarget

/-- Appended-MUL canonical-code view of the saved-bit MSB bit-test block. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (e c v10 : Word) (base : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) :=
  exp_msb_bit_test_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    e c v10 EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff base (base + 304)

/-- Canonical-code view of the saved-bit copy block. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (bit v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  exp_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    bit v18 squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base mulTarget

/-- Appended-MUL canonical-code view of the saved-bit copy block. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (bit v18 : Word) (base : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  exp_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    bit v18 EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff base (base + 304)

/-- Canonical-code view of the bit-test plus saved-bit prefix. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (e c v10 v18 : Word) (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    let bit := expTwoMulIterBit e
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    e c v10 v18 squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    base mulTarget

/-- Appended-MUL canonical-code view of the bit-test plus saved-bit prefix. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (e c v10 v18 : Word) (base : Word) :
    let bit := expTwoMulIterBit e
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    e c v10 v18 EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff base (base + 304)

/-- Canonical-code view of the saved-bit conditional-multiply BEQ gate. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    (squaringMulOff condMulOff : BitVec 21) (v18 : Word)
    (base mulTarget target : Word)
    (htarget :
      (base + 148 : Word) + signExtend13 EvmAsm.Evm64.canonicalExpCondMulSkipOff =
        target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
    v18 base mulTarget target htarget

/-- Appended-MUL canonical-code view of the saved-bit conditional-multiply
    BEQ gate. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    (v18 : Word) (base target : Word)
    (htarget :
      (base + 148 : Word) + signExtend13 EvmAsm.Evm64.canonicalExpCondMulSkipOff =
        target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff v18 base (base + 304) target htarget

/-- Canonical-code view of the saved-bit conditional-multiply BEQ gate,
    specialized to the canonical skip target. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_target_with_mul_spec_within
    (squaringMulOff condMulOff : BitVec 21) (v18 : Word)
    (base mulTarget : Word) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 256) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_spec_within
    squaringMulOff condMulOff v18 base mulTarget (base + 256)
    (EvmAsm.Evm64.canonicalExpCondMulSkip_target base)

/-- Appended-MUL canonical-code view of the saved-bit conditional-multiply
    BEQ gate, specialized to the canonical skip target. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_target_spec_within
    (v18 : Word) (base : Word) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 256) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
    v18 base (base + 256) (EvmAsm.Evm64.canonicalExpCondMulSkip_target base)

end EvmAsm.Evm64.Exp.Compose
