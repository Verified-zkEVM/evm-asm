/- Shared declaration home for the EXP top-level code/specification pipeline. -/

import EvmAsm.Evm64.Exp.Compose.SavedBitBase
import EvmAsm.Evm64.Exp.Compose.EvmExpCode
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Evm64.Exp.CondMulMarshalPair
import EvmAsm.Evm64.Exp.SquaringCallSeq
import EvmAsm.Evm64.Exp.Compose.TopCodeSubs
import EvmAsm.Evm64.Exp.Compose.TopBoundaryBlocks

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTopSavedBitLoopBackNextPc (base : Word) :
    ((base + 256 : Word) + 8) = base + 264 := by
  bv_omega

/-- Bit-test sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_bit_test_sub a i h)

/-- Squaring-call sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 40) mulOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSquaringAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_squaring_sub a i h)

/-- Conditional-multiply sub-block directly included in the top-level EXP code
    bundle. -/
theorem evmExpCode_iter_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code
      (base + 144) mulOff skipOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterCondMulAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_cond_mul_sub a i h)

/-- MSB bit-test sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_bit_test_sub a i h)

/-- Save-bit sub-block directly included in the corrected saved-bit top-level
    EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_save_bit_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 40) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSquaringAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_save_bit_sub a i h)

/-- Squaring-call sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 44) mulOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitSquaringAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_squaring_sub a i h)

/-- Saved-bit conditional-multiply sub-block directly included in the
    corrected saved-bit top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 148) mulOff skipOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitCondMulAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_cond_mul_sub a i h)

/-- Saved-bit loop-back sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 256)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitLoopBackAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_loop_back_sub a i h)

theorem evmExpMsbSavedBitTwoMulCode_iter_loop_back_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 256)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitLoopBackAddr] at h
  exact evmExpMsbSavedBitTwoMulCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitTwoMulCode_loop_back_sub a i h)

/-- Saved-bit conditional-multiply BEQ skip-gate directly included in the
    corrected saved-bit top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_cond_mul_beq_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.singleton (base + 148) (.BEQ .x18 .x0 skipOff))
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpMsbSavedBitCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_beq_sub
      (base + 148) mulOff skipOff a i h)

/-- Loop-back sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 252)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterLoopBackAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_loop_back_sub a i h)


open EvmAsm.Rv64

/-- Bit-test block lifted to the top-level EXP code bundle. -/
theorem exp_bit_test_evm_exp_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpCode base mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_bit_test_block_spec_within e c v10 (base + 28)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterBitTestNextPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_iter_bit_test_sub)

/-- MSB bit-test block lifted to the corrected saved-bit top-level EXP code
    bundle. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (expTwoMulIterBit e))) := by
  have h := EvmAsm.Evm64.exp_msb_bit_test_block_spec_within e c v10 (base + 28)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterBitTestNextPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpMsbSavedBitCode_iter_bit_test_sub)

/-- Save-bit block lifted to the corrected saved-bit top-level EXP code
    bundle. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_spec_within
    (bit v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_save_bit_block_spec_within bit v18 (base + 40)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSavedBitSaveNextPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpMsbSavedBitCode_iter_save_bit_sub)

/-- Loop-back block lifted to the top-level EXP code bundle. -/
theorem exp_loop_back_evm_exp_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target : Word)
    (htarget : ((base + 252) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 252)
      (evmExpCode base mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c ≠ 0⌝)
      (base + 260)
        ((.x9 ↦ᵣ expIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜expIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 252) target htarget
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopLoopBackNextPc] at h
  simpa [expIterCountNew] using
    (cpsBranchWithin_extend_code (h := h) (hmono := evmExpCode_iter_loop_back_sub))


open EvmAsm.Rv64

/-- Squaring-call factor-1 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_squaring_marshal_factor1_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 40) EvmAsm.Evm64.exp_loop_marshal_factor1) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_marshal_factor1_sub a i h)

/-- Squaring-call factor-2 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_squaring_marshal_result_to_factor2_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 72)
      EvmAsm.Evm64.exp_loop_marshal_result_to_factor2) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringFactor2Addr] at h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_marshal_result_to_factor2_sub a i h)

/-- Squaring-call JAL sub-block directly included in the top-level EXP code
    bundle. -/
theorem evmExpCode_squaring_square_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 104)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringSquareAddr] at h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_square_sub a i h)

/-- Squaring-call unmarshal sub-block directly included in the top-level EXP
    code bundle. -/
theorem evmExpCode_squaring_un_marshal_and_restore_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 108)
      EvmAsm.Evm64.exp_loop_un_marshal_and_restore) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringRestoreAddr] at h
  exact evmExpCode_iter_squaring_sub a i
    (exp_squaring_call_block_code_un_marshal_and_restore_sub a i h)

/-- Conditional-multiply factor-1 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_cond_mul_marshal_factor1_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 148) EvmAsm.Evm64.exp_loop_marshal_factor1) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  have hcall := exp_cond_mul_call_block_code_marshal_factor1_sub
    (base + 148) mulOff a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulCallStartAddr] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply factor-2 marshal sub-block directly included in the
    top-level EXP code bundle. -/
theorem evmExpCode_cond_mul_marshal_a_to_factor2_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 180)
      EvmAsm.Evm64.exp_loop_marshal_a_to_factor2) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulFactor2Addr] at h
  have hcall := exp_cond_mul_call_block_code_marshal_a_to_factor2_sub
    (base + 148) mulOff a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulCallStartAddr] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply JAL sub-block directly included in the top-level EXP
    code bundle. -/
theorem evmExpCode_cond_mul_square_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 212)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulSquareAddr] at h
  have hcall := exp_cond_mul_call_block_code_square_sub (base + 148) mulOff a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulCallStartAddr] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply unmarshal sub-block directly included in the top-level
    EXP code bundle. -/
theorem evmExpCode_cond_mul_un_marshal_and_restore_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 216)
      EvmAsm.Evm64.exp_loop_un_marshal_and_restore) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulRestoreAddr] at h
  have hcall := exp_cond_mul_call_block_code_un_marshal_and_restore_sub
    (base + 148) mulOff a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulCallStartAddr] at hcall
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_call_sub
      (base + 144) mulOff skipOff a i hcall)

/-- Conditional-multiply BEQ skip gate directly included in the top-level EXP
    code bundle. -/
theorem evmExpCode_cond_mul_beq_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.singleton (base + 144) (.BEQ .x10 .x0 skipOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_beq_sub
      (base + 144) mulOff skipOff a i h)


open EvmAsm.Rv64

/-- Squaring-call JAL spec lifted to the top-level EXP code bundle. -/
theorem exp_squaring_square_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 104) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 108)) := by
  have h := EvmAsm.Evm64.exp_square_block_spec_within mulOff vOld (base + 104)
  rw [hmul] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringSquareReturnPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_squaring_square_sub)

/-- Conditional-multiply JAL spec lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_square_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 212) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 212) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 216)) := by
  have h := EvmAsm.Evm64.exp_square_block_spec_within mulOff vOld (base + 212)
  rw [hmul] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulSquareReturnPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_cond_mul_square_sub)


open EvmAsm.Rv64

/-- Squaring-call factor-1 marshal spec lifted to the top-level EXP code
    bundle: at offset `base + 40`, copies result limbs from scratch to
    factor1, exits at `base + 72`. -/
theorem exp_squaring_marshal_factor1_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 (base + 40) (base + 72)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) := by
  have h := EvmAsm.Evm64.exp_loop_marshal_factor1_ofProg_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 40)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringFactor1ExitPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_squaring_marshal_factor1_sub)

/-- Squaring-call factor-2 marshal spec lifted to the top-level EXP code
    bundle: at offset `base + 72`, copies result limbs from scratch to the
    factor2 slot, exits at `base + 104`. -/
theorem exp_squaring_marshal_result_to_factor2_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 (base + 72) (base + 104)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3)) := by
  have h := EvmAsm.Evm64.exp_loop_marshal_result_to_factor2_ofProg_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 72)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringFactor2ExitPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_squaring_marshal_result_to_factor2_sub)

/-- Squaring-call un-marshal-and-restore spec lifted to the top-level EXP
    code bundle: at offset `base + 108`, copies factor1 limbs back to scratch
    and decrements `x12` by 32, exits at `base + 144`. -/
theorem exp_squaring_un_marshal_and_restore_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 (base + 108) (base + 144)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) := by
  have h := EvmAsm.Evm64.exp_loop_un_marshal_and_restore_ofProg_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 108)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringRestoreExitPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_squaring_un_marshal_and_restore_sub)


open EvmAsm.Rv64

/-- Conditional-multiply factor-1 marshal spec lifted to the top-level EXP
    code bundle: at offset `base + 148`, copies result limbs from scratch to
    factor1, exits at `base + 180`. -/
theorem exp_cond_mul_marshal_factor1_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 (base + 148) (base + 180)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) := by
  have h := EvmAsm.Evm64.exp_loop_marshal_factor1_ofProg_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 148)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulFactor2Addr_symm] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_marshal_factor1_sub)

/-- Conditional-multiply factor-2 marshal (from EVM-stack base slot) spec
    lifted to the top-level EXP code bundle: at offset `base + 180`, copies
    base limbs `a` from the EVM-stack window at `evmSp + -64..-40` into the
    factor2 slot, exits at `base + 212`. -/
theorem exp_cond_mul_marshal_a_to_factor2_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 (base + 180) (base + 212)
      (evmExpCode base mulOff skipOff backOff)
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) := by
  have h := EvmAsm.Evm64.exp_loop_marshal_a_to_factor2_ofProg_spec_within
    evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 (base + 180)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulFactor2ExitPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_marshal_a_to_factor2_sub)

/-- Conditional-multiply un-marshal-and-restore spec lifted to the top-level
    EXP code bundle: at offset `base + 216`, copies factor1 limbs back to
    scratch and decrements `x12` by 32, exits at `base + 252`. -/
theorem exp_cond_mul_un_marshal_and_restore_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 (base + 216) (base + 252)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) := by
  have h := EvmAsm.Evm64.exp_loop_un_marshal_and_restore_ofProg_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 216)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulRestoreExitPc] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_un_marshal_and_restore_sub)

/-- Conditional-multiply BEQ skip-gate spec lifted to the top-level EXP code
    bundle: at offset `base + 144`, branches on `x10 == 0` to the cond-mul
    skip target `(base + 144) + signExtend13 skipOff`, otherwise falls
    through to `base + 148` (the cond-mul JAL). -/
theorem exp_cond_mul_beq_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v10 : Word) (base target : Word)
    (htarget : (base + 144 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 144)
      (evmExpCode base mulOff skipOff backOff)
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝)
      (base + 148) ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) := by
  have h := EvmAsm.Rv64.beq_spec_within .x10 .x0 skipOff v10 (0 : Word)
    (base + 144)
  rw [htarget] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulBeqNextPc] at h
  exact cpsBranchWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_beq_sub)

/-- Saved-bit conditional-multiply BEQ skip-gate spec lifted to the corrected
    saved-bit top-level EXP code bundle: at offset `base + 148`, branches on
    `x18 == 0` to the cond-mul skip target, otherwise falls through to
    `base + 152` (the cond-mul taken block). -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base target : Word)
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) := by
  have h := EvmAsm.Rv64.beq_spec_within .x18 .x0 skipOff v18 (0 : Word)
    (base + 148)
  rw [htarget] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSavedBitCondMulBeqNextPc] at h
  exact cpsBranchWithin_extend_code (h := h)
    (hmono := evmExpMsbSavedBitCode_cond_mul_beq_sub)


open EvmAsm.Rv64

/-- Squaring-call marshal prefix and JAL lifted to the top-level EXP code bundle. -/
theorem exp_squaring_marshal_pair_then_square_evm_exp_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 17 (base + 40) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) **
       (.x1 ↦ᵣ (base + 108))) := by
  have h := EvmAsm.Evm64.exp_loop_squaring_marshal_pair_then_square_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff (base + 40)
  have htarget : (((base + 40) + 64 : Word) + signExtend21 mulOff) = mulTarget := by
    rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringMarshalPairTargetPc]
    exact hmul
  rw [htarget] at h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopSquaringMarshalPairReturnPc] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_iter_squaring_sub)

/-- Conditional-multiply marshal pair lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_marshal_pair_evm_exp_spec_within
    (sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 16 (base + 148) (base + 212)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
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
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)) := by
  have h := EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_spec_within
    sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 (base + 148)
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulMarshalPairNextPc] at h
  have hmono :
      ∀ addr instr, EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_code
          (base + 148) addr = some instr →
        (evmExpCode base mulOff skipOff backOff) addr = some instr := by
    intro addr instr hcode
    unfold EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_code at hcode
    exact CodeReq.union_sub
      (evmExpCode_cond_mul_marshal_factor1_sub (base := base)
        (mulOff := mulOff) (skipOff := skipOff) (backOff := backOff))
      (fun a i hfactor2 => by
        rw [EvmAsm.Evm64.Exp.AddrNorm.expTopCondMulFactor2Addr_symm] at hfactor2
        exact evmExpCode_cond_mul_marshal_a_to_factor2_sub
          (base := base) (mulOff := mulOff) (skipOff := skipOff)
          (backOff := backOff) a i hfactor2)
      addr instr hcode
  exact cpsTripleWithin_extend_code (h := h) (hmono := hmono)


open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

theorem expTopIterSquaringAddr (base : Word) :
    (base + 40 : Word) = base + 28 + 12 := by
  bv_omega


theorem expTopIterCondMulAddr (base : Word) :
    (base + 144 : Word) = base + 28 + 116 := by
  bv_omega


theorem expTopIterSavedBitSquaringAddr (base : Word) :
    (base + 44 : Word) = base + 28 + 16 := by
  bv_omega


theorem expTopIterSavedBitCondMulAddr (base : Word) :
    (base + 148 : Word) = base + 28 + 120 := by
  bv_omega


theorem expTopIterSavedBitLoopBackAddr (base : Word) :
    (base + 256 : Word) = base + 28 + 228 := by
  bv_omega


theorem expTopIterLoopBackAddr (base : Word) :
    (base + 252 : Word) = base + 28 + 224 := by
  bv_omega


theorem expTopSquaringFactor2Addr (base : Word) :
    (base + 72 : Word) = base + 40 + 32 := by
  bv_omega


theorem expTopSquaringSquareAddr (base : Word) :
    (base + 104 : Word) = base + 40 + 64 := by
  bv_omega


theorem expTopSquaringRestoreAddr (base : Word) :
    (base + 108 : Word) = base + 40 + 68 := by
  bv_omega


theorem expTopCondMulCallStartAddr (base : Word) :
    (base + 148 : Word) = base + 144 + 4 := by
  bv_omega


theorem expTopCondMulFactor2Addr (base : Word) :
    (base + 180 : Word) = base + 148 + 32 := by
  bv_omega


theorem expTopCondMulFactor2Addr_symm (base : Word) :
    ((base + 148 : Word) + 32) = base + 180 := by
  bv_omega


theorem expTopCondMulSquareAddr (base : Word) :
    (base + 212 : Word) = base + 148 + 64 := by
  bv_omega


theorem expTopCondMulRestoreAddr (base : Word) :
    (base + 216 : Word) = base + 148 + 68 := by
  bv_omega


theorem expTopPointerAdvanceNextPc (base : Word) :
    ((base + 24 : Word) + 4) = base + 28 := by
  bv_omega


theorem expTopPointerRestoreNextPc (base : Word) :
    ((base + 260 : Word) + 4) = base + 264 := by
  bv_omega


theorem expTopEpilogueNextPc (base : Word) :
    ((base + 264 : Word) + 36) = base + 300 := by
  bv_omega


theorem expTopSavedBitEpilogueEntryNextPc (base : Word) :
    ((base + 264 : Word) + 4) = base + 268 := by
  bv_omega


theorem expTopSavedBitEpilogueNextPc (base : Word) :
    ((base + 268 : Word) + 36) = base + 304 := by
  bv_omega


theorem expTopIterBitTestNextPc (base : Word) :
    ((base + 28 : Word) + 12) = base + 40 := by
  bv_omega


theorem expTopSavedBitSaveNextPc (base : Word) :
    ((base + 40 : Word) + 4) = base + 44 := by
  bv_omega


theorem expTopLoopBackNextPc (base : Word) :
    ((base + 252 : Word) + 8) = base + 260 := by
  bv_omega


theorem expTopCondMulBeqNextPc (base : Word) :
    ((base + 144 : Word) + 4) = base + 148 := by
  bv_omega


theorem expTopSavedBitCondMulBeqNextPc (base : Word) :
    ((base + 148 : Word) + 4) = base + 152 := by
  bv_omega


theorem expTopCondMulMarshalPairNextPc (base : Word) :
    ((base + 148 : Word) + 64) = base + 212 := by
  bv_omega

end EvmAsm.Evm64.Exp.Compose
