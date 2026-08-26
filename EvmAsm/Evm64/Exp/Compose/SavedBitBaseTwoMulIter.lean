/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulIter

  Two-MUL saved-bit EXP iteration CodeReq decomposition.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBaseIter

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- CodeReq decomposition for the corrected saved-bit iteration with separate
    MUL-call offsets at the squaring and conditional-multiply JAL sites. -/
abbrev expIterBodyFullMsbSavedBitTwoMulCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block,
    CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block,
    exp_squaring_call_block_code (base + 16) squaringMulOff,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) condMulOff skipOff,
    CodeReq.ofProg (base + 228) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
          squaringMulOff condMulOff skipOff backOff) := by
  unfold expIterBodyFullMsbSavedBitTwoMulCode
  unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h12 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_msb_bit_test_block).length) = base + 12 := by
    rw [EvmAsm.Evm64.exp_msb_bit_test_block_length]
    rfl
  rw [h12]
  rw [CodeReq.ofProg_append]
  have h16 :
      (base + 12 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_save_bit_block).length) = base + 16 := by
    rw [EvmAsm.Evm64.exp_save_bit_block_length]
    bv_addr
  rw [h16]
  rw [CodeReq.ofProg_append]
  have h120 :
      (base + 16 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff).length) =
        base + 120 := by
    rw [EvmAsm.Evm64.exp_squaring_call_block_length]
    bv_addr
  rw [h120]
  rw [CodeReq.ofProg_append]
  have h228 :
      (base + 120 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
          condMulOff skipOff).length) = base + 228 := by
    rw [EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length]
    bv_addr
  rw [h228]
  rw [← exp_squaring_call_block_code_eq_ofProg (base + 16) squaringMulOff]
  rw [← EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg
    (base + 120) condMulOff skipOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem expIterBodyFullMsbSavedBitTwoMulCode_bit_test_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_msb_bit_test_block 0
    (EvmAsm.Evm64.Exp.AddrNorm.expProgramStartAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_msb_bit_test_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_save_bit_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 12)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_save_bit_block 3
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopSquareProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_save_bit_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_squaring_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 16) squaringMulOff)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg,
    exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 16)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff) 4
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopCondMulProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_squaring_call_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_cond_mul_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) condMulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 120)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
      condMulOff skipOff) 30
    (EvmAsm.Evm64.Exp.AddrNorm.expSavedBitCondMulProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_cond_mul_call_with_saved_bit_skip_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitTwoMulCode_loop_back_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 228)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 228)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 57
    (EvmAsm.Evm64.Exp.AddrNorm.expSavedBitLoopBackProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len,
        exp_loop_back_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_two_mul_len]
      norm_num)

end EvmAsm.Evm64.Exp.Compose
