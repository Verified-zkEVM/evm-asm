/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseIter

  Single-offset saved-bit EXP iteration CodeReq decomposition.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBaseDefs

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- CodeReq decomposition for the corrected EXP square-and-multiply
    iteration: MSB bit-test, save bit, squaring call, saved-bit conditional
    multiply call, and trailing loop back-edge. -/
abbrev expIterBodyFullMsbSavedBitCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block,
    CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block,
    exp_squaring_call_block_code (base + 16) mulOff,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) mulOff skipOff,
    CodeReq.ofProg (base + 228) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expIterBodyFullMsbSavedBitCode_eq_ofProg (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
          mulOff skipOff backOff) := by
  unfold expIterBodyFullMsbSavedBitCode
  unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
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
        (EvmAsm.Evm64.exp_squaring_call_block mulOff).length) =
        base + 120 := by
    rw [EvmAsm.Evm64.exp_squaring_call_block_length]
    bv_addr
  rw [h120]
  rw [CodeReq.ofProg_append]
  have h228 :
      (base + 120 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
          mulOff skipOff).length) = base + 228 := by
    rw [EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length]
    bv_addr
  rw [h228]
  rw [← exp_squaring_call_block_code_eq_ofProg (base + 16) mulOff]
  rw [← EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg
    (base + 120) mulOff skipOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem expIterBodyFullMsbSavedBitCode_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_msb_bit_test_block 0
    (EvmAsm.Evm64.Exp.AddrNorm.expProgramStartAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_msb_bit_test_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_save_bit_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 12)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    EvmAsm.Evm64.exp_save_bit_block 3
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopSquareProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_save_bit_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 16) mulOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg,
    exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 16)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_squaring_call_block mulOff) 4
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopCondMulProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_squaring_call_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) mulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 120)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff) 30
    (EvmAsm.Evm64.Exp.AddrNorm.expSavedBitCondMulProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len,
        exp_cond_mul_call_with_saved_bit_skip_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 228)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i := by
  rw [expIterBodyFullMsbSavedBitCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 228)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 57
    (EvmAsm.Evm64.Exp.AddrNorm.expSavedBitLoopBackProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len, exp_loop_back_len]
      omega)
    (by
      simp only [exp_iter_body_full_msb_saved_bit_len]
      norm_num)

theorem expIterBodyFullMsbSavedBitCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 12) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (exp_squaring_call_block_code (base + 16) mulOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 120) mulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 228)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitCode base mulOff skipOff backOff)
        a = some i) := by
  exact ⟨expIterBodyFullMsbSavedBitCode_bit_test_sub,
    expIterBodyFullMsbSavedBitCode_save_bit_sub,
    expIterBodyFullMsbSavedBitCode_squaring_sub,
    expIterBodyFullMsbSavedBitCode_cond_mul_sub,
    expIterBodyFullMsbSavedBitCode_loop_back_sub⟩

end EvmAsm.Evm64.Exp.Compose
