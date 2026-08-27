/-
  EvmAsm.Evm64.Exp.Compose.BaseLengths

  Shared EXP composition length and byte-offset lemmas.
-/

module

public import EvmAsm.Evm64.Exp.CondMulCall

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

abbrev expIterCountNew (iterCount : Word) : Word :=
  iterCount + signExtend12 ((-1 : BitVec 12))

/-- Length of the EXP prologue block, restated in the composition namespace so
    future `skipBlock`-style subsumption proofs can use a compact simp set. -/
theorem exp_prologue_len : (EvmAsm.Evm64.exp_prologue).length = 6 := by
  exact EvmAsm.Evm64.exp_prologue_length

/-- Length of the EXP epilogue block, restated in the composition namespace. -/
theorem exp_epilogue_len : (EvmAsm.Evm64.exp_epilogue).length = 9 := by
  exact EvmAsm.Evm64.exp_epilogue_length

theorem exp_bit_test_block_len : (EvmAsm.Evm64.exp_bit_test_block).length = 3 := by
  exact EvmAsm.Evm64.exp_bit_test_block_length

theorem exp_square_block_len (mulOff : BitVec 21) :
    (EvmAsm.Evm64.exp_square_block mulOff).length = 1 := by
  exact EvmAsm.Evm64.exp_square_block_length mulOff

theorem exp_cond_mul_block_len (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff).length = 2 := by
  exact EvmAsm.Evm64.exp_cond_mul_block_length mulOff skipOff

theorem exp_loop_back_len (backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_loop_back backOff).length = 2 := by
  exact EvmAsm.Evm64.exp_loop_back_length backOff

theorem exp_loop_len (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 8 := by
  exact EvmAsm.Evm64.exp_loop_length mulOff skipOff backOff

theorem exp_iter_body_byte_len (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_iter_body mulOff skipOff).length = 24 := by
  exact EvmAsm.Evm64.exp_iter_body_byte_length mulOff skipOff

theorem exp_loop_back_byte_len (backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_loop_back backOff).length = 8 := by
  exact EvmAsm.Evm64.exp_loop_back_byte_length backOff

theorem exp_loop_byte_len (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 32 := by
  exact EvmAsm.Evm64.exp_loop_byte_length mulOff skipOff backOff

/-- Byte offset of the square-call block within one EXP loop iteration. -/
theorem exp_loop_square_byte_off :
    4 * (EvmAsm.Evm64.exp_bit_test_block).length = 12 := by
  rw [exp_bit_test_block_len]

/-- Byte offset of the conditional multiply block within one EXP loop iteration. -/
theorem exp_loop_cond_mul_byte_off (mulOff : BitVec 21) :
    4 * ((EvmAsm.Evm64.exp_bit_test_block).length +
      (EvmAsm.Evm64.exp_square_block mulOff).length) = 16 := by
  simp only [exp_bit_test_block_len, exp_square_block_len]

/-- Byte offset of the loop-back block within one EXP loop iteration. -/
theorem exp_loop_back_byte_off (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_iter_body mulOff skipOff).length = 24 := by
  exact exp_iter_body_byte_len mulOff skipOff

/-- Byte offset of the next EXP loop iteration. -/
theorem exp_loop_next_iter_byte_off (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 32 := by
  exact exp_loop_byte_len mulOff skipOff backOff

theorem exp_squaring_call_block_len (mulOff : BitVec 21) :
    (EvmAsm.Evm64.exp_squaring_call_block mulOff).length = 26 := by
  exact EvmAsm.Evm64.exp_squaring_call_block_length mulOff

theorem exp_squaring_call_block_byte_len (mulOff : BitVec 21) :
    4 * (EvmAsm.Evm64.exp_squaring_call_block mulOff).length = 104 := by
  exact EvmAsm.Evm64.exp_squaring_call_block_byte_length mulOff

theorem exp_cond_mul_call_with_skip_block_len
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block mulOff skipOff).length = 27 := by
  exact EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_length mulOff skipOff

theorem exp_iter_body_full_len
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff).length = 58 := by
  exact EvmAsm.Evm64.exp_iter_body_full_length mulOff skipOff backOff

theorem exp_loop_pointer_advance_len :
    (EvmAsm.Evm64.exp_loop_pointer_advance).length = 1 := by
  exact EvmAsm.Evm64.exp_loop_pointer_advance_length

theorem exp_loop_pointer_restore_len :
    (EvmAsm.Evm64.exp_loop_pointer_restore).length = 1 := by
  exact EvmAsm.Evm64.exp_loop_pointer_restore_length

theorem evm_exp_len (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.evm_exp mulOff skipOff backOff).length = 75 := by
  exact EvmAsm.Evm64.evm_exp_length mulOff skipOff backOff

/-- Bundled byte offsets for the blocks within one EXP loop iteration. -/
theorem exp_loop_block_byte_offsets (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_bit_test_block).length = 12 ∧
    4 * ((EvmAsm.Evm64.exp_bit_test_block).length +
      (EvmAsm.Evm64.exp_square_block mulOff).length) = 16 ∧
    4 * (EvmAsm.Evm64.exp_iter_body mulOff skipOff).length = 24 ∧
    4 * (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 32 := by
  exact ⟨exp_loop_square_byte_off,
    exp_loop_cond_mul_byte_off mulOff,
    exp_loop_back_byte_off mulOff skipOff,
    exp_loop_next_iter_byte_off mulOff skipOff backOff⟩

theorem exp_prologue_byte_len :
    4 * (EvmAsm.Evm64.exp_prologue).length = 24 := by
  exact EvmAsm.Evm64.exp_prologue_byte_length

theorem exp_epilogue_byte_len :
    4 * (EvmAsm.Evm64.exp_epilogue).length = 36 := by
  exact EvmAsm.Evm64.exp_epilogue_byte_length

/-- Byte offset of the EXP epilogue within the boundary-code layout. -/
theorem exp_boundary_epilogue_byte_off :
    4 * (EvmAsm.Evm64.exp_prologue).length = 24 := by
  exact exp_prologue_byte_len

/-- Byte offset immediately after the EXP prologue/epilogue boundary blocks. -/
theorem exp_boundary_end_byte_off :
    4 * ((EvmAsm.Evm64.exp_prologue).length +
      (EvmAsm.Evm64.exp_epilogue).length) = 60 := by
  simp only [exp_prologue_len, exp_epilogue_len]

/-- Bundled byte offsets for the EXP boundary-code layout. -/
theorem exp_boundary_block_byte_offsets :
    4 * (EvmAsm.Evm64.exp_prologue).length = 24 ∧
    4 * ((EvmAsm.Evm64.exp_prologue).length +
      (EvmAsm.Evm64.exp_epilogue).length) = 60 := by
  exact ⟨exp_boundary_epilogue_byte_off, exp_boundary_end_byte_off⟩

end EvmAsm.Evm64.Exp.Compose
