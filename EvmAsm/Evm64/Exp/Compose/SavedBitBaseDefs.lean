/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseDefs

  Shared arithmetic names and length lemmas for the corrected MSB-first
  saved-bit EXP layout.
-/

module

public import EvmAsm.Evm64.Exp.Compose.Base

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

abbrev expTwoMulIterBit (e : Word) : Word :=
  e >>> (63 : BitVec 6).toNat

abbrev expTwoMulIterW (r0 r1 r2 r3 : Word) : EvmWord :=
  expResultWord r0 r1 r2 r3

abbrev expTwoMulIterAw (a0 a1 a2 a3 : Word) : EvmWord :=
  expResultWord a0 a1 a2 a3

abbrev expTwoMulSquareW (r0 r1 r2 r3 : Word) : EvmWord :=
  let w := expTwoMulIterW r0 r1 r2 r3
  w * w

abbrev expTwoMulCondRw (r : EvmWord) (a0 a1 a2 a3 : Word) : EvmWord :=
  r * expTwoMulIterAw a0 a1 a2 a3

abbrev expTwoMulCondRwFromLimbs
    (r0 r1 r2 r3 a0 a1 a2 a3 : Word) : EvmWord :=
  expTwoMulCondRw (expTwoMulIterW r0 r1 r2 r3) a0 a1 a2 a3

abbrev expTwoMulIterRw
    (r0 r1 r2 r3 a0 a1 a2 a3 : Word) : EvmWord :=
  expTwoMulSquareW r0 r1 r2 r3 *
    expTwoMulIterAw a0 a1 a2 a3

abbrev expTwoMulIterCountNew (iterCount : Word) : Word :=
  iterCount + signExtend12 ((-1 : BitVec 12))

theorem exp_msb_bit_test_block_len :
    (EvmAsm.Evm64.exp_msb_bit_test_block).length = 3 := by
  exact EvmAsm.Evm64.exp_msb_bit_test_block_length

theorem exp_save_bit_block_len : (EvmAsm.Evm64.exp_save_bit_block).length = 1 := by
  exact EvmAsm.Evm64.exp_save_bit_block_length

theorem exp_cond_mul_call_with_saved_bit_skip_block_len
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
      mulOff skipOff).length = 27 := by
  exact EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length
    mulOff skipOff

theorem exp_iter_body_full_msb_saved_bit_len
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit
      mulOff skipOff backOff).length = 59 := by
  exact EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_length
    mulOff skipOff backOff

theorem exp_iter_body_full_msb_saved_bit_two_mul_len
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 59 := by
  exact EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_length
    squaringMulOff condMulOff skipOff backOff

theorem evm_exp_msb_saved_bit_len
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.evm_exp_msb_saved_bit mulOff skipOff backOff).length = 76 := by
  exact EvmAsm.Evm64.evm_exp_msb_saved_bit_length mulOff skipOff backOff

theorem evm_exp_msb_saved_bit_two_mul_len
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 76 := by
  exact EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_length
    squaringMulOff condMulOff skipOff backOff

end EvmAsm.Evm64.Exp.Compose
