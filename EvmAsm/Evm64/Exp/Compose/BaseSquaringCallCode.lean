/-
  EvmAsm.Evm64.Exp.Compose.BaseSquaringCallCode

  CodeReq decomposition for the base EXP squaring call block.
-/

module

public import EvmAsm.Evm64.Exp.Compose.BaseLengths
public import EvmAsm.Evm64.Exp.AddrNorm

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- CodeReq decomposition for one EXP squaring call: marshal factor 1, marshal
    the current result into factor 2, call `mul_callable`, then unmarshal the
    multiplication result back into the EXP scratch frame. -/
abbrev exp_squaring_call_block_code (base : Word) (mulOff : BitVec 21) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_loop_marshal_factor1,
    CodeReq.ofProg (base + 32) EvmAsm.Evm64.exp_loop_marshal_result_to_factor2,
    CodeReq.ofProg (base + 64) (EvmAsm.Evm64.exp_square_block mulOff),
    CodeReq.ofProg (base + 68) EvmAsm.Evm64.exp_loop_un_marshal_and_restore
  ]

theorem exp_squaring_call_block_code_eq_ofProg
    (base : Word) (mulOff : BitVec 21) :
    exp_squaring_call_block_code base mulOff =
      CodeReq.ofProg base (EvmAsm.Evm64.exp_squaring_call_block mulOff) := by
  unfold exp_squaring_call_block_code
  unfold EvmAsm.Evm64.exp_squaring_call_block
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h32 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_marshal_factor1).length) = base + 32 := by
    rw [EvmAsm.Evm64.exp_loop_marshal_factor1_length]
    rfl
  rw [h32]
  rw [CodeReq.ofProg_append]
  have h64 :
      (base + 32 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_loop_marshal_result_to_factor2).length) =
        base + 64 := by
    rw [EvmAsm.Evm64.exp_loop_marshal_result_to_factor2_length]
    bv_addr
  rw [h64]
  rw [CodeReq.ofProg_append]
  have h68 :
      (base + 64 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_square_block mulOff).length) = base + 68 := by
    rw [EvmAsm.Evm64.exp_square_block_length]
    bv_addr
  rw [h68]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil]
  rw [CodeReq.union_empty_right]

theorem exp_squaring_call_block_code_marshal_factor1_sub {base : Word}
    {mulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_loop_marshal_factor1) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  rw [exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_squaring_call_block mulOff)
    EvmAsm.Evm64.exp_loop_marshal_factor1 0
    (EvmAsm.Evm64.Exp.AddrNorm.expProgramStartAddr base)
    (by
      unfold EvmAsm.Evm64.exp_squaring_call_block
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_squaring_call_block_len,
        EvmAsm.Evm64.exp_loop_marshal_factor1_length]
      omega)
    (by
      simp only [exp_squaring_call_block_len]
      norm_num)

theorem exp_squaring_call_block_code_marshal_result_to_factor2_sub {base : Word}
    {mulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 32)
      EvmAsm.Evm64.exp_loop_marshal_result_to_factor2) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  rw [exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 32)
    (EvmAsm.Evm64.exp_squaring_call_block mulOff)
    EvmAsm.Evm64.exp_loop_marshal_result_to_factor2 8
    (EvmAsm.Evm64.Exp.AddrNorm.expSquaringCallFactor2ProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_squaring_call_block
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_squaring_call_block_len,
        EvmAsm.Evm64.exp_loop_marshal_result_to_factor2_length]
      omega)
    (by
      simp only [exp_squaring_call_block_len]
      norm_num)

theorem exp_squaring_call_block_code_square_sub {base : Word}
    {mulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 64)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  rw [exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 64)
    (EvmAsm.Evm64.exp_squaring_call_block mulOff)
    (EvmAsm.Evm64.exp_square_block mulOff) 16
    (EvmAsm.Evm64.Exp.AddrNorm.expSquaringCallSquareProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_squaring_call_block
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_squaring_call_block_len, exp_square_block_len]
      omega)
    (by
      simp only [exp_squaring_call_block_len]
      norm_num)

theorem exp_squaring_call_block_code_un_marshal_and_restore_sub {base : Word}
    {mulOff : BitVec 21} :
    ∀ a i, (CodeReq.ofProg (base + 68)
      EvmAsm.Evm64.exp_loop_un_marshal_and_restore) a = some i →
      (exp_squaring_call_block_code base mulOff) a = some i := by
  rw [exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 68)
    (EvmAsm.Evm64.exp_squaring_call_block mulOff)
    EvmAsm.Evm64.exp_loop_un_marshal_and_restore 17
    (EvmAsm.Evm64.Exp.AddrNorm.expSquaringCallRestoreProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_squaring_call_block
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_squaring_call_block_len,
        EvmAsm.Evm64.exp_loop_un_marshal_and_restore_length]
      omega)
    (by
      simp only [exp_squaring_call_block_len]
      norm_num)

end EvmAsm.Evm64.Exp.Compose
