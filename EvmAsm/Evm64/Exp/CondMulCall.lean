/-
  EvmAsm.Evm64.Exp.CondMulCall

  CodeReq decomposition for the conditional-multiply taken-branch call block.
  This mirrors `Exp/SquaringCall.lean`, but the second marshal block sources
  the fixed base `a` into MUL factor2 instead of copying the running result.

  Refs: GH #92, beads `evm-asm-b4asy`.
-/

module

public import EvmAsm.Evm64.Exp.CondMulMarshalPair
public import EvmAsm.Evm64.Exp.SquaringCall
public import EvmAsm.Evm64.Multiply.Callable

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (CodeReq Instr Program seq single)

/-- 4-block `unionAll` decomposition of `exp_cond_mul_call_block mulOff`.
    The block layout is:

    * offset 0:  marshal running result into MUL factor1
    * offset 32: marshal fixed base `a` into MUL factor2
    * offset 64: JAL to `mul_callable`
    * offset 68: unmarshal MUL output and restore `x12`
-/
abbrev exp_cond_mul_call_block_code (base : Word) (mulOff : BitVec 21) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base                exp_loop_marshal_factor1,
    CodeReq.ofProg (base + 32)         exp_loop_marshal_a_to_factor2,
    CodeReq.ofProg (base + 64)         (exp_square_block mulOff),
    CodeReq.ofProg (base + 68)         exp_loop_un_marshal_and_restore
  ]

theorem exp_cond_mul_call_block_code_eq_ofProg (base : Word) (mulOff : BitVec 21) :
    exp_cond_mul_call_block_code base mulOff =
      CodeReq.ofProg base (exp_cond_mul_call_block mulOff) := by
  unfold exp_cond_mul_call_block_code exp_cond_mul_call_block
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil,
    CodeReq.union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [CodeReq.ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * exp_loop_marshal_factor1.length) =
        base + 32 by rw [exp_loop_marshal_factor1_length]; rfl]
  rw [CodeReq.ofProg_append]
  rw [show (base + 32) +
        BitVec.ofNat 64 (4 * exp_loop_marshal_a_to_factor2.length) =
        base + 64 by
    rw [exp_loop_marshal_a_to_factor2_length]
    exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor2_end_addr base]
  rw [CodeReq.ofProg_append]
  rw [show (base + 64) + BitVec.ofNat 64 (4 * (exp_square_block mulOff).length) =
        base + 68 by
    rw [exp_square_block_length]
    exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_square_end_addr base]

theorem exp_cond_mul_call_block_code_marshal_factor1_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg base exp_loop_marshal_factor1) a = some i →
      (exp_cond_mul_call_block_code base mulOff) a = some i := by
  unfold exp_cond_mul_call_block_code
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem exp_cond_mul_call_block_code_marshal_a_to_factor2_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg (base + 32)
      exp_loop_marshal_a_to_factor2) a = some i →
      (exp_cond_mul_call_block_code base mulOff) a = some i := by
  unfold exp_cond_mul_call_block_code
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_factor1_length,
        exp_loop_marshal_a_to_factor2_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor1_factor2_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

theorem exp_cond_mul_call_block_code_square_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg (base + 64) (exp_square_block mulOff)) a = some i →
      (exp_cond_mul_call_block_code base mulOff) a = some i := by
  unfold exp_cond_mul_call_block_code
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_factor1_length,
        exp_square_block_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor1_square_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_a_to_factor2_length,
        exp_square_block_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor2_square_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

theorem exp_cond_mul_call_block_code_un_marshal_and_restore_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (CodeReq.ofProg (base + 68) exp_loop_un_marshal_and_restore) a = some i →
      (exp_cond_mul_call_block_code base mulOff) a = some i := by
  unfold exp_cond_mul_call_block_code
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_factor1_length,
        exp_loop_un_marshal_and_restore_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor1_restore_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_loop_marshal_a_to_factor2_length,
        exp_loop_un_marshal_and_restore_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_factor2_restore_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_square_block_length,
        exp_loop_un_marshal_and_restore_length] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expCallBlock_square_restore_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

/-- The two-block cond-mul marshal-pair prefix is contained in the full
    conditional-multiply call block code. -/
theorem exp_cond_mul_call_block_code_marshal_pair_sub
    (base : Word) (mulOff : BitVec 21) :
    ∀ a i, (exp_loop_cond_mul_marshal_pair_code base) a = some i →
      (exp_cond_mul_call_block_code base mulOff) a = some i := by
  intro a i h
  exact CodeReq.union_sub
    (exp_cond_mul_call_block_code_marshal_factor1_sub base mulOff)
    (exp_cond_mul_call_block_code_marshal_a_to_factor2_sub base mulOff)
    a i h

/-- CodeReq decomposition for the conditional-multiply step with its leading
    BEQ skip gate. The BEQ lives at `base`; the taken call block starts at
    `base + 4` and is skipped when the tested exponent bit is zero. -/
abbrev exp_cond_mul_call_with_skip_block_code
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.singleton base (.BEQ .x10 .x0 skipOff),
    exp_cond_mul_call_block_code (base + 4) mulOff
  ]

theorem exp_cond_mul_call_with_skip_block_code_eq_ofProg
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) :
    exp_cond_mul_call_with_skip_block_code base mulOff skipOff =
      CodeReq.ofProg base (exp_cond_mul_call_with_skip_block mulOff skipOff) := by
  unfold exp_cond_mul_call_with_skip_block_code
  unfold exp_cond_mul_call_with_skip_block
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil,
    CodeReq.union_empty_right]
  unfold single seq Program
  symm
  rw [CodeReq.ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * [Instr.BEQ .x10 .x0 skipOff].length) =
      base + 4 by rfl]
  rw [CodeReq.ofProg_singleton]
  rw [← exp_cond_mul_call_block_code_eq_ofProg (base + 4) mulOff]
  unfold exp_cond_mul_call_block_code
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem exp_cond_mul_call_with_skip_block_code_beq_sub
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) :
    ∀ a i, (CodeReq.singleton base (.BEQ .x10 .x0 skipOff)) a = some i →
      (exp_cond_mul_call_with_skip_block_code base mulOff skipOff) a = some i := by
  unfold exp_cond_mul_call_with_skip_block_code
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem exp_cond_mul_call_with_skip_block_code_call_sub
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) :
    ∀ a i, (exp_cond_mul_call_block_code (base + 4) mulOff) a = some i →
      (exp_cond_mul_call_with_skip_block_code base mulOff skipOff) a = some i := by
  rw [exp_cond_mul_call_with_skip_block_code_eq_ofProg,
    exp_cond_mul_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 4)
    (exp_cond_mul_call_with_skip_block mulOff skipOff)
    (exp_cond_mul_call_block mulOff) 1
    (EvmAsm.Evm64.Exp.AddrNorm.expCondMulCallSkipCallProgramAddr base)
    (by
      unfold exp_cond_mul_call_with_skip_block single
      simp only [seq]
      unfold Program
      rfl)
    (by
      simp only [exp_cond_mul_call_with_skip_block_length,
        exp_cond_mul_call_block_length]
      omega)
    (by
      simp only [exp_cond_mul_call_with_skip_block_length]
      norm_num)

/-- CodeReq decomposition for the conditional-multiply step with its leading
    BEQ skip gate, branching on the saved bit in `x18`. The BEQ lives at
    `base`; the taken call block starts at `base + 4` and is skipped when
    the saved exponent bit is zero. -/
abbrev exp_cond_mul_call_with_saved_bit_skip_block_code
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.singleton base (.BEQ .x18 .x0 skipOff),
    exp_cond_mul_call_block_code (base + 4) mulOff
  ]

theorem exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) :
    exp_cond_mul_call_with_saved_bit_skip_block_code base mulOff skipOff =
      CodeReq.ofProg base
        (exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff) := by
  unfold exp_cond_mul_call_with_saved_bit_skip_block_code
  unfold exp_cond_mul_call_with_saved_bit_skip_block
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil,
    CodeReq.union_empty_right]
  unfold single seq Program
  symm
  rw [CodeReq.ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * [Instr.BEQ .x18 .x0 skipOff].length) =
      base + 4 by rfl]
  rw [CodeReq.ofProg_singleton]
  rw [← exp_cond_mul_call_block_code_eq_ofProg (base + 4) mulOff]
  unfold exp_cond_mul_call_block_code
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem exp_cond_mul_call_with_saved_bit_skip_block_code_beq_sub
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) :
    ∀ a i, (CodeReq.singleton base (.BEQ .x18 .x0 skipOff)) a = some i →
      (exp_cond_mul_call_with_saved_bit_skip_block_code base mulOff skipOff)
        a = some i := by
  unfold exp_cond_mul_call_with_saved_bit_skip_block_code
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem exp_cond_mul_call_with_saved_bit_skip_block_code_call_sub
    (base : Word) (mulOff : BitVec 21) (skipOff : BitVec 13) :
    ∀ a i, (exp_cond_mul_call_block_code (base + 4) mulOff) a = some i →
      (exp_cond_mul_call_with_saved_bit_skip_block_code base mulOff skipOff)
        a = some i := by
  rw [exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg,
    exp_cond_mul_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 4)
    (exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff)
    (exp_cond_mul_call_block mulOff) 1
    (EvmAsm.Evm64.Exp.AddrNorm.expCondMulCallSkipCallProgramAddr base)
    (by
      unfold exp_cond_mul_call_with_saved_bit_skip_block single
      simp only [seq]
      unfold Program
      rfl)
    (by
      simp only [exp_cond_mul_call_with_saved_bit_skip_block_length,
        exp_cond_mul_call_block_length]
      omega)
    (by
      simp only [exp_cond_mul_call_with_saved_bit_skip_block_length]
      norm_num)

end EvmAsm.Evm64
