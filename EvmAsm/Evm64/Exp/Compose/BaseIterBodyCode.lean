/-
  EvmAsm.Evm64.Exp.Compose.BaseIterBodyCode

  CodeReq decomposition for the base EXP iteration body without loop back.
-/

module

public import EvmAsm.Evm64.Exp.Compose.BaseLengths
public import EvmAsm.Evm64.Exp.AddrNorm

public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- CodeReq decomposition for the 6-instruction `exp_iter_body`: bit-test,
    square JAL, and conditional-multiply branch/call. This body-only handle is
    the direct target for the `exp_iter_body_spec_within` composition; the
    existing `expOneIterCode` adds the loop-back tail at `base + 24`. -/
abbrev expIterBodyCode (base : Word)
    (mulOff : BitVec 21) (skipOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block,
    CodeReq.ofProg (base + 12) (EvmAsm.Evm64.exp_square_block mulOff),
    CodeReq.ofProg (base + 16) (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff)
  ]

theorem expIterBodyCode_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expIterBodyCode base mulOff skipOff) a = some i := by
  unfold expIterBodyCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem expIterBodyCode_square_sub {base : Word}
    {mulOff : BitVec 21} {skipOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 12)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (expIterBodyCode base mulOff skipOff) a = some i := by
  unfold expIterBodyCode
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_bit_test_block_len, exp_square_block_len] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expIterBodyCode_bit_test_square_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

theorem expIterBodyCode_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 16)
      (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff)) a = some i →
      (expIterBodyCode base mulOff skipOff) a = some i := by
  unfold expIterBodyCode
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_bit_test_block_len, exp_cond_mul_block_len] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expIterBodyCode_bit_test_cond_mul_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_square_block_len, exp_cond_mul_block_len] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expIterBodyCode_square_cond_mul_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

theorem expIterBodyCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expIterBodyCode base mulOff skipOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 12)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (expIterBodyCode base mulOff skipOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 16)
      (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff)) a = some i →
      (expIterBodyCode base mulOff skipOff) a = some i) := by
  exact ⟨expIterBodyCode_bit_test_sub, expIterBodyCode_square_sub,
    expIterBodyCode_cond_mul_sub⟩

theorem expIterBodyCode_eq_ofProg (base : Word)
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    expIterBodyCode base mulOff skipOff =
      CodeReq.ofProg base (EvmAsm.Evm64.exp_iter_body mulOff skipOff) := by
  unfold expIterBodyCode
  unfold EvmAsm.Evm64.exp_iter_body
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  symm
  rw [CodeReq.ofProg_append]
  have h12 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_bit_test_block).length) = base + 12 := by
    rw [EvmAsm.Evm64.exp_bit_test_block_length]
    rfl
  rw [h12]
  rw [CodeReq.ofProg_append]
  have h16 :
      (base + 12 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_square_block mulOff).length) = base + 16 := by
    rw [EvmAsm.Evm64.exp_square_block_length]
    bv_addr
  rw [h16]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil]
  rw [CodeReq.union_empty_right]

end EvmAsm.Evm64.Exp.Compose
