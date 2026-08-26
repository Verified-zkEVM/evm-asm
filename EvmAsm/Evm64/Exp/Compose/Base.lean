/-
  EvmAsm.Evm64.Exp.Compose.Base

  Shared composition infrastructure for EXP: `expCode` (the union of all
  sub-block `CodeReq`s), subsumption helpers tying sub-block codes back to
  `expCode`, and shared length lemmas.

  GH #92 composition work lands here and in sibling `Compose` modules.  This
  file keeps the shared layout, byte-offset, and boundary/loop code facts small
  enough for downstream top-code and semantic slices to import directly.
-/

module

public import EvmAsm.Evm64.Stack
public import EvmAsm.Evm64.Exp.CondMulCall
public import EvmAsm.Evm64.Exp.LimbSpec
public import EvmAsm.Evm64.Exp.Compose.BaseBoundary
public import EvmAsm.Evm64.Exp.Compose.BaseIterBodyCode
public import EvmAsm.Evm64.Exp.Compose.BaseSquaringCallCode

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64 (CodeReq Program cpsTripleWithin cpsTripleWithin_extend_code
  cpsTripleWithin_frameR cpsTripleWithin_seq cpsTripleWithin_weaken seq
  signExtend12)

/-- CodeReq decomposition for one EXP loop iteration. This mirrors
    `exp_loop`: bit-test (3 instructions), square call (1), conditional
    multiply branch/call (2), and loop-back (2). -/
abbrev expOneIterCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block,
    CodeReq.ofProg (base + 12) (EvmAsm.Evm64.exp_square_block mulOff),
    CodeReq.ofProg (base + 16) (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff),
    CodeReq.ofProg (base + 24) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expOneIterCode_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i := by
  unfold expOneIterCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem expOneIterCode_square_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 12)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i := by
  unfold expOneIterCode
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_bit_test_block_len, exp_square_block_len] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expIterBodyCode_bit_test_square_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

theorem expOneIterCode_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 16)
      (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff)) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i := by
  unfold expOneIterCode
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

theorem expOneIterCode_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i := by
  unfold expOneIterCode
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_bit_test_block_len, exp_loop_back_len] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expOneIterCode_bit_test_loop_back_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_square_block_len, exp_loop_back_len] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expOneIterCode_square_loop_back_disjoint_addr
        base hk1 hk2))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_cond_mul_block_len, exp_loop_back_len] at hk1 hk2
      exact EvmAsm.Evm64.Exp.AddrNorm.expOneIterCode_cond_mul_loop_back_disjoint_addr
        base hk1 hk2))
  exact CodeReq.union_mono_left

theorem expOneIterCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 12)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 16)
      (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff)) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expOneIterCode base mulOff skipOff backOff) a = some i) := by
  exact ⟨expOneIterCode_bit_test_sub, expOneIterCode_square_sub,
    expOneIterCode_cond_mul_sub, expOneIterCode_loop_back_sub⟩

/-- The concrete `CodeReq` for one full `exp_loop` program. -/
abbrev expLoopCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.ofProg base (EvmAsm.Evm64.exp_loop mulOff skipOff backOff)

theorem expLoopCode_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i := by
  unfold expLoopCode
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_loop mulOff skipOff backOff)
    EvmAsm.Evm64.exp_bit_test_block 0
    (EvmAsm.Evm64.Exp.AddrNorm.expProgramStartAddr base)
    (by
      unfold EvmAsm.Evm64.exp_loop EvmAsm.Evm64.exp_iter_body
      unfold EvmAsm.Evm64.exp_bit_test_block EvmAsm.Evm64.exp_square_block
      unfold EvmAsm.Evm64.exp_cond_mul_block EvmAsm.Evm64.exp_loop_back
      unfold EvmAsm.Rv64.ANDI EvmAsm.Rv64.SRLI EvmAsm.Rv64.ADDI
      unfold EvmAsm.Rv64.JAL EvmAsm.Rv64.BEQ
      rfl)
    (by
      simp only [exp_loop_len, exp_bit_test_block_len]
      omega)
    (by
      simp only [exp_loop_len]
      norm_num)

theorem expLoopCode_square_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 12)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i := by
  unfold expLoopCode
  exact CodeReq.ofProg_mono_sub base (base + 12)
    (EvmAsm.Evm64.exp_loop mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_square_block mulOff) 3
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopSquareProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_loop EvmAsm.Evm64.exp_iter_body
      unfold EvmAsm.Evm64.exp_bit_test_block EvmAsm.Evm64.exp_square_block
      unfold EvmAsm.Evm64.exp_cond_mul_block EvmAsm.Evm64.exp_loop_back
      unfold EvmAsm.Rv64.ANDI EvmAsm.Rv64.SRLI EvmAsm.Rv64.ADDI
      unfold EvmAsm.Rv64.JAL EvmAsm.Rv64.BEQ
      rfl)
    (by
      simp only [exp_loop_len, exp_square_block_len]
      omega)
    (by
      simp only [exp_loop_len]
      norm_num)

theorem expLoopCode_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 16)
      (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff)) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i := by
  unfold expLoopCode
  exact CodeReq.ofProg_mono_sub base (base + 16)
    (EvmAsm.Evm64.exp_loop mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff) 4
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopCondMulProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_loop EvmAsm.Evm64.exp_iter_body
      unfold EvmAsm.Evm64.exp_bit_test_block EvmAsm.Evm64.exp_square_block
      unfold EvmAsm.Evm64.exp_cond_mul_block EvmAsm.Evm64.exp_loop_back
      unfold EvmAsm.Rv64.ANDI EvmAsm.Rv64.SRLI EvmAsm.Rv64.ADDI
      unfold EvmAsm.Rv64.JAL EvmAsm.Rv64.BEQ
      rfl)
    (by
      simp only [exp_loop_len, exp_cond_mul_block_len]
      omega)
    (by
      simp only [exp_loop_len]
      norm_num)

theorem expLoopCode_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 24)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i := by
  unfold expLoopCode
  exact CodeReq.ofProg_mono_sub base (base + 24)
    (EvmAsm.Evm64.exp_loop mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 6
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopBackProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_loop EvmAsm.Evm64.exp_iter_body
      unfold EvmAsm.Evm64.exp_bit_test_block EvmAsm.Evm64.exp_square_block
      unfold EvmAsm.Evm64.exp_cond_mul_block EvmAsm.Evm64.exp_loop_back
      unfold EvmAsm.Rv64.ANDI EvmAsm.Rv64.SRLI EvmAsm.Rv64.ADDI
      unfold EvmAsm.Rv64.JAL EvmAsm.Rv64.BEQ
      rfl)
    (by
      simp only [exp_loop_len, exp_loop_back_len]
      omega)
    (by
      simp only [exp_loop_len]
      norm_num)

theorem expLoopCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 12)
      (EvmAsm.Evm64.exp_square_block mulOff)) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 16)
      (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff)) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i) := by
  exact ⟨expLoopCode_bit_test_sub, expLoopCode_square_sub,
    expLoopCode_cond_mul_sub, expLoopCode_loop_back_sub⟩

theorem expOneIterCode_loop_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expOneIterCode base mulOff skipOff backOff) a = some i →
      (expLoopCode base mulOff skipOff backOff) a = some i := by
  unfold expOneIterCode
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil]
  intro a i h
  unfold CodeReq.union at h
  split at h
  · cases h
    exact expLoopCode_bit_test_sub a _ (by assumption)
  · rename_i hBit
    split at h
    · cases h
      exact expLoopCode_square_sub a _ (by assumption)
    · rename_i hSquare
      split at h
      · cases h
        exact expLoopCode_cond_mul_sub a _ (by assumption)
      · rename_i hCond
        split at h
        · cases h
          exact expLoopCode_loop_back_sub a _ (by assumption)
        · simp_all [CodeReq.empty]

theorem expLoopCode_eq_oneIterCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expLoopCode base mulOff skipOff backOff =
      expOneIterCode base mulOff skipOff backOff := by
  unfold expLoopCode expOneIterCode
  unfold EvmAsm.Evm64.exp_loop
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h24 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_iter_body mulOff skipOff).length) = base + 24 := by
    rw [EvmAsm.Evm64.exp_iter_body_length]
    rfl
  rw [h24]
  unfold EvmAsm.Evm64.exp_iter_body
  simp only [EvmAsm.Rv64.seq]
  unfold Program
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
  rw [CodeReq.union_assoc]
  rw [CodeReq.union_assoc]

/-- CodeReq decomposition for one full EXP square-and-multiply iteration,
    including both MUL call blocks and the trailing loop back-edge. -/
abbrev expIterBodyFullCode (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block,
    exp_squaring_call_block_code (base + 12) mulOff,
    EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code (base + 116) mulOff skipOff,
    CodeReq.ofProg (base + 224) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expIterBodyFullCode_eq_ofProg (base : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expIterBodyFullCode base mulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff) := by
  unfold expIterBodyFullCode
  unfold EvmAsm.Evm64.exp_iter_body_full
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h12 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_bit_test_block).length) = base + 12 := by
    rw [EvmAsm.Evm64.exp_bit_test_block_length]
    rfl
  rw [h12]
  rw [CodeReq.ofProg_append]
  have h116 :
      (base + 12 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_squaring_call_block mulOff).length) =
        base + 116 := by
    rw [EvmAsm.Evm64.exp_squaring_call_block_length]
    bv_addr
  rw [h116]
  rw [CodeReq.ofProg_append]
  have h224 :
      (base + 116 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block mulOff skipOff).length) =
        base + 224 := by
    rw [EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_length]
    bv_addr
  rw [h224]
  rw [← exp_squaring_call_block_code_eq_ofProg (base + 12) mulOff]
  rw [← EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_eq_ofProg
    (base + 116) mulOff skipOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem expIterBodyFullCode_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i := by
  unfold expIterBodyFullCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem expIterBodyFullCode_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 12) mulOff) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullCode_eq_ofProg, exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 12)
    (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_squaring_call_block mulOff) 3
    (EvmAsm.Evm64.Exp.AddrNorm.expLoopSquareProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_len, exp_squaring_call_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_len]
      norm_num)

theorem expIterBodyFullCode_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code
      (base + 116) mulOff skipOff) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullCode_eq_ofProg,
    EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 116)
    (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block mulOff skipOff) 29
    (EvmAsm.Evm64.Exp.AddrNorm.expFullIterCondMulProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_len, exp_cond_mul_call_with_skip_block_len]
      omega)
    (by
      simp only [exp_iter_body_full_len]
      norm_num)

theorem expIterBodyFullCode_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 224)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 224)
    (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 56
    (EvmAsm.Evm64.Exp.AddrNorm.expFullIterLoopBackProgramAddr base)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp only [exp_iter_body_full_len, exp_loop_back_len]
      omega)
    (by
      simp only [exp_iter_body_full_len]
      norm_num)

theorem expIterBodyFullCode_block_subs {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (exp_squaring_call_block_code (base + 12) mulOff) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code
      (base + 116) mulOff skipOff) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 224)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullCode base mulOff skipOff backOff) a = some i) := by
  exact ⟨expIterBodyFullCode_bit_test_sub, expIterBodyFullCode_squaring_sub,
    expIterBodyFullCode_cond_mul_sub, expIterBodyFullCode_loop_back_sub⟩

end EvmAsm.Evm64.Exp.Compose
