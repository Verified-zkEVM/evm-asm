/-
  EvmAsm.Evm64.Exp.Compose.Base

  Shared composition infrastructure for EXP: `expCode` (the union of all
  sub-block `CodeReq`s), subsumption helpers tying sub-block codes back to
  `expCode`, and shared length lemmas.

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c). Concrete
  definitions will be added in the loop-composition slice (evm-asm-w5mk).
-/

import EvmAsm.Evm64.Exp.LimbSpec
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

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

/-- First EXP composition code skeleton: the verified boundary blocks around
    the loop. The loop body and callable-multiply blocks will extend this
    union as their composed specs land. -/
abbrev expBoundaryCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_prologue,
    CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue
  ]

theorem expBoundaryCode_prologue_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (expBoundaryCode base) a = some i := by
  unfold expBoundaryCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem expBoundaryCode_epilogue_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue) a = some i →
      (expBoundaryCode base) a = some i := by
  unfold expBoundaryCode
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_prologue_len, exp_epilogue_len] at hk1 hk2
      bv_omega))
  exact CodeReq.union_mono_left

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
      bv_omega))
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
      bv_omega))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_square_block_len, exp_cond_mul_block_len] at hk1 hk2
      bv_omega))
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
      bv_omega))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_square_block_len, exp_loop_back_len] at hk1 hk2
      bv_omega))
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_cond_mul_block_len, exp_loop_back_len] at hk1 hk2
      bv_omega))
  exact CodeReq.union_mono_left

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
    (by bv_omega)
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
    (by bv_omega)
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
    (by bv_omega)
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
    (by bv_omega)
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

end EvmAsm.Evm64.Exp.Compose
