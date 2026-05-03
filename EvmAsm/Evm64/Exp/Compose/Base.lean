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

theorem expBoundaryCode_block_subs {base : Word} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (expBoundaryCode base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue) a = some i →
      (expBoundaryCode base) a = some i) := by
  exact ⟨expBoundaryCode_prologue_sub, expBoundaryCode_epilogue_sub⟩

/-- Concrete prologue/epilogue boundary mini-program used by early EXP
    composition slices before the full 256-iteration loop is wired. -/
abbrev expBoundaryProgram : Program :=
  EvmAsm.Evm64.exp_prologue ;; EvmAsm.Evm64.exp_epilogue

theorem expBoundaryProgram_len : expBoundaryProgram.length = 15 := by
  native_decide

theorem expBoundaryProgram_byte_len : 4 * expBoundaryProgram.length = 60 := by
  rw [expBoundaryProgram_len]

/-- Concrete `CodeReq.ofProg` handle for `expBoundaryProgram`. -/
abbrev expBoundaryProgramCode (base : Word) : CodeReq :=
  CodeReq.ofProg base expBoundaryProgram

/-- The structural boundary-code union is exactly the executable boundary
    program's `CodeReq.ofProg` handle. -/
theorem expBoundaryCode_eq_programCode (base : Word) :
    expBoundaryCode base = expBoundaryProgramCode base := by
  unfold expBoundaryCode expBoundaryProgramCode expBoundaryProgram
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil,
    CodeReq.union_empty_right, EvmAsm.Rv64.seq]
  rw [show (base + 24 : Word) =
      base + BitVec.ofNat 64 (4 * EvmAsm.Evm64.exp_prologue.length) by
    rw [exp_prologue_len]
    bv_omega]
  rw [← CodeReq.ofProg_append]
  rfl

theorem expBoundaryProgramCode_prologue_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (expBoundaryProgramCode base) a = some i := by
  unfold expBoundaryProgramCode
  exact CodeReq.ofProg_mono_sub base base expBoundaryProgram EvmAsm.Evm64.exp_prologue 0
    (by bv_omega)
    (by unfold expBoundaryProgram; simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [expBoundaryProgram_len, exp_prologue_len]
      norm_num)
    (by
      rw [expBoundaryProgram_len]
      norm_num)

theorem expBoundaryProgramCode_epilogue_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue) a = some i →
      (expBoundaryProgramCode base) a = some i := by
  unfold expBoundaryProgramCode
  exact CodeReq.ofProg_mono_sub base (base + 24)
    expBoundaryProgram EvmAsm.Evm64.exp_epilogue 6
    (by bv_omega)
    (by unfold expBoundaryProgram; simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [expBoundaryProgram_len, exp_epilogue_len])
    (by
      rw [expBoundaryProgram_len]
      norm_num)

theorem expBoundaryProgramCode_block_subs {base : Word} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (expBoundaryProgramCode base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue) a = some i →
      (expBoundaryProgramCode base) a = some i) := by
  exact ⟨expBoundaryProgramCode_prologue_sub, expBoundaryProgramCode_epilogue_sub⟩

theorem expBoundaryProgramCode_program_sub {base : Word} :
    ∀ a i, (expBoundaryCode base) a = some i →
      (expBoundaryProgramCode base) a = some i := by
  unfold expBoundaryCode
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil]
  intro a i h
  unfold CodeReq.union at h
  split at h
  · cases h
    exact expBoundaryProgramCode_prologue_sub a _ (by assumption)
  · rename_i hPrologue
    split at h
    · cases h
      exact expBoundaryProgramCode_epilogue_sub a _ (by assumption)
    · simp_all [CodeReq.empty]

/-- Composed spec for the current EXP boundary mini-program: the EXP-specific
    prologue initializes the accumulator to one, and the EXP-specific epilogue
    writes that accumulator back to the EVM stack result slot. -/
theorem expBoundaryProgram_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryProgramCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       evmWordIs (evmSp + 32) (expResultWord
        ((0 : Word) + signExtend12 (1 : BitVec 12))
        (0 : Word) (0 : Word) (0 : Word))) := by
  have hPro :=
    EvmAsm.Evm64.exp_prologue_ofProg_spec_within
      sp cOld tOld m0 m1 m2 m3 base
  have hEpi :=
    EvmAsm.Evm64.exp_epilogue_word_spec_within sp evmSp
      ((0 : Word) + signExtend12 (1 : BitVec 12))
      ((0 : Word) + signExtend12 (1 : BitVec 12))
      (0 : Word) (0 : Word) (0 : Word) d0 d1 d2 d3 (base + 24)
  rw [show (base + 24 : Word) + 36 = base + 60 from by bv_omega] at hEpi
  have hProFramed : cpsTripleWithin 6 base (base + 24)
      (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ evmSp) **
         ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
         ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
         ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
         ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
        (by pcFree) hPro)
  have hEpiFramed : cpsTripleWithin 9 (base + 24) (base + 60)
      (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       evmWordIs (evmSp + 32) (expResultWord
        ((0 : Word) + signExtend12 (1 : BitVec 12))
        (0 : Word) (0 : Word) (0 : Word))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) **
         (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))))
        (by pcFree) hEpi)
  have hd : CodeReq.Disjoint
      (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue)
      (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue) :=
    CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_prologue_len, exp_epilogue_len] at hk1 hk2
      bv_omega)
  have hSeq := cpsTripleWithin_seq hd hProFramed hEpiFramed
  have hUnionSub :
      ∀ a i,
        ((CodeReq.ofProg base EvmAsm.Evm64.exp_prologue).union
          (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue)) a = some i →
        (expBoundaryProgramCode base) a = some i := by
    intro a i h
    unfold CodeReq.union at h
    split at h
    · cases h
      exact expBoundaryProgramCode_prologue_sub a _ (by assumption)
    · exact expBoundaryProgramCode_epilogue_sub a i h
  simpa only [Nat.reduceAdd] using
    cpsTripleWithin_extend_code hUnionSub hSeq

/-- Composed spec for the current EXP boundary mini-program over the
    structural boundary `CodeReq` union. -/
theorem expBoundaryCode_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 15 base (base + 60) (expBoundaryCode base)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ
        ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ (0 : Word)) **
       evmWordIs (evmSp + 32) (expResultWord
        ((0 : Word) + signExtend12 (1 : BitVec 12))
        (0 : Word) (0 : Word) (0 : Word))) := by
  rw [expBoundaryCode_eq_programCode]
  exact expBoundaryProgram_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 d0 d1 d2 d3 base

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

theorem exp_loop_back_loop_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base target : Word)
    (htarget : ((base + 24) + 4 : Word) + signExtend13 backOff = target) :
    let cNew := c + signExtend12 ((-1 : BitVec 12))
    cpsBranchWithin 2 (base + 24)
      (expLoopCode base mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew ≠ 0⌝)
      (base + 32) ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 24) target htarget
  have hnext : ((base + 24 : Word) + 8) = base + 32 := by bv_omega
  rw [hnext] at h
  exact cpsBranchWithin_extend_code (h := h) (hmono := expLoopCode_loop_back_sub)

theorem exp_bit_test_loop_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 3 base (base + 12) (expLoopCode base mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e >>> (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e &&& signExtend12 (1 : BitVec 12)))) := by
  have h := EvmAsm.Evm64.exp_bit_test_block_spec_within e c v10 base
  exact cpsTripleWithin_extend_code (h := h) (hmono := expLoopCode_bit_test_sub)

theorem exp_square_loop_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (vOld : Word) (base mulTarget : Word)
    (hmul : ((base + 12) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 1 (base + 12) mulTarget
      (expLoopCode base mulOff skipOff backOff)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 16)) := by
  have h := EvmAsm.Evm64.exp_square_block_spec_within mulOff vOld (base + 12)
  rw [hmul] at h
  have hret : ((base + 12 : Word) + 4) = base + 16 := by bv_omega
  rw [hret] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := expLoopCode_square_sub)

theorem exp_cond_mul_loop_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v10 vOld : Word) (base skipTarget mulTarget : Word)
    (hskip : ((base + 16) + signExtend13 skipOff : Word) = skipTarget)
    (hmul : (((base + 16) + 4) + signExtend21 mulOff : Word) = mulTarget) :
    cpsBranchWithin 2 (base + 16) (expLoopCode base mulOff skipOff backOff)
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vOld))
      skipTarget
        ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vOld) **
          ⌜v10 = 0⌝)
      mulTarget
        ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (base + 24)) **
          ⌜v10 ≠ 0⌝) := by
  have h := EvmAsm.Evm64.exp_cond_mul_block_spec_within
    mulOff skipOff v10 vOld (base + 16)
  rw [hskip, hmul] at h
  have hret : ((base + 16 : Word) + 8) = base + 24 := by bv_omega
  rw [hret] at h
  exact cpsBranchWithin_extend_code (h := h) (hmono := expLoopCode_cond_mul_sub)

end EvmAsm.Evm64.Exp.Compose
