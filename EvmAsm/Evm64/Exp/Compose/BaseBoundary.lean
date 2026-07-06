/-
  EvmAsm.Evm64.Exp.Compose.BaseBoundary

  Boundary mini-program CodeReq decomposition and composed spec for EXP.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.Exp.LimbSpec
import EvmAsm.Evm64.Exp.Compose.BaseLengths
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

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
      exact EvmAsm.Evm64.Exp.AddrNorm.expBoundaryCode_prologue_epilogue_disjoint_addr
        base hk1 hk2))
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
  unfold expBoundaryProgram EvmAsm.Rv64.seq
  rw [EvmAsm.Rv64.Program.length_append, exp_prologue_len, exp_epilogue_len]

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
  rw [EvmAsm.Evm64.Exp.AddrNorm.expBoundaryProgramEpilogueAddr base]
  rw [← CodeReq.ofProg_append]
  rfl

theorem expBoundaryProgramCode_prologue_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (expBoundaryProgramCode base) a = some i := by
  unfold expBoundaryProgramCode
  exact CodeReq.ofProg_mono_sub base base expBoundaryProgram EvmAsm.Evm64.exp_prologue 0
    (EvmAsm.Evm64.Exp.AddrNorm.expProgramStartAddr base)
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
    (EvmAsm.Evm64.Exp.AddrNorm.expTopPointerAdvanceProgramAddr base)
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
  rw [EvmAsm.Evm64.Exp.AddrNorm.expBoundaryEpilogueExitPc] at hEpi
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

end EvmAsm.Evm64.Exp.Compose
