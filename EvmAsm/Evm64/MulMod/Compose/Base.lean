/-
  EvmAsm.Evm64.MulMod.Compose.Base

  Shared composition infrastructure for MULMOD: `evm_mulmod_program_code`
  (the `CodeReq.ofProg` handle for the assembled top-level `evm_mulmod`) and
  sub-block subsumption/lift helpers used by the later stack-spec composition.
-/

import EvmAsm.Evm64.MulMod.LimbSpec
import EvmAsm.Evm64.MulMod.AddrNorm

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- `CodeReq.ofProg` handle for the assembled top-level `evm_mulmod` program. -/
abbrev evm_mulmod_program_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod

local macro "evm_mulmod_slice_rfl" : tactic =>
  `(tactic|
    first
      | rfl
      | (unfold evm_mulmod evm_mulmod_nonzero_or_zero_prefix
            evm_mulmod_reduce_zero_path evm_mulmod_epilogue
            evm_mulmod_zero_path_skip_nonzero evm_mulmod_product_layout
            evm_mulmod_product_zero LD OR' BNE SD ADDI JAL single seq
         rfl))

/-- The zero/nonzero modulus prefix block (8 instrs at offset 0) is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_nonzero_or_zero_prefix_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg base evm_mulmod_nonzero_or_zero_prefix) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base base evm_mulmod
    evm_mulmod_nonzero_or_zero_prefix 0 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_nonzero_or_zero_prefix_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The zero-result path block (4 instrs at offset 32) is subsumed by the
    top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_reduce_zero_path_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 32) evm_mulmod_reduce_zero_path) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 32) evm_mulmod
    evm_mulmod_reduce_zero_path 8 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_reduce_zero_path_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The zero-path epilogue block (1 instr at offset 48) is subsumed by the
    top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_epilogue_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 48) evm_mulmod_epilogue) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 48) evm_mulmod
    evm_mulmod_epilogue 12 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_epilogue_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The jump over the nonzero path (1 instr at offset 52) is subsumed by the
    top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_zero_path_skip_nonzero_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 52) evm_mulmod_zero_path_skip_nonzero) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 52) evm_mulmod
    evm_mulmod_zero_path_skip_nonzero 13 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_zero_path_skip_nonzero_length]; decide
  · rw [evm_mulmod_length]; decide

/-- The first nonzero-path block, which zeroes the product window at offset 56,
    is subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_zero_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 56) evm_mulmod_product_zero) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 56) evm_mulmod
    evm_mulmod_product_zero 14 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length, evm_mulmod_product_zero_length]; decide
  · rw [evm_mulmod_length]; decide

/-- Prefix branch spec lifted from its sub-block `CodeReq.ofProg` handle onto
    `evm_mulmod_program_code`. -/
theorem evm_mulmod_nonzero_or_zero_prefix_evm_mulmod_spec_within
    (sp v5Old v6Old n0 n1 n2 n3 : Word) (base : Word) :
    let orAll := n0 ||| n1 ||| n2 ||| n3
    cpsBranchWithin 8 base (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6Old) ** (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3))
      ((base + 28) + signExtend13 (28 : BitVec 13))
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll ≠ 0⌝)
      (base + 32)
        ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ orAll) ** (.x5 ↦ᵣ n3) ** (.x0 ↦ᵣ 0) **
         ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ n0) **
         ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ n1) **
         ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ n2) **
         ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ n3) **
         ⌜orAll = 0⌝) := by
  intro orAll
  exact cpsBranchWithin_extend_code
    (h := evm_mulmod_nonzero_or_zero_prefix_spec_within sp v5Old v6Old n0 n1 n2 n3 base)
    (hmono := evm_mulmod_program_code_nonzero_or_zero_prefix_sub base)

/-- Zero-result path spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_reduce_zero_path_evm_mulmod_spec_within
    (sp m0 m1 m2 m3 : Word) (base : Word) :
    cpsTripleWithin 4 (base + 32) ((base + 32) + 16) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ m3))
      ((.x12 ↦ᵣ sp) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ (0 : Word))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_reduce_zero_path_ofProg_spec_within sp m0 m1 m2 m3 (base + 32))
    (hmono := evm_mulmod_program_code_reduce_zero_path_sub base)

/-- Zero-path epilogue spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_epilogue_evm_mulmod_spec_within
    (sp : Word) (base : Word) :
    cpsTripleWithin 1 (base + 48) ((base + 48) + 4) (evm_mulmod_program_code base)
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_epilogue_spec_within sp (base + 48))
    (hmono := evm_mulmod_program_code_epilogue_sub base)

/-- Zero-path skip spec lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_zero_path_skip_nonzero_evm_mulmod_spec_within
    (base : Word) :
    cpsTripleWithin 1 (base + 52) ((base + 52) + signExtend21 (2100 : BitVec 21))
      (evm_mulmod_program_code base)
      empAssertion
      empAssertion :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_zero_path_skip_nonzero_spec_within (base + 52))
    (hmono := evm_mulmod_program_code_zero_path_skip_nonzero_sub base)


/-- Product-window zeroing spec lifted onto `evm_mulmod_program_code` at the
    start of the nonzero path. -/
theorem evm_mulmod_product_zero_evm_mulmod_spec_within (sp : Word) (base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word) :
    cpsTripleWithin 8 (base + 56) ((base + 56) + 32) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
       ((sp + 56) ↦ₘ b3) **
       ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) ** ((sp + 80) ↦ₘ n2) **
       ((sp + 88) ↦ₘ n3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ p0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ p1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ p2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ p3) **
       ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ p4) **
       ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ p7))
      (evmMulModProductZeroPost sp a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_zero_spec_within sp (base + 56)
      a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 p0 p1 p2 p3 p4 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_zero_sub base)

end EvmAsm.Evm64.MulMod.Compose
