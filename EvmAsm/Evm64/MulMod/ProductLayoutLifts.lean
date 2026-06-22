/-
  EvmAsm.Evm64.MulMod.ProductLayoutLifts

  Reusable lifts of product-layout sub-block specs onto the local
  `evm_mulmod_product_layout_code` CodeReq.  These are the same-CodeReq
  building blocks for the full product-layout composition proof.
-/

import EvmAsm.Evm64.MulMod.AddPartialTable

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

local macro "evm_mulmod_product_layout_slice_rfl" : tactic =>
  `(tactic|
    first
      | rfl
      | (unfold evm_mulmod_product_layout evm_mulmod_product_zero
            evm_mulmod_product_add_partial evm_mulmod_product_propagate_carry
            LD SD ADD SLTU OR' MUL MULHU single seq
         rfl))

/-- Product-window zeroing is the first block of `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_zero_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_zero_code base) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_zero_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base base evm_mulmod_product_layout
    evm_mulmod_product_zero 0 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length, evm_mulmod_product_zero_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Product-window zeroing lifted onto the local product-layout code requirement. -/
abbrev evm_mulmod_product_layout_zero_spec_within :=
  fun sp base a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 p0 p1 p2 p3 p4 p5 p6 p7 =>
    cpsTripleWithin_extend_code
      (h := evm_mulmod_product_zero_spec_within sp base
        a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 p0 p1 p2 p3 p4 p5 p6 p7)
      (hmono := evm_mulmod_product_layout_zero_code_sub base)


/-- Core+finish code for layout call 00 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call00_core_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 32)
        (0 : BitVec 12) (32 : BitVec 12) (96 : BitVec 12) (104 : BitVec 12)) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 32) evm_mulmod_product_layout _ 8 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Carry-propagation code for layout call 00 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call00_carry_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_propagate_carry_code (base + 92) [112, 120, 128, 136, 144, 152]) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_propagate_carry_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 92) evm_mulmod_product_layout _ 23 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Layout call 00 split code is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call00_code_sub (base : Word) :
    ∀ a i, ((evm_mulmod_product_add_partial_core_finish_code (base + 32)
        (0 : BitVec 12) (32 : BitVec 12) (96 : BitVec 12) (104 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code ((base + 32) + 60) [112, 120, 128, 136, 144, 152])) a = some i →
      (evm_mulmod_product_layout_code base) a = some i :=
  CodeReq.union_sub (evm_mulmod_product_layout_call00_core_code_sub base)
    (by
      intro a i h
      apply evm_mulmod_product_layout_call00_carry_code_sub base
      rw [show (base + 32) + 60 = base + 92 by bv_omega] at h
      exact h)

/-- Layout call 00 spec lifted onto the local product-layout code requirement. -/
abbrev evm_mulmod_product_layout_call00_spec_within :=
  fun sp base a b lo hi p2 p3 p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old =>
    cpsTripleWithin_extend_code
      (h := evm_mulmod_product_add_partial_layout_call00_spec_within sp (base + 32) a b lo hi p2 p3 p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (hmono := evm_mulmod_product_layout_call00_code_sub base)

/-- Core+finish code for layout call 01 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call01_core_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 188)
        (8 : BitVec 12) (32 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12)) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 188) evm_mulmod_product_layout _ 47 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Carry-propagation code for layout call 01 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call01_carry_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_propagate_carry_code (base + 248) [120, 128, 136, 144, 152]) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_propagate_carry_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 248) evm_mulmod_product_layout _ 62 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Layout call 01 split code is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call01_code_sub (base : Word) :
    ∀ a i, ((evm_mulmod_product_add_partial_core_finish_code (base + 188)
        (8 : BitVec 12) (32 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code ((base + 188) + 60) [120, 128, 136, 144, 152])) a = some i →
      (evm_mulmod_product_layout_code base) a = some i :=
  CodeReq.union_sub (evm_mulmod_product_layout_call01_core_code_sub base)
    (by
      intro a i h
      apply evm_mulmod_product_layout_call01_carry_code_sub base
      rw [show (base + 188) + 60 = base + 248 by bv_omega] at h
      exact h)

/-- Layout call 01 spec lifted onto the local product-layout code requirement. -/
abbrev evm_mulmod_product_layout_call01_spec_within :=
  fun sp base a b lo hi p3 p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old =>
    cpsTripleWithin_extend_code
      (h := evm_mulmod_product_add_partial_layout_call01_spec_within sp (base + 188) a b lo hi p3 p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (hmono := evm_mulmod_product_layout_call01_code_sub base)

/-- Core+finish code for layout call 02 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call02_core_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 328)
        (0 : BitVec 12) (40 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12)) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 328) evm_mulmod_product_layout _ 82 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Carry-propagation code for layout call 02 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call02_carry_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_propagate_carry_code (base + 388) [120, 128, 136, 144, 152]) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_propagate_carry_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 388) evm_mulmod_product_layout _ 97 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Layout call 02 split code is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call02_code_sub (base : Word) :
    ∀ a i, ((evm_mulmod_product_add_partial_core_finish_code (base + 328)
        (0 : BitVec 12) (40 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code ((base + 328) + 60) [120, 128, 136, 144, 152])) a = some i →
      (evm_mulmod_product_layout_code base) a = some i :=
  CodeReq.union_sub (evm_mulmod_product_layout_call02_core_code_sub base)
    (by
      intro a i h
      apply evm_mulmod_product_layout_call02_carry_code_sub base
      rw [show (base + 328) + 60 = base + 388 by bv_omega] at h
      exact h)

/-- Layout call 02 spec lifted onto the local product-layout code requirement. -/
abbrev evm_mulmod_product_layout_call02_spec_within :=
  fun sp base a b lo hi p3 p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old =>
    cpsTripleWithin_extend_code
      (h := evm_mulmod_product_add_partial_layout_call02_spec_within sp (base + 328) a b lo hi p3 p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (hmono := evm_mulmod_product_layout_call02_code_sub base)

/-- Core+finish code for layout call 03 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call03_core_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 468)
        (16 : BitVec 12) (32 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12)) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 468) evm_mulmod_product_layout _ 117 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Carry-propagation code for layout call 03 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call03_carry_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_propagate_carry_code (base + 528) [128, 136, 144, 152]) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_propagate_carry_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 528) evm_mulmod_product_layout _ 132 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Layout call 03 split code is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call03_code_sub (base : Word) :
    ∀ a i, ((evm_mulmod_product_add_partial_core_finish_code (base + 468)
        (16 : BitVec 12) (32 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code ((base + 468) + 60) [128, 136, 144, 152])) a = some i →
      (evm_mulmod_product_layout_code base) a = some i :=
  CodeReq.union_sub (evm_mulmod_product_layout_call03_core_code_sub base)
    (by
      intro a i h
      apply evm_mulmod_product_layout_call03_carry_code_sub base
      rw [show (base + 468) + 60 = base + 528 by bv_omega] at h
      exact h)

/-- Layout call 03 spec lifted onto the local product-layout code requirement. -/
abbrev evm_mulmod_product_layout_call03_spec_within :=
  fun sp base a b lo hi p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old =>
    cpsTripleWithin_extend_code
      (h := evm_mulmod_product_add_partial_layout_call03_spec_within sp (base + 468) a b lo hi p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (hmono := evm_mulmod_product_layout_call03_code_sub base)

/-- Core+finish code for layout call 04 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call04_core_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 592)
        (8 : BitVec 12) (40 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12)) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 592) evm_mulmod_product_layout _ 148 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Carry-propagation code for layout call 04 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call04_carry_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_propagate_carry_code (base + 652) [128, 136, 144, 152]) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_propagate_carry_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 652) evm_mulmod_product_layout _ 163 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Layout call 04 split code is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call04_code_sub (base : Word) :
    ∀ a i, ((evm_mulmod_product_add_partial_core_finish_code (base + 592)
        (8 : BitVec 12) (40 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code ((base + 592) + 60) [128, 136, 144, 152])) a = some i →
      (evm_mulmod_product_layout_code base) a = some i :=
  CodeReq.union_sub (evm_mulmod_product_layout_call04_core_code_sub base)
    (by
      intro a i h
      apply evm_mulmod_product_layout_call04_carry_code_sub base
      rw [show (base + 592) + 60 = base + 652 by bv_omega] at h
      exact h)

/-- Layout call 04 spec lifted onto the local product-layout code requirement. -/
abbrev evm_mulmod_product_layout_call04_spec_within :=
  fun sp base a b lo hi p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old =>
    cpsTripleWithin_extend_code
      (h := evm_mulmod_product_add_partial_layout_call04_spec_within sp (base + 592) a b lo hi p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (hmono := evm_mulmod_product_layout_call04_code_sub base)

/-- Core+finish code for layout call 05 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call05_core_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 716)
        (0 : BitVec 12) (48 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12)) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 716) evm_mulmod_product_layout _ 179 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Carry-propagation code for layout call 05 is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call05_carry_code_sub (base : Word) :
    ∀ a i, (evm_mulmod_product_propagate_carry_code (base + 776) [128, 136, 144, 152]) a = some i →
      (evm_mulmod_product_layout_code base) a = some i := by
  unfold evm_mulmod_product_propagate_carry_code evm_mulmod_product_layout_code
  refine CodeReq.ofProg_mono_sub base (base + 776) evm_mulmod_product_layout _ 194 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_product_layout_slice_rfl
  · rw [evm_mulmod_product_layout_length]
    decide
  · rw [evm_mulmod_product_layout_length]
    decide

/-- Layout call 05 split code is contained in `evm_mulmod_product_layout`. -/
theorem evm_mulmod_product_layout_call05_code_sub (base : Word) :
    ∀ a i, ((evm_mulmod_product_add_partial_core_finish_code (base + 716)
        (0 : BitVec 12) (48 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12)).union
        (evm_mulmod_product_propagate_carry_code ((base + 716) + 60) [128, 136, 144, 152])) a = some i →
      (evm_mulmod_product_layout_code base) a = some i :=
  CodeReq.union_sub (evm_mulmod_product_layout_call05_core_code_sub base)
    (by
      intro a i h
      apply evm_mulmod_product_layout_call05_carry_code_sub base
      rw [show (base + 716) + 60 = base + 776 by bv_omega] at h
      exact h)

/-- Layout call 05 spec lifted onto the local product-layout code requirement. -/
abbrev evm_mulmod_product_layout_call05_spec_within :=
  fun sp base a b lo hi p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old =>
    cpsTripleWithin_extend_code
      (h := evm_mulmod_product_add_partial_layout_call05_spec_within sp (base + 716) a b lo hi p4 p5 p6 p7 x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (hmono := evm_mulmod_product_layout_call05_code_sub base)

/-- Stack cells in the product-layout prefix that layout call00 does not touch.

    Call00 only reads `a[0]`, `b[0]`, and the product window. The remaining
    input limbs are framed through it for the first prefix composition step. -/
@[irreducible]
def evmMulModProductLayoutCall00Frame (sp : Word) (a b n : EvmWord) : Assertion :=
  ((sp + 8) ↦ₘ a.getLimbN 1) **
  ((sp + 16) ↦ₘ a.getLimbN 2) **
  ((sp + 24) ↦ₘ a.getLimbN 3) **
  ((sp + 40) ↦ₘ b.getLimbN 1) **
  ((sp + 48) ↦ₘ b.getLimbN 2) **
  ((sp + 56) ↦ₘ b.getLimbN 3) **
  ((sp + 64) ↦ₘ n.getLimbN 0) **
  ((sp + 72) ↦ₘ n.getLimbN 1) **
  ((sp + 80) ↦ₘ n.getLimbN 2) **
  ((sp + 88) ↦ₘ n.getLimbN 3)

theorem evmMulModProductLayoutCall00Frame_unfold (sp : Word) (a b n : EvmWord) :
    evmMulModProductLayoutCall00Frame sp a b n =
      (((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) **
       ((sp + 24) ↦ₘ a.getLimbN 3) **
       ((sp + 40) ↦ₘ b.getLimbN 1) **
       ((sp + 48) ↦ₘ b.getLimbN 2) **
       ((sp + 56) ↦ₘ b.getLimbN 3) **
       ((sp + 64) ↦ₘ n.getLimbN 0) **
       ((sp + 72) ↦ₘ n.getLimbN 1) **
       ((sp + 80) ↦ₘ n.getLimbN 2) **
       ((sp + 88) ↦ₘ n.getLimbN 3)) := by
  delta evmMulModProductLayoutCall00Frame; rfl

/-- First product-layout prefix composition: zero the product window, then add
    the `(a[0] * b[0])` partial product. -/
theorem evm_mulmod_product_layout_zero_call00_spec_within
    (sp base : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin (8 + (15 + 24)) base (base + 188) (evm_mulmod_product_layout_code base)
      (evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
       ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
        (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
        (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
      (((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ mulModCarryStepCarry (0 : Word)
          (mulModCarryStepCarry (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModCarryStepCarry (0 : Word)
                  (mulModCarryStepCarry (0 : Word)
                    (mulModAddPartialHiCarry (0 : Word) (0 : Word)
                      (a.getLimbN 0) (b.getLimbN 0)))))))) **
        (.x9 ↦ᵣ mulModCarryStepValue (0 : Word)
          (mulModCarryStepCarry (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModCarryStepCarry (0 : Word)
                  (mulModCarryStepCarry (0 : Word)
                    (mulModAddPartialHiCarry (0 : Word) (0 : Word)
                      (a.getLimbN 0) (b.getLimbN 0)))))))) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ
          mulModCarryStepValue (0 : Word)
            (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ
          mulModCarryStepValue (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)))) **
        ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ
          mulModCarryStepValue (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))))) **
        ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ
          mulModCarryStepValue (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModCarryStepCarry (0 : Word)
                  (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)))))) **
        ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ
          mulModCarryStepValue (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModCarryStepCarry (0 : Word)
                  (mulModCarryStepCarry (0 : Word)
                    (mulModAddPartialHiCarry (0 : Word) (0 : Word)
                      (a.getLimbN 0) (b.getLimbN 0))))))) **
        ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ
          mulModCarryStepValue (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModCarryStepCarry (0 : Word)
                  (mulModCarryStepCarry (0 : Word)
                    (mulModCarryStepCarry (0 : Word)
                      (mulModAddPartialHiCarry (0 : Word) (0 : Word)
                        (a.getLimbN 0) (b.getLimbN 0)))))))) **
        (.x5 ↦ᵣ a.getLimbN 0) **
        (.x6 ↦ᵣ b.getLimbN 0) **
        (.x7 ↦ᵣ mulModAddPartialLoProduct (a.getLimbN 0) (b.getLimbN 0)) **
        (.x8 ↦ᵣ mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 0)) **
        (.x11 ↦ᵣ mulModAddPartialHiValue (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)) **
        (.x13 ↦ᵣ mulModAddPartialHiBaseCarry (0 : Word) (a.getLimbN 0) (b.getLimbN 0)) **
        (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo (0 : Word) (0 : Word)
          (a.getLimbN 0) (b.getLimbN 0)) **
        (sp ↦ₘ a.getLimbN 0) **
        ((sp + 32) ↦ₘ b.getLimbN 0) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ
          mulModAddPartialLoValue (0 : Word) (a.getLimbN 0) (b.getLimbN 0)) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ
          mulModAddPartialHiValue (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))) **
       evmMulModProductLayoutCall00Frame sp a b n) := by
  simp only [evmMulModProductLayoutPre_unfold, evmMulModProductLayoutCall00Frame_unfold]
  have hZero := evm_mulmod_product_layout_zero_spec_within sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (n.getLimbN 0) (n.getLimbN 1) (n.getLimbN 2) (n.getLimbN 3)
    p0 p1 p2 p3 p4 p5 p6 p7
  unfold evmMulModProductZeroPost at hZero
  have hZeroF := cpsTripleWithin_frameR
    (((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
      (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
      (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
    (by pcFree) hZero
  have hCall := evm_mulmod_product_layout_call00_spec_within sp base
    (a.getLimbN 0) (b.getLimbN 0) (0 : Word) (0 : Word)
    (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  unfold evmMulModAddPartialCoreFullPre at hCall
  rw [signExtend12_0, signExtend12_32] at hCall
  rw [show sp + (0 : Word) = sp by bv_omega] at hCall
  have hCallF := cpsTripleWithin_frameR
    ((((sp + 8) ↦ₘ a.getLimbN 1) **
      ((sp + 16) ↦ₘ a.getLimbN 2) **
      ((sp + 24) ↦ₘ a.getLimbN 3) **
      ((sp + 40) ↦ₘ b.getLimbN 1) **
      ((sp + 48) ↦ₘ b.getLimbN 2) **
      ((sp + 56) ↦ₘ b.getLimbN 3) **
      ((sp + 64) ↦ₘ n.getLimbN 0) **
      ((sp + 72) ↦ₘ n.getLimbN 1) **
      ((sp + 80) ↦ₘ n.getLimbN 2) **
      ((sp + 88) ↦ₘ n.getLimbN 3)))
    (by pcFree) hCall
  have hComp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hZeroF hCallF
  rw [show base + 32 + 60 + 96 = base + 188 by bv_omega] at hComp
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    hComp


/-- Product offset 96 after layout call00. -/
def mulModProductLayoutCall00P96 (a b : EvmWord) : Word :=
  mulModAddPartialLoValue (0 : Word) (a.getLimbN 0) (b.getLimbN 0)

/-- Product offset 104 after layout call00. -/
def mulModProductLayoutCall00P104 (a b : EvmWord) : Word :=
  mulModAddPartialHiValue (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)

/-- Carry generated by layout call00 before propagating through offset 112. -/
def mulModProductLayoutCall00Carry104 (a b : EvmWord) : Word :=
  mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)

/-- Product offset 112 after layout call00. -/
def mulModProductLayoutCall00P112 (a b : EvmWord) : Word :=
  mulModCarryStepValue (0 : Word) (mulModProductLayoutCall00Carry104 a b)

/-- Carry after layout call00 propagates through offset 112. -/
def mulModProductLayoutCall00Carry112 (a b : EvmWord) : Word :=
  mulModCarryStepCarry (0 : Word) (mulModProductLayoutCall00Carry104 a b)

/-- Product offset 120 after layout call00. -/
def mulModProductLayoutCall00P120 (a b : EvmWord) : Word :=
  mulModCarryStepValue (0 : Word) (mulModProductLayoutCall00Carry112 a b)

/-- Carry after layout call00 propagates through offset 120. -/
def mulModProductLayoutCall00Carry120 (a b : EvmWord) : Word :=
  mulModCarryStepCarry (0 : Word) (mulModProductLayoutCall00Carry112 a b)

/-- Product offset 128 after layout call00. -/
def mulModProductLayoutCall00P128 (a b : EvmWord) : Word :=
  mulModCarryStepValue (0 : Word) (mulModProductLayoutCall00Carry120 a b)

/-- Carry after layout call00 propagates through offset 128. -/
def mulModProductLayoutCall00Carry128 (a b : EvmWord) : Word :=
  mulModCarryStepCarry (0 : Word) (mulModProductLayoutCall00Carry120 a b)

/-- Product offset 136 after layout call00. -/
def mulModProductLayoutCall00P136 (a b : EvmWord) : Word :=
  mulModCarryStepValue (0 : Word) (mulModProductLayoutCall00Carry128 a b)

/-- Carry after layout call00 propagates through offset 136. -/
def mulModProductLayoutCall00Carry136 (a b : EvmWord) : Word :=
  mulModCarryStepCarry (0 : Word) (mulModProductLayoutCall00Carry128 a b)

/-- Product offset 144 after layout call00. -/
def mulModProductLayoutCall00P144 (a b : EvmWord) : Word :=
  mulModCarryStepValue (0 : Word) (mulModProductLayoutCall00Carry136 a b)

/-- Carry after layout call00 propagates through offset 144. -/
def mulModProductLayoutCall00Carry144 (a b : EvmWord) : Word :=
  mulModCarryStepCarry (0 : Word) (mulModProductLayoutCall00Carry136 a b)

/-- Product offset 152 after layout call00. -/
def mulModProductLayoutCall00P152 (a b : EvmWord) : Word :=
  mulModCarryStepValue (0 : Word) (mulModProductLayoutCall00Carry144 a b)

/-- Carry after layout call00 propagates through offset 152. -/
def mulModProductLayoutCall00Carry152 (a b : EvmWord) : Word :=
  mulModCarryStepCarry (0 : Word) (mulModProductLayoutCall00Carry144 a b)

/-- Product-layout cells that layout call01 does not touch after call00. -/
@[irreducible]
def evmMulModProductLayoutCall01Frame (sp : Word) (a b n : EvmWord) : Assertion :=
  (sp ↦ₘ a.getLimbN 0) **
  ((sp + 16) ↦ₘ a.getLimbN 2) **
  ((sp + 24) ↦ₘ a.getLimbN 3) **
  ((sp + 40) ↦ₘ b.getLimbN 1) **
  ((sp + 48) ↦ₘ b.getLimbN 2) **
  ((sp + 56) ↦ₘ b.getLimbN 3) **
  ((sp + 64) ↦ₘ n.getLimbN 0) **
  ((sp + 72) ↦ₘ n.getLimbN 1) **
  ((sp + 80) ↦ₘ n.getLimbN 2) **
  ((sp + 88) ↦ₘ n.getLimbN 3) **
  ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ mulModProductLayoutCall00P96 a b)

/-- Folded post after zeroing and product-layout calls 00 and 01. -/
@[irreducible]
def evmMulModProductLayoutZeroCall01Post (sp : Word) (a b n : EvmWord) : Assertion :=
  (((.x12 ↦ᵣ sp) **
    (.x10 ↦ᵣ mulModCarryStepCarry (mulModProductLayoutCall00P152 a b)
      (mulModCarryStepCarry (mulModProductLayoutCall00P144 a b)
        (mulModCarryStepCarry (mulModProductLayoutCall00P136 a b)
          (mulModCarryStepCarry (mulModProductLayoutCall00P128 a b)
            (mulModCarryStepCarry (mulModProductLayoutCall00P120 a b)
              (mulModAddPartialHiCarry (mulModProductLayoutCall00P112 a b)
                (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0))))))) **
    (.x9 ↦ᵣ mulModCarryStepValue (mulModProductLayoutCall00P152 a b)
      (mulModCarryStepCarry (mulModProductLayoutCall00P144 a b)
        (mulModCarryStepCarry (mulModProductLayoutCall00P136 a b)
          (mulModCarryStepCarry (mulModProductLayoutCall00P128 a b)
            (mulModCarryStepCarry (mulModProductLayoutCall00P120 a b)
              (mulModAddPartialHiCarry (mulModProductLayoutCall00P112 a b)
                (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0))))))) **
    ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ
      mulModCarryStepValue (mulModProductLayoutCall00P120 a b)
        (mulModAddPartialHiCarry (mulModProductLayoutCall00P112 a b)
          (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0))) **
    ((sp + signExtend12 (128 : BitVec 12)) ↦ₘ
      mulModCarryStepValue (mulModProductLayoutCall00P128 a b)
        (mulModCarryStepCarry (mulModProductLayoutCall00P120 a b)
          (mulModAddPartialHiCarry (mulModProductLayoutCall00P112 a b)
            (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0)))) **
    ((sp + signExtend12 (136 : BitVec 12)) ↦ₘ
      mulModCarryStepValue (mulModProductLayoutCall00P136 a b)
        (mulModCarryStepCarry (mulModProductLayoutCall00P128 a b)
          (mulModCarryStepCarry (mulModProductLayoutCall00P120 a b)
            (mulModAddPartialHiCarry (mulModProductLayoutCall00P112 a b)
              (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0))))) **
    ((sp + signExtend12 (144 : BitVec 12)) ↦ₘ
      mulModCarryStepValue (mulModProductLayoutCall00P144 a b)
        (mulModCarryStepCarry (mulModProductLayoutCall00P136 a b)
          (mulModCarryStepCarry (mulModProductLayoutCall00P128 a b)
            (mulModCarryStepCarry (mulModProductLayoutCall00P120 a b)
              (mulModAddPartialHiCarry (mulModProductLayoutCall00P112 a b)
                (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0)))))) **
    ((sp + signExtend12 (152 : BitVec 12)) ↦ₘ
      mulModCarryStepValue (mulModProductLayoutCall00P152 a b)
        (mulModCarryStepCarry (mulModProductLayoutCall00P144 a b)
          (mulModCarryStepCarry (mulModProductLayoutCall00P136 a b)
            (mulModCarryStepCarry (mulModProductLayoutCall00P128 a b)
              (mulModCarryStepCarry (mulModProductLayoutCall00P120 a b)
                (mulModAddPartialHiCarry (mulModProductLayoutCall00P112 a b)
                  (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0))))))) **
    (.x5 ↦ᵣ a.getLimbN 1) **
    (.x6 ↦ᵣ b.getLimbN 0) **
    (.x7 ↦ᵣ mulModAddPartialLoProduct (a.getLimbN 1) (b.getLimbN 0)) **
    (.x8 ↦ᵣ mulModAddPartialHiProduct (a.getLimbN 1) (b.getLimbN 0)) **
    (.x11 ↦ᵣ mulModAddPartialHiValue (mulModProductLayoutCall00P112 a b)
      (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0)) **
    (.x13 ↦ᵣ mulModAddPartialHiBaseCarry (mulModProductLayoutCall00P112 a b)
      (a.getLimbN 1) (b.getLimbN 0)) **
    (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo (mulModProductLayoutCall00P112 a b)
      (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0)) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ a.getLimbN 1) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ b.getLimbN 0) **
    ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ
      mulModAddPartialLoValue (mulModProductLayoutCall00P104 a b)
        (a.getLimbN 1) (b.getLimbN 0)) **
    ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ
      mulModAddPartialHiValue (mulModProductLayoutCall00P112 a b)
        (mulModProductLayoutCall00P104 a b) (a.getLimbN 1) (b.getLimbN 0))) **
   evmMulModProductLayoutCall01Frame sp a b n)

/-- Product-layout prefix through call01. -/
theorem evm_mulmod_product_layout_zero_call01_spec_within
    (sp base : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin ((8 + (15 + 24)) + (15 + 20)) base (base + 328)
      (evm_mulmod_product_layout_code base)
      (evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
       ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
        (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
        (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
      (evmMulModProductLayoutZeroCall01Post sp a b n) := by
  simp only [evmMulModProductLayoutPre_unfold]
  unfold evmMulModProductLayoutZeroCall01Post evmMulModProductLayoutCall01Frame
  unfold mulModProductLayoutCall00P96 mulModProductLayoutCall00P104
  unfold mulModProductLayoutCall00P112 mulModProductLayoutCall00P120
  unfold mulModProductLayoutCall00P128 mulModProductLayoutCall00P136
  unfold mulModProductLayoutCall00P144 mulModProductLayoutCall00P152
  unfold mulModProductLayoutCall00Carry104 mulModProductLayoutCall00Carry112
  unfold mulModProductLayoutCall00Carry120 mulModProductLayoutCall00Carry128
  unfold mulModProductLayoutCall00Carry136 mulModProductLayoutCall00Carry144
  have hPrev := evm_mulmod_product_layout_zero_call00_spec_within sp base a b n
    p0 p1 p2 p3 p4 p5 p6 p7
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  simp only [evmMulModProductLayoutPre_unfold, evmMulModProductLayoutCall00Frame_unfold] at hPrev
  have hCall := evm_mulmod_product_layout_call01_spec_within sp base
    (a.getLimbN 1) (b.getLimbN 0)
    (mulModAddPartialHiValue (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))
    (mulModCarryStepValue (0 : Word)
      (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)))
    (mulModCarryStepValue (0 : Word)
      (mulModCarryStepCarry (0 : Word)
        (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))))
    (mulModCarryStepValue (0 : Word)
      (mulModCarryStepCarry (0 : Word)
        (mulModCarryStepCarry (0 : Word)
          (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)))))
    (mulModCarryStepValue (0 : Word)
      (mulModCarryStepCarry (0 : Word)
        (mulModCarryStepCarry (0 : Word)
          (mulModCarryStepCarry (0 : Word)
            (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))))))
    (mulModCarryStepValue (0 : Word)
      (mulModCarryStepCarry (0 : Word)
        (mulModCarryStepCarry (0 : Word)
          (mulModCarryStepCarry (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0)))))))
    (mulModCarryStepValue (0 : Word)
      (mulModCarryStepCarry (0 : Word)
        (mulModCarryStepCarry (0 : Word)
          (mulModCarryStepCarry (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))))))))
    (a.getLimbN 0) (b.getLimbN 0)
    (mulModAddPartialLoProduct (a.getLimbN 0) (b.getLimbN 0))
    (mulModAddPartialHiProduct (a.getLimbN 0) (b.getLimbN 0))
    (mulModCarryStepValue (0 : Word)
      (mulModCarryStepCarry (0 : Word)
        (mulModCarryStepCarry (0 : Word)
          (mulModCarryStepCarry (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))))))))
    (mulModCarryStepCarry (0 : Word)
      (mulModCarryStepCarry (0 : Word)
        (mulModCarryStepCarry (0 : Word)
          (mulModCarryStepCarry (0 : Word)
            (mulModCarryStepCarry (0 : Word)
              (mulModCarryStepCarry (0 : Word)
                (mulModAddPartialHiCarry (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))))))))
    (mulModAddPartialHiValue (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))
    (mulModAddPartialHiBaseCarry (0 : Word) (a.getLimbN 0) (b.getLimbN 0))
    (mulModAddPartialHiCarryFromLo (0 : Word) (0 : Word) (a.getLimbN 0) (b.getLimbN 0))
  unfold evmMulModAddPartialCoreFullPre at hCall
  simp only [signExtend12_8, signExtend12_32] at hCall
  have hCallF := cpsTripleWithin_frameR
    (((sp ↦ₘ a.getLimbN 0) **
      ((sp + 16) ↦ₘ a.getLimbN 2) **
      ((sp + 24) ↦ₘ a.getLimbN 3) **
      ((sp + 40) ↦ₘ b.getLimbN 1) **
      ((sp + 48) ↦ₘ b.getLimbN 2) **
      ((sp + 56) ↦ₘ b.getLimbN 3) **
      ((sp + 64) ↦ₘ n.getLimbN 0) **
      ((sp + 72) ↦ₘ n.getLimbN 1) **
      ((sp + 80) ↦ₘ n.getLimbN 2) **
      ((sp + 88) ↦ₘ n.getLimbN 3) **
      ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ
        mulModAddPartialLoValue (0 : Word) (a.getLimbN 0) (b.getLimbN 0))))
    (by pcFree) hCall
  have hComp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hPrev hCallF
  rw [show base + 188 + 60 + 80 = base + 328 by bv_omega] at hComp
  simp only [mulModProductLayoutCall00Carry104, mulModProductLayoutCall00Carry112,
    mulModProductLayoutCall00Carry120, mulModProductLayoutCall00Carry128,
    mulModProductLayoutCall00Carry136, signExtend12_8, signExtend12_32]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    hComp


end EvmAsm.Evm64
