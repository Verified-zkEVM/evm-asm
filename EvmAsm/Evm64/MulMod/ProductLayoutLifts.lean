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

end EvmAsm.Evm64
