/-
  EvmAsm.Evm64.MulMod.Compose.ProductSuffix

  Additional product-partial suffix lifts for MULMOD, kept separate from
  `Compose.Base` so the base infrastructure stays below the file-size cap.
-/

import EvmAsm.Evm64.MulMod.Compose.Base

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

local macro "evm_mulmod_slice_rfl" : tactic =>
  `(tactic|
    first
      | rfl
      | (unfold evm_mulmod evm_mulmod_nonzero_or_zero_prefix
            evm_mulmod_reduce_zero_path evm_mulmod_epilogue
            evm_mulmod_zero_path_skip_nonzero evm_mulmod_product_layout
            evm_mulmod_product_zero evm_mulmod_product_add_partial
            evm_mulmod_product_propagate_carry evm_mulmod_reduce512 evm_mulmod_reduce512_loop
            evm_mulmod_reduce512_write_result evm_mulmod_reduce512_init
            LD OR' BNE SD ADDI JAL MUL MULHU ADD SLTU single seq
         rfl))

/-- The finish suffix of the tenth product partial at offset 1272 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_tenth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1272)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1272) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3968 : BitVec 12)) 318 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the tenth product partial at offset 1280 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_tenth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1280)
        (evm_mulmod_product_propagate_carry [3976, 3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1280) evm_mulmod
    (evm_mulmod_product_propagate_carry [3976, 3984, 3992]) 320 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Tenth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_tenth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1272) ((base + 1272) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3968 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1272)
      (3968 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_tenth_finish_sub base)

/-- Tenth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_tenth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p5 p6 p7 : Word) :
    cpsTripleWithin 12 (base + 1280) ((base + 1280) + 48) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ p5) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ mulModCarryStepCarry p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       (.x9 ↦ᵣ mulModCarryStepValue p7
          (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry))) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ mulModCarryStepValue p5 carry) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p6 (mulModCarryStepCarry p5 carry)) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7
           (mulModCarryStepCarry p6 (mulModCarryStepCarry p5 carry)))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_136_144_152_spec_within
      sp (base + 1280) carry v9 p5 p6 p7)
    (hmono := evm_mulmod_program_code_product_tenth_carry_sub base)

/-- The finish suffix of the eleventh product partial at offset 1380 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_eleventh_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1380)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3976 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1380) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3976 : BitVec 12)) 345 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the eleventh product partial at offset 1388 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_eleventh_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1388)
        (evm_mulmod_product_propagate_carry [3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1388) evm_mulmod
    (evm_mulmod_product_propagate_carry [3984, 3992]) 347 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Eleventh product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_eleventh_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1380) ((base + 1380) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1380)
      (3976 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_eleventh_finish_sub base)

/-- Eleventh product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_eleventh_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p6 p7 : Word) :
    cpsTripleWithin 8 (base + 1388) ((base + 1388) + 32) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 carry)) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 carry)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 carry) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7 (mulModCarryStepCarry p6 carry))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_144_152_spec_within
      sp (base + 1388) carry v9 p6 p7)
    (hmono := evm_mulmod_program_code_product_eleventh_carry_sub base)

/-- The finish suffix of the twelfth product partial at offset 1472 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_twelfth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1472)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3976 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1472) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3976 : BitVec 12)) 368 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the twelfth product partial at offset 1480 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_twelfth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1480)
        (evm_mulmod_product_propagate_carry [3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1480) evm_mulmod
    (evm_mulmod_product_propagate_carry [3984, 3992]) 370 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Twelfth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_twelfth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1472) ((base + 1472) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1472)
      (3976 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_twelfth_finish_sub base)

/-- Twelfth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_twelfth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p6 p7 : Word) :
    cpsTripleWithin 8 (base + 1480) ((base + 1480) + 32) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 carry)) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 carry)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 carry) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7 (mulModCarryStepCarry p6 carry))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_144_152_spec_within
      sp (base + 1480) carry v9 p6 p7)
    (hmono := evm_mulmod_program_code_product_twelfth_carry_sub base)

/-- The finish suffix of the thirteenth product partial at offset 1564 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_thirteenth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1564)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3976 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1564) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3976 : BitVec 12)) 391 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the thirteenth product partial at offset 1572 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_thirteenth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1572)
        (evm_mulmod_product_propagate_carry [3984, 3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1572) evm_mulmod
    (evm_mulmod_product_propagate_carry [3984, 3992]) 393 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Thirteenth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_thirteenth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1564) ((base + 1564) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3976 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1564)
      (3976 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_thirteenth_finish_sub base)

/-- Thirteenth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_thirteenth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p6 p7 : Word) :
    cpsTripleWithin 8 (base + 1572) ((base + 1572) + 32) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ p6) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 (mulModCarryStepCarry p6 carry)) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 (mulModCarryStepCarry p6 carry)) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ mulModCarryStepValue p6 carry) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ
         mulModCarryStepValue p7 (mulModCarryStepCarry p6 carry))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_144_152_spec_within
      sp (base + 1572) carry v9 p6 p7)
    (hmono := evm_mulmod_program_code_product_thirteenth_carry_sub base)

/-- The finish suffix of the fourteenth product partial at offset 1656 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fourteenth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1656)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3984 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1656) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3984 : BitVec 12)) 414 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the fourteenth product partial at offset 1664 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fourteenth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1664)
        (evm_mulmod_product_propagate_carry [3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1664) evm_mulmod
    (evm_mulmod_product_propagate_carry [3992]) 416 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Fourteenth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fourteenth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1656) ((base + 1656) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1656)
      (3984 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_fourteenth_finish_sub base)

/-- Fourteenth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fourteenth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p7 : Word) :
    cpsTripleWithin 4 (base + 1664) ((base + 1664) + 16) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 carry) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 carry) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 carry)) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_one_spec_within
      sp (base + 1664) (3992 : BitVec 12) carry p7 v9)
    (hmono := evm_mulmod_program_code_product_fourteenth_carry_sub base)

/-- The finish suffix of the fifteenth product partial at offset 1732 is subsumed by
    the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fifteenth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1732)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3984 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1732) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3984 : BitVec 12)) 433 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- The carry-propagation suffix of the fifteenth product partial at offset 1740 is
    subsumed by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fifteenth_carry_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1740)
        (evm_mulmod_product_propagate_carry [3992])) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1740) evm_mulmod
    (evm_mulmod_product_propagate_carry [3992]) 435 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Fifteenth product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fifteenth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1732) ((base + 1732) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3984 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1732)
      (3984 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_fifteenth_finish_sub base)

/-- Fifteenth product-partial carry suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fifteenth_carry_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (carry v9 p7 : Word) :
    cpsTripleWithin 4 (base + 1740) ((base + 1740) + 16) (evm_mulmod_program_code base)
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ carry) ** (.x9 ↦ᵣ v9) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ p7))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ mulModCarryStepCarry p7 carry) **
       (.x9 ↦ᵣ mulModCarryStepValue p7 carry) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ mulModCarryStepValue p7 carry)) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_propagate_carry_one_spec_within
      sp (base + 1740) (3992 : BitVec 12) carry p7 v9)
    (hmono := evm_mulmod_program_code_product_fifteenth_carry_sub base)

/-- The finish suffix of the final product partial at offset 1808 is subsumed by
    the top-level `evm_mulmod_program_code`. The final partial has no carry tail,
    so this suffix reaches the reducer start at offset 1816. -/
theorem evm_mulmod_program_code_product_sixteenth_finish_sub
    (base : Word) :
    ∀ a i, (CodeReq.ofProg (base + 1808)
        (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3992 : BitVec 12))) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1808) evm_mulmod
    (OR' .x10 .x13 .x14 ;; SD .x12 .x11 (3992 : BitVec 12)) 452 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Final product-partial finish suffix lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_sixteenth_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word)
    (loCarry hiBaseCarry hiCarryFromLo hiVal hiOld : Word) :
    cpsTripleWithin 2 (base + 1808) ((base + 1808) + 8) (evm_mulmod_program_code base)
      ((.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) ** (.x10 ↦ᵣ loCarry) **
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
       ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ hiOld))
      (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ hiVal) **
        ((sp + signExtend12 (3992 : BitVec 12)) ↦ₘ hiVal)) **
       (.x13 ↦ᵣ hiBaseCarry) ** (.x14 ↦ᵣ hiCarryFromLo) **
       (.x10 ↦ᵣ (hiBaseCarry ||| hiCarryFromLo))) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_finish_spec_within sp (base + 1808)
      (3992 : BitVec 12) loCarry hiBaseCarry hiCarryFromLo hiVal hiOld)
    (hmono := evm_mulmod_program_code_product_sixteenth_finish_sub base)

end EvmAsm.Evm64.MulMod.Compose
