/-
  EvmAsm.Evm64.MulMod.Compose.ProductCore

  Product-partial core lifts for MULMOD. These bridge the generic
  add-partial core+finish spec onto concrete slices of the top-level program.
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

/-- The core+finish block of the first product partial at offset 88 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_first_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 88)
        (0 : BitVec 12) (32 : BitVec 12) (3936 : BitVec 12) (3944 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 88) evm_mulmod
    (LD .x5 .x12 (0 : BitVec 12) ;;
     LD .x6 .x12 (32 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3936 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3936 : BitVec 12) ;;
     LD .x9 .x12 (3944 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3944 : BitVec 12)) 22 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- First product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_first_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 88) ((base + 88) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (32 : BitVec 12) (3936 : BitVec 12) (3944 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (0 : BitVec 12) (32 : BitVec 12) (3936 : BitVec 12) (3944 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 88)
      (0 : BitVec 12) (32 : BitVec 12) (3936 : BitVec 12) (3944 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_first_core_finish_sub base)

/-- The core+finish block of the second product partial at offset 244 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_second_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 244)
        (8 : BitVec 12) (32 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 244) evm_mulmod
    (LD .x5 .x12 (8 : BitVec 12) ;;
     LD .x6 .x12 (32 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3944 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3944 : BitVec 12) ;;
     LD .x9 .x12 (3952 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3952 : BitVec 12)) 61 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Second product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_second_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 244) ((base + 244) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (32 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (8 : BitVec 12) (32 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 244)
      (8 : BitVec 12) (32 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_second_core_finish_sub base)

/-- The core+finish block of the third product partial at offset 384 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_third_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 384)
        (0 : BitVec 12) (40 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 384) evm_mulmod
    (LD .x5 .x12 (0 : BitVec 12) ;;
     LD .x6 .x12 (40 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3944 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3944 : BitVec 12) ;;
     LD .x9 .x12 (3952 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3952 : BitVec 12)) 96 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Third product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_third_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 384) ((base + 384) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (40 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (0 : BitVec 12) (40 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 384)
      (0 : BitVec 12) (40 : BitVec 12) (3944 : BitVec 12) (3952 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_third_core_finish_sub base)

/-- The core+finish block of the fourth product partial at offset 524 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fourth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 524)
        (16 : BitVec 12) (32 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 524) evm_mulmod
    (LD .x5 .x12 (16 : BitVec 12) ;;
     LD .x6 .x12 (32 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3952 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3952 : BitVec 12) ;;
     LD .x9 .x12 (3960 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3960 : BitVec 12)) 131 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Fourth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fourth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 524) ((base + 524) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (32 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (16 : BitVec 12) (32 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 524)
      (16 : BitVec 12) (32 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_fourth_core_finish_sub base)

/-- The core+finish block of the fifth product partial at offset 648 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fifth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 648)
        (8 : BitVec 12) (40 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 648) evm_mulmod
    (LD .x5 .x12 (8 : BitVec 12) ;;
     LD .x6 .x12 (40 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3952 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3952 : BitVec 12) ;;
     LD .x9 .x12 (3960 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3960 : BitVec 12)) 162 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Fifth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fifth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 648) ((base + 648) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (40 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (8 : BitVec 12) (40 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 648)
      (8 : BitVec 12) (40 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_fifth_core_finish_sub base)

/-- The core+finish block of the sixth product partial at offset 772 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_sixth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 772)
        (0 : BitVec 12) (48 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 772) evm_mulmod
    (LD .x5 .x12 (0 : BitVec 12) ;;
     LD .x6 .x12 (48 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3952 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3952 : BitVec 12) ;;
     LD .x9 .x12 (3960 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3960 : BitVec 12)) 193 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Sixth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_sixth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 772) ((base + 772) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (48 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (0 : BitVec 12) (48 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 772)
      (0 : BitVec 12) (48 : BitVec 12) (3952 : BitVec 12) (3960 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_sixth_core_finish_sub base)

/-- The core+finish block of the seventh product partial at offset 896 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_seventh_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 896)
        (24 : BitVec 12) (32 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 896) evm_mulmod
    (LD .x5 .x12 (24 : BitVec 12) ;;
     LD .x6 .x12 (32 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3960 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3960 : BitVec 12) ;;
     LD .x9 .x12 (3968 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3968 : BitVec 12)) 224 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Seventh product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_seventh_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 896) ((base + 896) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (32 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (24 : BitVec 12) (32 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 896)
      (24 : BitVec 12) (32 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_seventh_core_finish_sub base)

/-- The core+finish block of the eighth product partial at offset 1004 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_eighth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1004)
        (16 : BitVec 12) (40 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1004) evm_mulmod
    (LD .x5 .x12 (16 : BitVec 12) ;;
     LD .x6 .x12 (40 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3960 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3960 : BitVec 12) ;;
     LD .x9 .x12 (3968 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3968 : BitVec 12)) 251 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Eighth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_eighth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1004) ((base + 1004) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (40 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (16 : BitVec 12) (40 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1004)
      (16 : BitVec 12) (40 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_eighth_core_finish_sub base)

/-- The core+finish block of the ninth product partial at offset 1112 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_ninth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1112)
        (8 : BitVec 12) (48 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1112) evm_mulmod
    (LD .x5 .x12 (8 : BitVec 12) ;;
     LD .x6 .x12 (48 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3960 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3960 : BitVec 12) ;;
     LD .x9 .x12 (3968 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3968 : BitVec 12)) 278 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Ninth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_ninth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1112) ((base + 1112) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (48 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (8 : BitVec 12) (48 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1112)
      (8 : BitVec 12) (48 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_ninth_core_finish_sub base)

/-- The core+finish block of the tenth product partial at offset 1220 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_tenth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1220)
        (0 : BitVec 12) (56 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1220) evm_mulmod
    (LD .x5 .x12 (0 : BitVec 12) ;;
     LD .x6 .x12 (56 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3960 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3960 : BitVec 12) ;;
     LD .x9 .x12 (3968 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3968 : BitVec 12)) 305 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Tenth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_tenth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1220) ((base + 1220) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (0 : BitVec 12) (56 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (0 : BitVec 12) (56 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1220)
      (0 : BitVec 12) (56 : BitVec 12) (3960 : BitVec 12) (3968 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_tenth_core_finish_sub base)

/-- The core+finish block of the eleventh product partial at offset 1328 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_eleventh_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1328)
        (24 : BitVec 12) (40 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1328) evm_mulmod
    (LD .x5 .x12 (24 : BitVec 12) ;;
     LD .x6 .x12 (40 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3968 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3968 : BitVec 12) ;;
     LD .x9 .x12 (3976 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3976 : BitVec 12)) 332 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Eleventh product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_eleventh_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1328) ((base + 1328) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (40 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (24 : BitVec 12) (40 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1328)
      (24 : BitVec 12) (40 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_eleventh_core_finish_sub base)

/-- The core+finish block of the twelfth product partial at offset 1420 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_twelfth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1420)
        (16 : BitVec 12) (48 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1420) evm_mulmod
    (LD .x5 .x12 (16 : BitVec 12) ;;
     LD .x6 .x12 (48 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3968 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3968 : BitVec 12) ;;
     LD .x9 .x12 (3976 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3976 : BitVec 12)) 355 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Twelfth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_twelfth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1420) ((base + 1420) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (48 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (16 : BitVec 12) (48 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1420)
      (16 : BitVec 12) (48 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_twelfth_core_finish_sub base)

/-- The core+finish block of the thirteenth product partial at offset 1512 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_thirteenth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1512)
        (8 : BitVec 12) (56 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1512) evm_mulmod
    (LD .x5 .x12 (8 : BitVec 12) ;;
     LD .x6 .x12 (56 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3968 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3968 : BitVec 12) ;;
     LD .x9 .x12 (3976 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3976 : BitVec 12)) 378 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Thirteenth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_thirteenth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1512) ((base + 1512) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (8 : BitVec 12) (56 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (8 : BitVec 12) (56 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1512)
      (8 : BitVec 12) (56 : BitVec 12) (3968 : BitVec 12) (3976 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_thirteenth_core_finish_sub base)

/-- The core+finish block of the fourteenth product partial at offset 1604 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fourteenth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1604)
        (24 : BitVec 12) (48 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1604) evm_mulmod
    (LD .x5 .x12 (24 : BitVec 12) ;;
     LD .x6 .x12 (48 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3976 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3976 : BitVec 12) ;;
     LD .x9 .x12 (3984 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3984 : BitVec 12)) 401 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Fourteenth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fourteenth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1604) ((base + 1604) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (48 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (24 : BitVec 12) (48 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1604)
      (24 : BitVec 12) (48 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_fourteenth_core_finish_sub base)

/-- The core+finish block of the fifteenth product partial at offset 1680 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fifteenth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1680)
        (16 : BitVec 12) (56 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1680) evm_mulmod
    (LD .x5 .x12 (16 : BitVec 12) ;;
     LD .x6 .x12 (56 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3976 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3976 : BitVec 12) ;;
     LD .x9 .x12 (3984 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3984 : BitVec 12)) 420 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Fifteenth product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_fifteenth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1680) ((base + 1680) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (16 : BitVec 12) (56 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (16 : BitVec 12) (56 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1680)
      (16 : BitVec 12) (56 : BitVec 12) (3976 : BitVec 12) (3984 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_fifteenth_core_finish_sub base)

/-- The core+finish block of the final product partial at offset 1756 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_sixteenth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 1756)
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 1756) evm_mulmod
    (LD .x5 .x12 (24 : BitVec 12) ;;
     LD .x6 .x12 (56 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (3984 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (3984 : BitVec 12) ;;
     LD .x9 .x12 (3992 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (3992 : BitVec 12)) 439 ?_ ?_ ?_ ?_
  · bv_omega
  · evm_mulmod_slice_rfl
  · rw [evm_mulmod_length]
    decide
  · rw [evm_mulmod_length]
    decide

/-- Final product-partial core+finish block lifted onto `evm_mulmod_program_code`. -/
theorem evm_mulmod_product_sixteenth_core_finish_evm_mulmod_spec_within
    (sp : Word) (base : Word) (a b lo hi : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 15 (base + 1756) ((base + 1756) + 60) (evm_mulmod_program_code base)
      (evmMulModAddPartialCoreFullPre sp
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 1756)
      (24 : BitVec 12) (56 : BitVec 12) (3984 : BitVec 12) (3992 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_sixteenth_core_finish_sub base)

end EvmAsm.Evm64.MulMod.Compose
