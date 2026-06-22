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
        (0 : BitVec 12) (32 : BitVec 12) (96 : BitVec 12) (104 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 88) evm_mulmod
    (LD .x5 .x12 (0 : BitVec 12) ;;
     LD .x6 .x12 (32 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (96 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (96 : BitVec 12) ;;
     LD .x9 .x12 (104 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (104 : BitVec 12)) 22 ?_ ?_ ?_ ?_
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
        (0 : BitVec 12) (32 : BitVec 12) (96 : BitVec 12) (104 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (0 : BitVec 12) (32 : BitVec 12) (96 : BitVec 12) (104 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 88)
      (0 : BitVec 12) (32 : BitVec 12) (96 : BitVec 12) (104 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_first_core_finish_sub base)

/-- The core+finish block of the second product partial at offset 244 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_second_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 244)
        (8 : BitVec 12) (32 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 244) evm_mulmod
    (LD .x5 .x12 (8 : BitVec 12) ;;
     LD .x6 .x12 (32 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (104 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (104 : BitVec 12) ;;
     LD .x9 .x12 (112 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (112 : BitVec 12)) 61 ?_ ?_ ?_ ?_
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
        (8 : BitVec 12) (32 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (8 : BitVec 12) (32 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 244)
      (8 : BitVec 12) (32 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_second_core_finish_sub base)

/-- The core+finish block of the third product partial at offset 384 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_third_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 384)
        (0 : BitVec 12) (40 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 384) evm_mulmod
    (LD .x5 .x12 (0 : BitVec 12) ;;
     LD .x6 .x12 (40 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (104 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (104 : BitVec 12) ;;
     LD .x9 .x12 (112 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (112 : BitVec 12)) 96 ?_ ?_ ?_ ?_
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
        (0 : BitVec 12) (40 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (0 : BitVec 12) (40 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 384)
      (0 : BitVec 12) (40 : BitVec 12) (104 : BitVec 12) (112 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_third_core_finish_sub base)

/-- The core+finish block of the fourth product partial at offset 524 is subsumed
    by the top-level `evm_mulmod_program_code`. -/
theorem evm_mulmod_program_code_product_fourth_core_finish_sub
    (base : Word) :
    ∀ a i, (evm_mulmod_product_add_partial_core_finish_code (base + 524)
        (16 : BitVec 12) (32 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12)) a = some i →
      (evm_mulmod_program_code base) a = some i := by
  unfold evm_mulmod_product_add_partial_core_finish_code evm_mulmod_program_code
  refine CodeReq.ofProg_mono_sub base (base + 524) evm_mulmod
    (LD .x5 .x12 (16 : BitVec 12) ;;
     LD .x6 .x12 (32 : BitVec 12) ;;
     single (.MUL .x7 .x5 .x6) ;;
     single (.MULHU .x8 .x5 .x6) ;;
     LD .x9 .x12 (112 : BitVec 12) ;;
     ADD .x9 .x9 .x7 ;;
     SLTU .x10 .x9 .x7 ;;
     SD .x12 .x9 (112 : BitVec 12) ;;
     LD .x9 .x12 (120 : BitVec 12) ;;
     ADD .x11 .x9 .x8 ;;
     SLTU .x13 .x11 .x8 ;;
     ADD .x11 .x11 .x10 ;;
     SLTU .x14 .x11 .x10 ;;
     OR' .x10 .x13 .x14 ;;
     SD .x12 .x11 (120 : BitVec 12)) 131 ?_ ?_ ?_ ?_
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
        (16 : BitVec 12) (32 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12) a b lo hi
        x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
      (evmMulModAddPartialCorePost sp
        (16 : BitVec 12) (32 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12) a b lo hi) :=
  cpsTripleWithin_extend_code
    (h := evm_mulmod_product_add_partial_core_finish_spec_within sp (base + 524)
      (16 : BitVec 12) (32 : BitVec 12) (112 : BitVec 12) (120 : BitVec 12) a b lo hi
      x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old)
    (hmono := evm_mulmod_program_code_product_fourth_core_finish_sub base)

end EvmAsm.Evm64.MulMod.Compose
