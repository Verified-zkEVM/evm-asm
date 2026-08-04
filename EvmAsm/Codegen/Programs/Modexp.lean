/-
  EvmAsm.Codegen.Programs.Modexp

  MODEXP precompile assembly helpers split out of `Programs.Noop` to keep the
  child-frame handler module under the file-size guardrail.
-/

namespace EvmAsm.Codegen

private def modexpReadLengthAsm (suffix : String) (fieldOff : Nat) (dstReg : String) : String :=
  "  li " ++ dstReg ++ ", 0\n" ++
  "  li x29, 0\n" ++
  ".Lmodexp_len_loop_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x31, 32\n" ++
  "  beq x29, x31, .Lmodexp_len_done_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  "  addi x31, x29, " ++ toString fieldOff ++ "\n" ++
  "  bgeu x31, x17, .Lmodexp_len_missing_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  "  add x31, x18, x31
  lbu x16, 0(x31)
" ++
  "  j .Lmodexp_len_have_byte_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  ".Lmodexp_len_missing_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x16, 0\n" ++
  ".Lmodexp_len_have_byte_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x31, 30\n" ++
  "  bltu x29, x31, .Lmodexp_len_high_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  "  slli " ++ dstReg ++ ", " ++ dstReg ++ ", 8\n" ++
  "  or " ++ dstReg ++ ", " ++ dstReg ++ ", x16\n" ++
  "  j .Lmodexp_len_next_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  ".Lmodexp_len_high_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  bnez x16, .L" ++ suffix ++ "_bn254_fail_allot\n" ++
  ".Lmodexp_len_next_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  addi x29, x29, 1\n" ++
  "  j .Lmodexp_len_loop_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  ".Lmodexp_len_done_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x31, 1024\n" ++
  "  bltu x31, " ++ dstReg ++ ", .L" ++ suffix ++ "_bn254_fail_allot\n"

private def modexpByteLog2Asm (suffix : String) : String :=
  "  li x31, 128\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_7_" ++ suffix ++ "\n" ++
  "  li x31, 64\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_6_" ++ suffix ++ "\n" ++
  "  li x31, 32\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_5_" ++ suffix ++ "\n" ++
  "  li x31, 16\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_4_" ++ suffix ++ "\n" ++
  "  li x31, 8\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_3_" ++ suffix ++ "\n" ++
  "  li x31, 4\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_2_" ++ suffix ++ "\n" ++
  "  li x31, 2\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_1_" ++ suffix ++ "\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_7_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 7\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_6_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 6\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_5_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 5\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_4_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 4\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_3_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 3\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_2_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 2\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_1_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 1\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n"

private def modexpReadSmallComponentAsm
    (suffix name startReg lenReg dstReg : String) : String :=
  "  li " ++ dstReg ++ ", 0\n" ++
  "  li x29, 0\n" ++
  ".Lmodexp_read_" ++ name ++ "_loop_" ++ suffix ++ ":\n" ++
  "  beq x29, " ++ lenReg ++ ", .Lmodexp_read_" ++ name ++ "_done_" ++ suffix ++ "\n" ++
  "  add x31, " ++ startReg ++ ", x29\n" ++
  "  bgeu x31, x17, .Lmodexp_read_" ++ name ++ "_missing_" ++ suffix ++ "\n" ++
  "  add x31, x18, x31
  lbu x16, 0(x31)
" ++
  "  j .Lmodexp_read_" ++ name ++ "_have_" ++ suffix ++ "\n" ++
  ".Lmodexp_read_" ++ name ++ "_missing_" ++ suffix ++ ":\n" ++
  "  li x16, 0\n" ++
  ".Lmodexp_read_" ++ name ++ "_have_" ++ suffix ++ ":\n" ++
  "  slli " ++ dstReg ++ ", " ++ dstReg ++ ", 8\n" ++
  "  or " ++ dstReg ++ ", " ++ dstReg ++ ", x16\n" ++
  "  addi x29, x29, 1\n" ++
  "  j .Lmodexp_read_" ++ name ++ "_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_read_" ++ name ++ "_done_" ++ suffix ++ ":\n"

private def modexpStageComponentAsm
    (suffix name startReg lenReg dstLabel : String) : String :=
  "  la x28, " ++ dstLabel ++ "\n" ++
  "  li x29, 0\n" ++
  ".Lmodexp_stage_" ++ name ++ "_loop_" ++ suffix ++ ":\n" ++
  "  beq x29, " ++ lenReg ++ ", .Lmodexp_stage_" ++ name ++ "_done_" ++ suffix ++ "\n" ++
  "  add x31, " ++ startReg ++ ", x29\n" ++
  "  bgeu x31, x17, .Lmodexp_stage_" ++ name ++ "_missing_" ++ suffix ++ "\n" ++
  "  add x31, x18, x31
  lbu x16, 0(x31)
" ++
  "  j .Lmodexp_stage_" ++ name ++ "_have_" ++ suffix ++ "\n" ++
  ".Lmodexp_stage_" ++ name ++ "_missing_" ++ suffix ++ ":\n" ++
  "  li x16, 0\n" ++
  ".Lmodexp_stage_" ++ name ++ "_have_" ++ suffix ++ ":\n" ++
  "  sb x16, 0(x28)
  addi x28, x28, 1
  addi x29, x29, 1
" ++
  "  j .Lmodexp_stage_" ++ name ++ "_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_stage_" ++ name ++ "_done_" ++ suffix ++ ":\n"

def modexpPrecompileGasAsm
    (chargePrecompileGasAsm : String → String → String)
    (suffix : String)
    (inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat) : String :=
  "  la x15, evm_precompile_frame
  li x16, 1
  sd x16, 0(x15)
  sd x0, 8(x15)
" ++
  "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x18, x13, x18\n" ++
  modexpReadLengthAsm suffix 0 "x5" ++
  modexpReadLengthAsm suffix 32 "x22" ++
  modexpReadLengthAsm suffix 64 "x23" ++
  "  la x16, precompile_shared_status\n  ld x16, 0(x16)\n" ++
  "  bnez x16, .L" ++ suffix ++ "_bn254_fail_allot\n" ++
  "  la x16, precompile_shared_cost\n  ld x16, 0(x16)\n" ++
  chargePrecompileGasAsm "x16" "x31" ++
  "  or x24, x5, x23
  beqz x24, 7b
  beqz x23, 7b
  li x31, 4
" ++
  "  bltu x31, x5, .Lmodexp_backend_" ++ suffix ++ "\n" ++
  "  bltu x31, x22, .Lmodexp_backend_" ++ suffix ++ "\n" ++
  "  bltu x31, x23, .Lmodexp_backend_" ++ suffix ++ "\n" ++
  "  li x30, 96\n" ++
  modexpReadSmallComponentAsm suffix "base" "x30" "x5" "x24" ++
  "  add x30, x30, x5\n" ++
  modexpReadSmallComponentAsm suffix "exp" "x30" "x22" "x25" ++
  "  add x30, x30, x22\n" ++
  modexpReadSmallComponentAsm suffix "mod" "x30" "x23" "x26" ++
  "  li x27, 0\n" ++
  "  beqz x26, .Lmodexp_result_ready_" ++ suffix ++ "\n" ++
  "  remu x24, x24, x26
  li x27, 1
  remu x27, x27, x26
  mv x28, x25
" ++
  ".Lmodexp_pow_loop_" ++ suffix ++ ":\n" ++
  "  beqz x28, .Lmodexp_result_ready_" ++ suffix ++ "\n" ++
  "  andi x31, x28, 1\n" ++
  "  beqz x31, .Lmodexp_pow_skip_mul_" ++ suffix ++ "\n" ++
  "  mul x27, x27, x24
  remu x27, x27, x26
" ++
  ".Lmodexp_pow_skip_mul_" ++ suffix ++ ":\n" ++
  "  srli x28, x28, 1\n" ++
  "  beqz x28, .Lmodexp_pow_loop_" ++ suffix ++ "\n" ++
  "  mul x24, x24, x24
  remu x24, x24, x26
" ++
  "  j .Lmodexp_pow_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_result_ready_" ++ suffix ++ ":\n" ++
  "  sd x23, 8(x15)
  addi x28, x15, 16
  li x29, 0
" ++
  ".Lmodexp_result_store_loop_" ++ suffix ++ ":\n" ++
  "  beq x29, x23, .Lmodexp_result_store_done_" ++ suffix ++ "\n" ++
  "  sub x31, x23, x29
  addi x31, x31, -1
  slli x31, x31, 3
  srl x16, x27, x31
  andi x16, x16, 255
  sb x16, 0(x28)
  addi x28, x28, 1
  addi x29, x29, 1
" ++
  "  j .Lmodexp_result_store_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_result_store_done_" ++ suffix ++ ":\n" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  mv x24, x23\n" ++
  "  bgeu x22, x24, .Lmodexp_copy_len_done_" ++ suffix ++ "\n" ++
  "  mv x24, x22\n" ++
  ".Lmodexp_copy_len_done_" ++ suffix ++ ":\n" ++
  "  beqz x24, 7b
  addi x28, x15, 16
" ++
  "  ld x29, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x29, x13, x29\n" ++
  ".Lmodexp_copy_loop_" ++ suffix ++ ":\n" ++
  "  lbu x16, 0(x28)
  sb x16, 0(x29)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x24, x24, -1
" ++
  "  bnez x24, .Lmodexp_copy_loop_" ++ suffix ++ "\n" ++
  "  j 7b\n" ++
  ".Lmodexp_backend_" ++ suffix ++ ":\n" ++
  "  li x30, 96\n" ++
  modexpStageComponentAsm suffix "base" "x30" "x5" "modexp_base_scratch" ++
  "  add x30, x30, x5\n" ++
  modexpStageComponentAsm suffix "exp" "x30" "x22" "modexp_exp_scratch" ++
  "  add x30, x30, x22\n" ++
  modexpStageComponentAsm suffix "modulus" "x30" "x23" "modexp_modulus_scratch" ++
  "  mv s9, x13
  mv s10, x10
  mv s11, x12
  la a0, modexp_base_scratch
  mv a1, x5
  la a2, modexp_exp_scratch
  mv a3, x22
  la a4, modexp_modulus_scratch
  mv a5, x23
  la a6, modexp_output_scratch
  jal x1, zkvm_modexp
  mv t6, a0
  mv x13, s9
  mv x10, s10
  mv x12, s11
  la x15, evm_precompile_frame
" ++
  "  bnez t6, .L" ++ suffix ++ "_bn254_fail_allot\n" ++
  "  sd x23, 8(x15)
  la x28, modexp_output_scratch
  addi x29, x15, 16
  mv x24, x23
" ++
  ".Lmodexp_backend_frame_copy_loop_" ++ suffix ++ ":\n" ++
  "  beqz x24, .Lmodexp_backend_frame_copy_done_" ++ suffix ++ "\n" ++
  "  lbu x16, 0(x28)
  sb x16, 0(x29)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x24, x24, -1
" ++
  "  j .Lmodexp_backend_frame_copy_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_backend_frame_copy_done_" ++ suffix ++ ":\n" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  mv x24, x23\n" ++
  "  bgeu x22, x24, .Lmodexp_backend_copy_len_done_" ++ suffix ++ "\n" ++
  "  mv x24, x22\n" ++
  ".Lmodexp_backend_copy_len_done_" ++ suffix ++ ":\n" ++
  "  beqz x24, 7b
  la x28, modexp_output_scratch
" ++
  "  ld x29, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x29, x13, x29\n" ++
  ".Lmodexp_backend_copy_loop_" ++ suffix ++ ":\n" ++
  "  lbu x16, 0(x28)
  sb x16, 0(x29)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x24, x24, -1
" ++
  "  bnez x24, .Lmodexp_backend_copy_loop_" ++ suffix ++ "\n" ++
  "  j 7b\n"

/-- Charge-free MODEXP body for `precompile_shared_execute`. Reads absolute
    calldata from `precompile_shared_ctx`, writes only `evm_precompile_frame`,
    and exits via the shared-execute soft/ok/fail labels (no OUT copy).
    Length/overflow validation is owned by `precompile_shared_select_price`;
    this body re-checks status then computes. Soft-empty when base|mod lengths
    are zero (execution-specs empty returndata success). -/
def modexpSharedExecuteAsm : String :=
  let suffix := "pse"
  "  la x15, evm_precompile_frame\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  la t0, precompile_shared_ctx\n" ++
  "  ld x18, 8(t0)\n" ++
  "  ld x17, 16(t0)\n" ++
  modexpReadLengthAsm suffix 0 "x5" ++
  modexpReadLengthAsm suffix 32 "x22" ++
  modexpReadLengthAsm suffix 64 "x23" ++
  "  la x16, precompile_shared_status\n  ld x16, 0(x16)\n" ++
  "  bnez x16, .Lpse_fail\n" ++
  "  or x24, x5, x23\n" ++
  "  beqz x24, .Lpse_soft_ok\n" ++
  "  beqz x23, .Lpse_soft_ok\n" ++
  "  li x31, 4\n" ++
  "  bltu x31, x5, .Lmodexp_backend_" ++ suffix ++ "\n" ++
  "  bltu x31, x22, .Lmodexp_backend_" ++ suffix ++ "\n" ++
  "  bltu x31, x23, .Lmodexp_backend_" ++ suffix ++ "\n" ++
  "  li x30, 96\n" ++
  modexpReadSmallComponentAsm suffix "base" "x30" "x5" "x24" ++
  "  add x30, x30, x5\n" ++
  modexpReadSmallComponentAsm suffix "exp" "x30" "x22" "x25" ++
  "  add x30, x30, x22\n" ++
  modexpReadSmallComponentAsm suffix "mod" "x30" "x23" "x26" ++
  "  li x27, 0\n" ++
  "  beqz x26, .Lmodexp_result_ready_" ++ suffix ++ "\n" ++
  "  remu x24, x24, x26\n" ++
  "  li x27, 1\n" ++
  "  remu x27, x27, x26\n" ++
  "  mv x28, x25\n" ++
  ".Lmodexp_pow_loop_" ++ suffix ++ ":\n" ++
  "  beqz x28, .Lmodexp_result_ready_" ++ suffix ++ "\n" ++
  "  andi x31, x28, 1\n" ++
  "  beqz x31, .Lmodexp_pow_skip_mul_" ++ suffix ++ "\n" ++
  "  mul x27, x27, x24\n" ++
  "  remu x27, x27, x26\n" ++
  ".Lmodexp_pow_skip_mul_" ++ suffix ++ ":\n" ++
  "  srli x28, x28, 1\n" ++
  "  beqz x28, .Lmodexp_pow_loop_" ++ suffix ++ "\n" ++
  "  mul x24, x24, x24\n" ++
  "  remu x24, x24, x26\n" ++
  "  j .Lmodexp_pow_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_result_ready_" ++ suffix ++ ":\n" ++
  "  sd x23, 8(x15)\n" ++
  "  addi x28, x15, 16\n" ++
  "  li x29, 0\n" ++
  ".Lmodexp_result_store_loop_" ++ suffix ++ ":\n" ++
  "  beq x29, x23, .Lmodexp_result_store_done_" ++ suffix ++ "\n" ++
  "  sub x31, x23, x29\n" ++
  "  addi x31, x31, -1\n" ++
  "  slli x31, x31, 3\n" ++
  "  srl x16, x27, x31\n" ++
  "  andi x16, x16, 255\n" ++
  "  sb x16, 0(x28)\n" ++
  "  addi x28, x28, 1\n" ++
  "  addi x29, x29, 1\n" ++
  "  j .Lmodexp_result_store_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_result_store_done_" ++ suffix ++ ":\n" ++
  "  j .Lpse_ok\n" ++
  ".Lmodexp_backend_" ++ suffix ++ ":\n" ++
  "  li x30, 96\n" ++
  modexpStageComponentAsm suffix "base" "x30" "x5" "modexp_base_scratch" ++
  "  add x30, x30, x5\n" ++
  modexpStageComponentAsm suffix "exp" "x30" "x22" "modexp_exp_scratch" ++
  "  add x30, x30, x22\n" ++
  modexpStageComponentAsm suffix "modulus" "x30" "x23" "modexp_modulus_scratch" ++
  "  la a0, modexp_base_scratch\n" ++
  "  mv a1, x5\n" ++
  "  la a2, modexp_exp_scratch\n" ++
  "  mv a3, x22\n" ++
  "  la a4, modexp_modulus_scratch\n" ++
  "  mv a5, x23\n" ++
  "  la a6, modexp_output_scratch\n" ++
  "  jal x1, zkvm_modexp\n" ++
  "  bnez a0, .Lpse_fail\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  sd x23, 8(x15)\n" ++
  "  la x28, modexp_output_scratch\n" ++
  "  addi x29, x15, 16\n" ++
  "  mv x24, x23\n" ++
  ".Lmodexp_backend_frame_copy_loop_" ++ suffix ++ ":\n" ++
  "  beqz x24, .Lmodexp_backend_frame_copy_done_" ++ suffix ++ "\n" ++
  "  lbu x16, 0(x28)\n" ++
  "  sb x16, 0(x29)\n" ++
  "  addi x28, x28, 1\n" ++
  "  addi x29, x29, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  j .Lmodexp_backend_frame_copy_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_backend_frame_copy_done_" ++ suffix ++ ":\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  j .Lpse_ok\n" ++
  -- modexpReadLengthAsm hard-fail labels (select_price already validated)
  ".Lpse_bn254_fail_allot:\n" ++
  "  j .Lpse_fail\n"

end EvmAsm.Codegen
