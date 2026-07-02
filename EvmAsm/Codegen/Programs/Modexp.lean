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
  "  add x31, x18, x31\n" ++
  "  lbu x16, 0(x31)\n" ++
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
  "  add x31, x18, x31\n" ++
  "  lbu x16, 0(x31)\n" ++
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
  "  add x31, x18, x31\n" ++
  "  lbu x16, 0(x31)\n" ++
  "  j .Lmodexp_stage_" ++ name ++ "_have_" ++ suffix ++ "\n" ++
  ".Lmodexp_stage_" ++ name ++ "_missing_" ++ suffix ++ ":\n" ++
  "  li x16, 0\n" ++
  ".Lmodexp_stage_" ++ name ++ "_have_" ++ suffix ++ ":\n" ++
  "  sb x16, 0(x28)\n" ++
  "  addi x28, x28, 1\n" ++
  "  addi x29, x29, 1\n" ++
  "  j .Lmodexp_stage_" ++ name ++ "_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_stage_" ++ name ++ "_done_" ++ suffix ++ ":\n"

def modexpPrecompileGasAsm
    (chargePrecompileGasAsm : String → String → String)
    (suffix : String)
    (inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x18, x13, x18\n" ++
  modexpReadLengthAsm suffix 0 "x5" ++
  modexpReadLengthAsm suffix 32 "x22" ++
  modexpReadLengthAsm suffix 64 "x23" ++
  "  mv x24, x5\n" ++
  "  bgeu x24, x23, .Lmodexp_max_done_" ++ suffix ++ "\n" ++
  "  mv x24, x23\n" ++
  ".Lmodexp_max_done_" ++ suffix ++ ":\n" ++
  "  addi x25, x24, 7\n" ++
  "  srli x25, x25, 3\n" ++
  "  li x31, 32\n" ++
  "  bltu x31, x24, .Lmodexp_complex_large_" ++ suffix ++ "\n" ++
  "  li x26, 16\n" ++
  "  j .Lmodexp_complex_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_complex_large_" ++ suffix ++ ":\n" ++
  "  mul x26, x25, x25\n" ++
  "  slli x26, x26, 1\n" ++
  ".Lmodexp_complex_done_" ++ suffix ++ ":\n" ++
  "  li x27, 0\n" ++
  "  li x30, 0\n" ++
  "  mv x28, x22\n" ++
  "  li x31, 32\n" ++
  "  bgeu x31, x28, .Lmodexp_head_len_done_" ++ suffix ++ "\n" ++
  "  mv x28, x31\n" ++
  ".Lmodexp_head_len_done_" ++ suffix ++ ":\n" ++
  "  li x29, 0\n" ++
  ".Lmodexp_head_loop_" ++ suffix ++ ":\n" ++
  "  beq x29, x28, .Lmodexp_head_done_zero_" ++ suffix ++ "\n" ++
  "  addi x31, x5, 96\n" ++
  "  add x31, x31, x29\n" ++
  "  bgeu x31, x17, .Lmodexp_head_missing_" ++ suffix ++ "\n" ++
  "  add x31, x18, x31\n" ++
  "  lbu x16, 0(x31)\n" ++
  "  j .Lmodexp_head_have_byte_" ++ suffix ++ "\n" ++
  ".Lmodexp_head_missing_" ++ suffix ++ ":\n" ++
  "  li x16, 0\n" ++
  ".Lmodexp_head_have_byte_" ++ suffix ++ ":\n" ++
  "  bnez x16, .Lmodexp_head_nonzero_" ++ suffix ++ "\n" ++
  "  addi x29, x29, 1\n" ++
  "  j .Lmodexp_head_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_head_nonzero_" ++ suffix ++ ":\n" ++
  "  li x30, 1\n" ++
  "  sub x27, x28, x29\n" ++
  "  addi x27, x27, -1\n" ++
  "  slli x27, x27, 3\n" ++
  modexpByteLog2Asm suffix ++
  ".Lmodexp_head_done_zero_" ++ suffix ++ ":\n" ++
  ".Lmodexp_log_done_" ++ suffix ++ ":\n" ++
  "  li x31, 32\n" ++
  "  bltu x31, x22, .Lmodexp_iter_large_exp_" ++ suffix ++ "\n" ++
  "  beqz x30, .Lmodexp_iter_zero_head_" ++ suffix ++ "\n" ++
  "  mv x28, x27\n" ++
  "  j .Lmodexp_iter_max_" ++ suffix ++ "\n" ++
  ".Lmodexp_iter_large_exp_" ++ suffix ++ ":\n" ++
  "  addi x28, x22, -32\n" ++
  "  slli x28, x28, 4\n" ++
  "  add x28, x28, x27\n" ++
  "  j .Lmodexp_iter_max_" ++ suffix ++ "\n" ++
  ".Lmodexp_iter_zero_head_" ++ suffix ++ ":\n" ++
  "  li x28, 0\n" ++
  ".Lmodexp_iter_max_" ++ suffix ++ ":\n" ++
  "  bnez x28, .Lmodexp_iter_done_" ++ suffix ++ "\n" ++
  "  li x28, 1\n" ++
  ".Lmodexp_iter_done_" ++ suffix ++ ":\n" ++
  "  mul x16, x26, x28\n" ++
  "  li x31, 500\n" ++
  "  bgeu x16, x31, .Lmodexp_cost_done_" ++ suffix ++ "\n" ++
  "  mv x16, x31\n" ++
  ".Lmodexp_cost_done_" ++ suffix ++ ":\n" ++
  chargePrecompileGasAsm "x16" "x31" ++
  "  or x24, x5, x23\n" ++
  "  beqz x24, 7b\n" ++
  "  beqz x23, 7b\n" ++
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
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  mv x24, x23\n" ++
  "  bgeu x22, x24, .Lmodexp_copy_len_done_" ++ suffix ++ "\n" ++
  "  mv x24, x22\n" ++
  ".Lmodexp_copy_len_done_" ++ suffix ++ ":\n" ++
  "  beqz x24, 7b\n" ++
  "  addi x28, x15, 16\n" ++
  "  ld x29, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x29, x13, x29\n" ++
  ".Lmodexp_copy_loop_" ++ suffix ++ ":\n" ++
  "  lbu x16, 0(x28)\n" ++
  "  sb x16, 0(x29)\n" ++
  "  addi x28, x28, 1\n" ++
  "  addi x29, x29, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  bnez x24, .Lmodexp_copy_loop_" ++ suffix ++ "\n" ++
  "  j 7b\n" ++
  ".Lmodexp_backend_" ++ suffix ++ ":\n" ++
  "  li x30, 96\n" ++
  modexpStageComponentAsm suffix "base" "x30" "x5" "modexp_base_scratch" ++
  "  add x30, x30, x5\n" ++
  modexpStageComponentAsm suffix "exp" "x30" "x22" "modexp_exp_scratch" ++
  "  add x30, x30, x22\n" ++
  modexpStageComponentAsm suffix "modulus" "x30" "x23" "modexp_modulus_scratch" ++
  "  mv s9, x13\n" ++
  "  mv s10, x10\n" ++
  "  mv s11, x12\n" ++
  "  la a0, modexp_base_scratch\n" ++
  "  mv a1, x5\n" ++
  "  la a2, modexp_exp_scratch\n" ++
  "  mv a3, x22\n" ++
  "  la a4, modexp_modulus_scratch\n" ++
  "  mv a5, x23\n" ++
  "  la a6, modexp_output_scratch\n" ++
  "  jal x1, zkvm_modexp\n" ++
  "  mv t6, a0\n" ++
  "  mv x13, s9\n" ++
  "  mv x10, s10\n" ++
  "  mv x12, s11\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  bnez t6, .L" ++ suffix ++ "_bn254_fail_allot\n" ++
  "  sd x23, 8(x15)\n" ++
  "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  mv x24, x23\n" ++
  "  bgeu x22, x24, .Lmodexp_backend_copy_len_done_" ++ suffix ++ "\n" ++
  "  mv x24, x22\n" ++
  ".Lmodexp_backend_copy_len_done_" ++ suffix ++ ":\n" ++
  "  beqz x24, 7b\n" ++
  "  la x28, modexp_output_scratch\n" ++
  "  ld x29, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x29, x13, x29\n" ++
  ".Lmodexp_backend_copy_loop_" ++ suffix ++ ":\n" ++
  "  lbu x16, 0(x28)\n" ++
  "  sb x16, 0(x29)\n" ++
  "  addi x28, x28, 1\n" ++
  "  addi x29, x29, 1\n" ++
  "  addi x24, x24, -1\n" ++
  "  bnez x24, .Lmodexp_backend_copy_loop_" ++ suffix ++ "\n" ++
  "  j 7b\n"

end EvmAsm.Codegen
