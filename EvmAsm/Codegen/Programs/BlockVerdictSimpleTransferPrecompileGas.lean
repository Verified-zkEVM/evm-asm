/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPrecompileGas

  Active-precompile gas dispatch fragment for block_verdict simple-transfer handling.
-/

namespace EvmAsm.Codegen

private def blockVerdictModexpReadLengthAsm (fieldOff : Nat) (dstReg : String) : String :=
  "  li " ++ dstReg ++ ", 0; li a5, 0\n" ++
  ".Lbv_modexp_len_loop_" ++ toString fieldOff ++ ":\n" ++
  "  li a6, 32; beq a5, a6, .Lbv_modexp_len_done_" ++ toString fieldOff ++ "\n" ++
  "  addi a6, a5, " ++ toString fieldOff ++ "\n" ++
  "  bgeu a6, a4, .Lbv_modexp_len_missing_" ++ toString fieldOff ++ "\n" ++
  "  add a6, a3, a6; lbu a6, 0(a6)\n" ++
  "  j .Lbv_modexp_len_have_" ++ toString fieldOff ++ "\n" ++
  ".Lbv_modexp_len_missing_" ++ toString fieldOff ++ ":\n" ++
  "  li a6, 0\n" ++
  ".Lbv_modexp_len_have_" ++ toString fieldOff ++ ":\n" ++
  "  li a7, 30; bltu a5, a7, .Lbv_modexp_len_high_" ++ toString fieldOff ++ "\n" ++
  "  slli " ++ dstReg ++ ", " ++ dstReg ++ ", 8; or " ++ dstReg ++ ", " ++ dstReg ++ ", a6\n" ++
  "  j .Lbv_modexp_len_next_" ++ toString fieldOff ++ "\n" ++
  ".Lbv_modexp_len_high_" ++ toString fieldOff ++ ":\n" ++
  "  bnez a6, .Lbv_simple_transfer_precompile_fail\n" ++
  ".Lbv_modexp_len_next_" ++ toString fieldOff ++ ":\n" ++
  "  addi a5, a5, 1; j .Lbv_modexp_len_loop_" ++ toString fieldOff ++ "\n" ++
  ".Lbv_modexp_len_done_" ++ toString fieldOff ++ ":\n" ++
  "  li a6, 1024; bltu a6, " ++ dstReg ++ ", .Lbv_simple_transfer_precompile_fail\n"

def blockVerdictSimpleTransferPrecompileGasAsm : String :=
  "  # Active precompile recipients have empty state-trie code but still execute. Detect them\n" ++
  "  # before the zero-value EOA shortcut so their execution gas reaches the exact gas arena.\n" ++
  "  mv t0, t2; addi t0, t0, 72; li t1, 0\n" ++
  ".Lbv_tx_gas_precharge_pc0_prefix:\n" ++
  "  li t3, 18; beq t1, t3, .Lbv_tx_gas_precharge_pc0_low16\n" ++
  "  add t3, t0, t1; lbu t4, 0(t3); bnez t4, .Lbv_tx_gas_precharge_value_check\n" ++
  "  addi t1, t1, 1; j .Lbv_tx_gas_precharge_pc0_prefix\n" ++
  ".Lbv_tx_gas_precharge_pc0_low16:\n" ++
  "  lbu t3, 18(t0); lbu t4, 19(t0); slli t3, t3, 8; or t3, t3, t4\n" ++
  "  li t4, 1; bltu t3, t4, .Lbv_tx_gas_precharge_value_check\n" ++
  "  li t4, 1; beq t3, t4, .Lbv_simple_transfer_precompile_ecrecover\n" ++
  "  li t4, 2; beq t3, t4, .Lbv_simple_transfer_precompile_sha256\n" ++
  "  li t4, 3; beq t3, t4, .Lbv_simple_transfer_precompile_ripemd160\n" ++
  "  li t4, 4; beq t3, t4, .Lbv_simple_transfer_precompile_identity\n" ++
  "  li t4, 5; beq t3, t4, .Lbv_simple_transfer_precompile_modexp\n" ++
  "  li t4, 6; beq t3, t4, .Lbv_simple_transfer_precompile_ecadd\n" ++
  "  li t4, 7; beq t3, t4, .Lbv_simple_transfer_precompile_ecmul\n" ++
  "  li t4, 8; beq t3, t4, .Lbv_simple_transfer_precompile_ecpairing\n" ++
  "  li t4, 9; beq t3, t4, .Lbv_simple_transfer_precompile_blake2f\n" ++
  "  li t4, 10; beq t3, t4, .Lbv_simple_transfer_precompile_point_eval\n" ++
  "  li t4, 11; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g1add\n" ++
  "  li t4, 12; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g1msm\n" ++
  "  li t4, 13; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g2add\n" ++
  "  li t4, 14; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g2msm\n" ++
  "  li t4, 15; beq t3, t4, .Lbv_simple_transfer_precompile_bls_pairing\n" ++
  "  li t4, 16; beq t3, t4, .Lbv_simple_transfer_precompile_bls_map_g1\n" ++
  "  li t4, 17; beq t3, t4, .Lbv_simple_transfer_precompile_bls_map_g2\n" ++
  "  li t4, 256; beq t3, t4, .Lbv_simple_transfer_precompile_p256\n" ++
  ".Lbv_tx_gas_precharge_value_check:\n" ++
  -- The MTx empty-code route enters this shared active-precompile recognizer
  -- with its context copied into the scalar scratch. Falling through here
  -- means the recipient was not active, so resume indexed EOA settlement.
  "  la t0, bv_mtx_precompile_lane; ld t0, 0(t0); bnez t0, .Lbv_mtx_precompile_not_active\n" ++
  "  ld t0,  96(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 104(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 112(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 120(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  li t6, 0; j .Lbv_simple_transfer_no_log_then_after_tx_gas_precharge\n" ++
  ".Lbv_tx_gas_precharge_nonzero_value:\n" ++
  "  # The post-balance verifier below models an EOA simple transfer: sender\n" ++
  "  # final balance = precharge + unused intrinsic refund - value. For value\n" ++
  "  # transfers into contracts, bytecode execution spends additional gas, so\n" ++
  "  # leave the verdict to the state-root/BAL checks instead.\n" ++
  "  # Direct transfers to active precompiles also execute code despite having\n" ++
  "  # no state-trie code hash; skip this 21k-only verifier for them too.\n" ++
  "  mv t0, t2; addi t0, t0, 72; li t1, 0\n" ++
  ".Lbv_tx_gas_precharge_pc_prefix:\n" ++
  "  li t3, 18; beq t1, t3, .Lbv_tx_gas_precharge_pc_low16\n" ++
  "  add t3, t0, t1; lbu t4, 0(t3); bnez t4, .Lbv_tx_gas_precharge_not_precompile\n" ++
  "  addi t1, t1, 1; j .Lbv_tx_gas_precharge_pc_prefix\n" ++
  ".Lbv_tx_gas_precharge_pc_low16:\n" ++
  "  lbu t3, 18(t0); lbu t4, 19(t0); slli t3, t3, 8; or t3, t3, t4\n" ++
  "  li t4, 1; bltu t3, t4, .Lbv_tx_gas_precharge_not_precompile\n" ++
  "  li t4, 1; beq t3, t4, .Lbv_simple_transfer_precompile_ecrecover\n" ++
  "  li t4, 2; beq t3, t4, .Lbv_simple_transfer_precompile_sha256\n" ++
  "  li t4, 3; beq t3, t4, .Lbv_simple_transfer_precompile_ripemd160\n" ++
  "  li t4, 4; beq t3, t4, .Lbv_simple_transfer_precompile_identity\n" ++
  "  li t4, 5; beq t3, t4, .Lbv_simple_transfer_precompile_modexp\n" ++
  "  li t4, 6; beq t3, t4, .Lbv_simple_transfer_precompile_ecadd\n" ++
  "  li t4, 7; beq t3, t4, .Lbv_simple_transfer_precompile_ecmul\n" ++
  "  li t4, 8; beq t3, t4, .Lbv_simple_transfer_precompile_ecpairing\n" ++
  "  li t4, 9; beq t3, t4, .Lbv_simple_transfer_precompile_blake2f\n" ++
  "  li t4, 10; beq t3, t4, .Lbv_simple_transfer_precompile_point_eval\n" ++
  "  li t4, 11; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g1add\n" ++
  "  li t4, 12; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g1msm\n" ++
  "  li t4, 13; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g2add\n" ++
  "  li t4, 14; beq t3, t4, .Lbv_simple_transfer_precompile_bls_g2msm\n" ++
  "  li t4, 15; beq t3, t4, .Lbv_simple_transfer_precompile_bls_pairing\n" ++
  "  li t4, 16; beq t3, t4, .Lbv_simple_transfer_precompile_bls_map_g1\n" ++
  "  li t4, 17; beq t3, t4, .Lbv_simple_transfer_precompile_bls_map_g2\n" ++
  "  li t4, 256; beq t3, t4, .Lbv_simple_transfer_precompile_p256\n" ++
  "  j .Lbv_tx_gas_precharge_not_precompile\n" ++
  ".Lbv_simple_transfer_precompile_ecrecover:\n" ++
  "  li t6, 3000\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_sha256:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); addi t5, t5, 31; srli t5, t5, 5; li t6, 12; mul t6, t6, t5; addi t6, t6, 60\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ripemd160:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); addi t5, t5, 31; srli t5, t5, 5; li t6, 120; mul t6, t6, t5; addi t6, t6, 600\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_identity:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); addi t5, t5, 31; srli t5, t5, 5; li t6, 3; mul t6, t6, t5; addi t6, t6, 15\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_modexp:\n" ++
  -- Match execution-specs' MODEXP decoder and EIP-2565/Amsterdam gas formula.
  -- Header bytes absent from calldata are zero; any length above 1024 is an
  -- exceptional halt and therefore consumes all remaining transaction gas.
  "  la t2, bv_simple_transfer_tx; ld a3, 56(t2); ld a4, 64(t2)\n" ++
  blockVerdictModexpReadLengthAsm 0 "a0" ++
  blockVerdictModexpReadLengthAsm 32 "a1" ++
  blockVerdictModexpReadLengthAsm 64 "a2" ++
  -- complexity = 16 for max(baseLen, modulusLen) <= 32, otherwise
  -- 2 * ceil(maxLen / 8)^2.
  "  mv t3, a0; bgeu t3, a2, .Lbv_modexp_max_done; mv t3, a2\n" ++
  ".Lbv_modexp_max_done:\n" ++
  "  li t6, 16; li t4, 32; bgeu t4, t3, .Lbv_modexp_complex_done\n" ++
  "  addi t3, t3, 7; srli t3, t3, 3; mul t6, t3, t3; slli t6, t6, 1\n" ++
  ".Lbv_modexp_complex_done:\n" ++
  -- bitsPart = bit_length(first min(32, expLen) exponent bytes) - 1.
  -- Scan the zero-padded buffer for its first nonzero byte so no 256-bit
  -- temporary is needed.
  "  mv a5, a1; li t3, 32; bgeu t3, a5, .Lbv_modexp_head_len_done; mv a5, t3\n" ++
  ".Lbv_modexp_head_len_done:\n" ++
  "  li a6, 0; li a7, 0\n" ++
  ".Lbv_modexp_head_loop:\n" ++
  "  beq a6, a5, .Lbv_modexp_head_done\n" ++
  "  addi t3, a0, 96; add t3, t3, a6; li t4, 0; bgeu t3, a4, .Lbv_modexp_head_have\n" ++
  "  add t3, a3, t3; lbu t4, 0(t3)\n" ++
  ".Lbv_modexp_head_have:\n" ++
  "  bnez t4, .Lbv_modexp_head_nonzero; addi a6, a6, 1; j .Lbv_modexp_head_loop\n" ++
  ".Lbv_modexp_head_nonzero:\n" ++
  "  sub a7, a5, a6; addi a7, a7, -1; slli a7, a7, 3\n" ++
  ".Lbv_modexp_head_log_loop:\n" ++
  "  li t3, 2; bltu t4, t3, .Lbv_modexp_head_done; srli t4, t4, 1; addi a7, a7, 1; j .Lbv_modexp_head_log_loop\n" ++
  ".Lbv_modexp_head_done:\n" ++
  "  mv t5, a7; li t3, 32; bgeu t3, a1, .Lbv_modexp_iterations_min\n" ++
  "  addi t5, a1, -32; slli t5, t5, 4; add t5, t5, a7\n" ++
  ".Lbv_modexp_iterations_min:\n" ++
  "  bnez t5, .Lbv_modexp_iterations_done; li t5, 1\n" ++
  ".Lbv_modexp_iterations_done:\n" ++
  "  mul t6, t6, t5; li t4, 500; bgeu t6, t4, .Lbv_modexp_cost_done; mv t6, t4\n" ++
  ".Lbv_modexp_cost_done:\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecadd:\n" ++
  "  li t6, 150\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecmul:\n" ++
  -- A direct transaction to ecMul bypasses the opcode dispatcher, so run the
  -- same kernel validity gate as the CALL precompile path. The precompile
  -- zero-pads short input and ignores bytes beyond the first 96. Stage that
  -- exact window before calling the shared kernel validity gate.
  "  la t2, bv_simple_transfer_tx; ld t5, 56(t2); ld t4, 64(t2); la t3, evm_precompile_frame; li a0, 0\n" ++
  ".Lbv_simple_transfer_ecmul_zero:\n" ++
  "  li a1, 96; beq a0, a1, .Lbv_simple_transfer_ecmul_copy_init; add a2, t3, a0; sb zero, 0(a2); addi a0, a0, 1; j .Lbv_simple_transfer_ecmul_zero\n" ++
  ".Lbv_simple_transfer_ecmul_copy_init:\n" ++
  "  li a0, 0; li a1, 96; bleu t4, a1, .Lbv_simple_transfer_ecmul_copy; mv t4, a1\n" ++
  ".Lbv_simple_transfer_ecmul_copy:\n" ++
  "  beq a0, t4, .Lbv_simple_transfer_ecmul_run; add a1, t5, a0; lbu a2, 0(a1); add a1, t3, a0; sb a2, 0(a1); addi a0, a0, 1; j .Lbv_simple_transfer_ecmul_copy\n" ++
  ".Lbv_simple_transfer_ecmul_run:\n" ++
  "  mv a0, t3; addi a1, t3, 64; addi a2, t3, 128; jal ra, zkvm_bn254_g1_mul\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  "  li t6, 6000\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecpairing:\n" ++
  -- `alt_bn128_pairing_check` charges by complete 192-byte tuples, then
  -- raises an exceptional halt when a partial tuple remains.
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 192; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail; divu t5, t5, t4; li t6, 34000; mul t6, t6, t5; li t4, 45000; add t6, t6, t4\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_blake2f:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 213; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  ld t5, 56(t2); lbu t6, 0(t5); slli t6, t6, 24; lbu t4, 1(t5); slli t4, t4, 16; or t6, t6, t4; lbu t4, 2(t5); slli t4, t4, 8; or t6, t6, t4; lbu t4, 3(t5); or t6, t6, t4\n" ++
  "  lbu t4, 212(t5); li t5, 1; bgtu t4, t5, .Lbv_simple_transfer_precompile_fail\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_point_eval:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 192; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  -- A top-level transaction to an active precompile bypasses the opcode
  -- dispatcher, so validate the KZG input here as `run_precompile` does.  An
  -- invalid versioned hash or proof is an exceptional halt and consumes all
  -- transaction execution gas; only a valid proof leaves gas after the fixed
  -- 50000 charge.
  "  ld t5, 56(t2)\n" ++
  "  addi a0, t5, 96; li a1, 48; la a2, evm_precompile_frame; jal ra, zkvm_sha256\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 56(t2)\n" ++
  "  lbu t3, 0(t5); li t4, 1; bne t3, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  li t3, 1; la t4, evm_precompile_frame\n" ++
  ".Lbv_simple_transfer_point_eval_hash_loop:\n" ++
  "  li t2, 32; beq t3, t2, .Lbv_simple_transfer_point_eval_hash_ok\n" ++
  "  add t2, t5, t3; lbu a0, 0(t2); add t2, t4, t3; lbu a1, 0(t2)\n" ++
  "  bne a0, a1, .Lbv_simple_transfer_precompile_fail\n" ++
  "  addi t3, t3, 1; j .Lbv_simple_transfer_point_eval_hash_loop\n" ++
  ".Lbv_simple_transfer_point_eval_hash_ok:\n" ++
  "  addi a0, t5, 96; addi a1, t5, 32; addi a2, t5, 64; addi a3, t5, 144; addi a4, t4, 32\n" ++
  "  sb zero, 32(t4); jal ra, zkvm_kzg_point_eval\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  "  la t4, evm_precompile_frame; lbu t3, 32(t4); beqz t3, .Lbv_simple_transfer_precompile_fail\n" ++
  "  li t6, 50000\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g1add:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 256; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  li t6, 375\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g1msm:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); beqz t5, .Lbv_simple_transfer_precompile_fail; li t4, 160; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail; divu t5, t5, t4; li t6, 12000; mul t6, t6, t5\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g2add:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 512; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  li t6, 600\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g2msm:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); beqz t5, .Lbv_simple_transfer_precompile_fail; li t4, 288; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail; divu t5, t5, t4; li t6, 22500; mul t6, t6, t5\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_pairing:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); beqz t5, .Lbv_simple_transfer_precompile_fail; li t4, 384; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail; divu t5, t5, t4; li t6, 32600; mul t6, t6, t5; li t4, 37700; add t6, t6, t4\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_map_g1:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 64; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  li t6, 5500\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_map_g2:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 128; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  li t6, 23800\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_p256:\n" ++
  "  li t6, 6900\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_default:\n" ++
  "  li t6, 0\n" ++
  "  j .Lbv_simple_transfer_no_log_then_after_tx_gas_precharge\n"

end EvmAsm.Codegen
