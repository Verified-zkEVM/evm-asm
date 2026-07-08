/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPrecompileGas

  Active-precompile gas dispatch fragment for block_verdict simple-transfer handling.
-/

namespace EvmAsm.Codegen

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
  "  li t6, 500\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecadd:\n" ++
  "  li t6, 150\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecmul:\n" ++
  "  li t6, 6000\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecpairing:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 192; divu t5, t5, t4; li t6, 34000; mul t6, t6, t5; li t4, 45000; add t6, t6, t4\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_blake2f:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 213; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  ld t5, 56(t2); lbu t6, 0(t5); slli t6, t6, 24; lbu t4, 1(t5); slli t4, t4, 16; or t6, t6, t4; lbu t4, 2(t5); slli t4, t4, 8; or t6, t6, t4; lbu t4, 3(t5); or t6, t6, t4\n" ++
  "  lbu t4, 212(t5); li t5, 1; bgtu t4, t5, .Lbv_simple_transfer_precompile_fail\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_point_eval:\n" ++
  "  la t2, bv_simple_transfer_tx; ld t5, 64(t2); li t4, 192; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
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
