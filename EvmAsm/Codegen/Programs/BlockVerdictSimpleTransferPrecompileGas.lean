/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPrecompileGas

  Active-precompile gas dispatch fragment for block_verdict simple-transfer handling.
-/

import EvmAsm.Codegen.Programs.PrecompileRuntime

namespace EvmAsm.Codegen

def blockVerdictSimpleTransferPrecompileGasAsmFor (ctxLabel : String) : String :=
  "  # Active precompile recipients have empty state-trie code but still execute. Detect them\n" ++
  "  # before the zero-value EOA shortcut so their execution gas reaches the exact gas arena.\n" ++
  ".Lbv_tx_gas_precharge_pc0_prefix:\n" ++
  -- Root and child routes fill the same descriptor.  The shared entry owns
  -- address classification and gas pricing; t2 is restored to the live MTx
  -- context before the route-local EOA checks below.
  "  la t0, precompile_shared_ctx; la t1, " ++ ctxLabel ++ "; addi t1, t1, 72; sd t1, 0(t0)\n" ++
  "  la t1, " ++ ctxLabel ++ "; ld t1, 56(t1); sd t1, 8(t0)\n" ++
  "  la t1, " ++ ctxLabel ++ "; ld t1, 64(t1); sd t1, 16(t0)\n" ++
  "  jal ra, precompile_shared_select_price\n" ++
  "  la t0, precompile_shared_selector; ld t3, 0(t0); la t2, " ++ ctxLabel ++ "\n" ++
  precompileSharedStatusFailAsm ".Lbv_simple_transfer_precompile_fail" ++
  "  beqz t3, .Lbv_tx_gas_precharge_value_check\n" ++
  precompileSelectorBranchesAsm "t3" "t4" true
    [ ("1", ".Lbv_simple_transfer_precompile_ecrecover")
    , ("2", ".Lbv_simple_transfer_precompile_sha256")
    , ("3", ".Lbv_simple_transfer_precompile_ripemd160")
    , ("4", ".Lbv_simple_transfer_precompile_identity")
    , ("5", ".Lbv_simple_transfer_precompile_modexp")
    , ("6", ".Lbv_simple_transfer_precompile_ecadd")
    , ("7", ".Lbv_simple_transfer_precompile_ecmul")
    , ("8", ".Lbv_simple_transfer_precompile_ecpairing")
    , ("9", ".Lbv_simple_transfer_precompile_blake2f")
    , ("10", ".Lbv_simple_transfer_precompile_point_eval")
    , ("11", ".Lbv_simple_transfer_precompile_bls_g1add")
    , ("12", ".Lbv_simple_transfer_precompile_bls_g1msm")
    , ("13", ".Lbv_simple_transfer_precompile_bls_g2add")
    , ("14", ".Lbv_simple_transfer_precompile_bls_g2msm")
    , ("15", ".Lbv_simple_transfer_precompile_bls_pairing")
    , ("16", ".Lbv_simple_transfer_precompile_bls_map_g1")
    , ("17", ".Lbv_simple_transfer_precompile_bls_map_g2")
    , ("256", ".Lbv_simple_transfer_precompile_p256") ] ++
  ".Lbv_tx_gas_precharge_value_check:\n" ++
  -- #11163: shared-body arm sets lane 2 before entering.  Falling through here
  -- means the recipient was not an active precompile — resume the bytecode
  -- loop (empty codeSize → STOP).
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
  "  la t0, precompile_shared_selector; ld t3, 0(t0); la t2, " ++ ctxLabel ++ "\n" ++
  "  beqz t3, .Lbv_mtx_precompile_not_active\n" ++
  precompileSelectorBranchesAsm "t3" "t4" true
    [ ("1", ".Lbv_simple_transfer_precompile_ecrecover")
    , ("2", ".Lbv_simple_transfer_precompile_sha256")
    , ("3", ".Lbv_simple_transfer_precompile_ripemd160")
    , ("4", ".Lbv_simple_transfer_precompile_identity")
    , ("5", ".Lbv_simple_transfer_precompile_modexp")
    , ("6", ".Lbv_simple_transfer_precompile_ecadd")
    , ("7", ".Lbv_simple_transfer_precompile_ecmul")
    , ("8", ".Lbv_simple_transfer_precompile_ecpairing")
    , ("9", ".Lbv_simple_transfer_precompile_blake2f")
    , ("10", ".Lbv_simple_transfer_precompile_point_eval")
    , ("11", ".Lbv_simple_transfer_precompile_bls_g1add")
    , ("12", ".Lbv_simple_transfer_precompile_bls_g1msm")
    , ("13", ".Lbv_simple_transfer_precompile_bls_g2add")
    , ("14", ".Lbv_simple_transfer_precompile_bls_g2msm")
    , ("15", ".Lbv_simple_transfer_precompile_bls_pairing")
    , ("16", ".Lbv_simple_transfer_precompile_bls_map_g1")
    , ("17", ".Lbv_simple_transfer_precompile_bls_map_g2")
    , ("256", ".Lbv_simple_transfer_precompile_p256") ] ++
  "  j .Lbv_mtx_precompile_not_active\n" ++
  ".Lbv_simple_transfer_precompile_ecrecover:\n" ++
  -- At depth zero the precompile's returndata is intentionally not materialized:
  -- execution-specs stores it only in `evm.output`/`MessageCallOutput.return_data`,
  -- while the transaction path consumes gas, refund, logs, error, and deletions
  -- to make the receipt and state transition.  There is no caller memory window
  -- or return-data consumer for a top-level transaction.  Keep ECRECOVER's
  -- recovery/output kernel on the child path, where CALL-family code consumes it.
  -- This selector is not the checked-system-call path: that path stages a runtime
  -- payload and enters `runtime_dispatcher_call` with `system_call_mode` enabled.
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_sha256:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2)\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ripemd160:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2)\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_identity:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2)\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_modexp:\n" ++
  -- As with ECRECOVER above, direct top-level MODEXP has no observable output
  -- consumer.  The child processor owns the shared computation because it must
  -- copy returndata to the CALL-family caller; this root route only needs the
  -- formula and exceptional-halt behavior that affect the transaction result.
  -- Match execution-specs' MODEXP decoder and EIP-2565/Amsterdam gas formula.
  -- Header bytes absent from calldata are zero; any length above 1024 is an
  -- exceptional halt and therefore consumes all remaining transaction gas.
  "  la t2, " ++ ctxLabel ++ "; ld a3, 56(t2); ld a4, 64(t2)\n" ++
  precompileSharedLoadCostAsm "t6" ++
  precompileSharedStatusFailAsm ".Lbv_simple_transfer_precompile_fail" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecadd:\n" ++
  -- Use the same zero-padded two-point validation as the child ECADD route.
  -- execution-specs' `alt_bn128_add` rejects invalid field elements or points
  -- with an exceptional halt, so a direct top-level precompile must not accept
  -- the length-correct but invalid input that the old root-only path ignored.
  "  la t2, " ++ ctxLabel ++ "; ld t5, 56(t2); ld t4, 64(t2)\n" ++
  stagePrecompileInputWindowFromAsm "bv_simple_transfer_ecadd_p1" "t5" "t4"
    precompileFrameBls12G1Input0Off 0 64 ++
  stagePrecompileInputWindowFromAsm "bv_simple_transfer_ecadd_p2" "t5" "t4"
    precompileFrameBls12G1Input1Off 64 64 ++
  precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
  precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  precompileKernelCallAsm "ra" "zkvm_bn254_g1_add" "a0"
    ".Lbv_simple_transfer_precompile_fail" "" "  " ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecmul:\n" ++
  -- A direct transaction to ecMul bypasses the opcode dispatcher, so run the
  -- same kernel validity gate as the CALL precompile path. The precompile
  -- zero-pads short input and ignores bytes beyond the first 96. Stage that
  -- exact window before calling the shared kernel validity gate.
  "  la t2, " ++ ctxLabel ++ "; ld t5, 56(t2); ld t4, 64(t2); la t3, evm_precompile_frame; li a0, 0\n" ++
  ".Lbv_simple_transfer_ecmul_zero:\n" ++
  "  li a1, 96; beq a0, a1, .Lbv_simple_transfer_ecmul_copy_init; add a2, t3, a0; sb zero, 0(a2); addi a0, a0, 1; j .Lbv_simple_transfer_ecmul_zero\n" ++
  ".Lbv_simple_transfer_ecmul_copy_init:\n" ++
  "  li a0, 0; li a1, 96; bleu t4, a1, .Lbv_simple_transfer_ecmul_copy; mv t4, a1\n" ++
  ".Lbv_simple_transfer_ecmul_copy:\n" ++
  "  beq a0, t4, .Lbv_simple_transfer_ecmul_run; add a1, t5, a0; lbu a2, 0(a1); add a1, t3, a0; sb a2, 0(a1); addi a0, a0, 1; j .Lbv_simple_transfer_ecmul_copy\n" ++
  ".Lbv_simple_transfer_ecmul_run:\n" ++
  "  mv a0, t3; addi a1, t3, 64; addi a2, t3, 128" ++
  precompileKernelCallAsm "ra" "zkvm_bn254_g1_mul" "a0"
    ".Lbv_simple_transfer_precompile_fail" "" "; " ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_ecpairing:\n" ++
  -- `alt_bn128_pairing_check` charges by complete 192-byte tuples, then
  -- raises an exceptional halt when a partial tuple remains.
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); li t4, 192; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail\n" ++
  -- Pairing validity is part of the precompile, not just its length formula.
  -- Reuse the child route's kernel: invalid field elements, off-curve points,
  -- and a non-subgroup G2 component take the same exceptional-halt route.
  "  la t2, " ++ ctxLabel ++ "; ld a0, 56(t2); ld t5, 64(t2); li t4, 192; divu a1, t5, t4\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  precompileKernelCallAsm "ra" "zkvm_bn254_pairing" "a0"
    ".Lbv_simple_transfer_precompile_fail" "" "  " ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2)\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_blake2f:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); li t4, 213; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  ld t5, 56(t2); lbu t6, 0(t5); slli t6, t6, 24; lbu t4, 1(t5); slli t4, t4, 16; or t6, t6, t4; lbu t4, 2(t5); slli t4, t4, 8; or t6, t6, t4; lbu t4, 3(t5); or t6, t6, t4\n" ++
  "  lbu t4, 212(t5); li t5, 1; bgtu t4, t5, .Lbv_simple_transfer_precompile_fail\n" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_point_eval:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); li t4, 192; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  -- A top-level transaction to an active precompile bypasses the opcode
  -- dispatcher, so validate the KZG input here as `run_precompile` does.  An
  -- invalid versioned hash or proof is an exceptional halt and consumes all
  -- transaction execution gas; only a valid proof leaves gas after the fixed
  -- 50000 charge.
  "  ld t5, 56(t2)\n" ++
  "  addi a0, t5, 96; li a1, 48; la a2, evm_precompile_frame; jal ra, zkvm_sha256\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 56(t2)\n" ++
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
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g1add:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); li t4, 256; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  ld a0, 56(t2)\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
  "  jal ra, zkvm_bls12_g1_add\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g1msm:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); beqz t5, .Lbv_simple_transfer_precompile_fail; li t4, 160; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail; mv x18, t5\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld a0, 56(t2); ld t5, 64(t2); li t4, 160; divu a1, t5, t4\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  "  jal ra, zkvm_bls12_g1_msm\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g2add:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); li t4, 512; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  ld a0, 56(t2)\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G2AddOutputOff ++
  "  jal ra, zkvm_bls12_g2_add\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_g2msm:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); beqz t5, .Lbv_simple_transfer_precompile_fail; li t4, 288; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail; mv x18, t5\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld a0, 56(t2); ld t5, 64(t2); li t4, 288; divu a1, t5, t4\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G2OutputOff ++
  "  jal ra, zkvm_bls12_g2_msm\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_pairing:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); beqz t5, .Lbv_simple_transfer_precompile_fail; li t4, 384; remu t3, t5, t4; bnez t3, .Lbv_simple_transfer_precompile_fail\n" ++
  -- The BLS pairing kernel performs the same decode, curve, and subgroup
  -- validation as the child precompile path.
  "  la t2, " ++ ctxLabel ++ "; ld a0, 56(t2); ld t5, 64(t2); li t4, 384; divu a1, t5, t4\n" ++
  precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
  "  jal ra, zkvm_bls12_pairing\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_map_g1:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); li t4, 64; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  ld a0, 56(t2)\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
  "  jal ra, zkvm_bls12_map_fp_to_g1\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_bls_map_g2:\n" ++
  "  la t2, " ++ ctxLabel ++ "; ld t5, 64(t2); li t4, 128; bne t5, t4, .Lbv_simple_transfer_precompile_fail\n" ++
  "  ld a0, 56(t2)\n" ++
  precompileFrameAddi "a1" precompileFrameBls12G2OutputOff ++
  "  jal ra, zkvm_bls12_map_fp2_to_g2\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_p256:\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_precompile_default:\n" ++
  "  li t6, 0\n" ++
  "  j .Lbv_simple_transfer_no_log_then_after_tx_gas_precharge\n"

def blockVerdictSimpleTransferPrecompileGasAsm : String :=
  blockVerdictSimpleTransferPrecompileGasAsmFor "bv_simple_transfer_tx"

end EvmAsm.Codegen
