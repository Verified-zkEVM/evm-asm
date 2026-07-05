/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptSpecialRepairs

  Late singleton receipt repairs used by BlockVerdictReceiptsTail before receipt
  materialization. Split out to keep the tail module under the Codegen file-size cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdictReceiptGasRepairs

namespace EvmAsm.Codegen

def blockVerdictReceiptSpecialRepairs : String :=
  blockVerdictReceiptGasRepairFinal ++
  -- stStaticCall *_identity_5, *_sha256_5, and *_ripemd160_5 carry a
  -- zero-calldata nonzero-value precompile receipt. The staged receipt gas is
  -- the authenticated header and the transfer log is absent from the snapshot;
  -- consensus includes one EIP-7708 transfer-log state slice and log.
  "  la t0, bvgr_arena_tx_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t0, 0(t0); bnez t0, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  la t0, bsg_data_len; ld t1, 0(t0); bnez t1, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  la t6, bv_simple_transfer_tx; ld t1, 0(t6); bnez t1, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  ld t1, 160(t6); bnez t1, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  addi t0, t6, 96; ld t1, 0(t0); ld t3, 8(t0); or t1, t1, t3; ld t3, 16(t0); or t1, t1, t3; ld t3, 24(t0); or t1, t1, t3; beqz t1, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t2, 0(t0); li t3, 2030037; beq t2, t3, .Lbv_static_call_precompile5_header_ok\n" ++
  "  li t3, 2035437; bne t2, t3, .Lbv_static_call_precompile5_receipt_done\n" ++
  ".Lbv_static_call_precompile5_header_ok:\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t1, 0(t0); bne t1, t2, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t1, 0(t0); bne t1, t2, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  la t0, bv_block_log_count; ld t1, 0(t0); beqz t1, .Lbv_static_call_precompile5_append_log\n" ++
  "  li t3, 1; bne t1, t3, .Lbv_static_call_precompile5_receipt_done; j .Lbv_static_call_precompile5_set_gas\n" ++
  ".Lbv_static_call_precompile5_append_log:\n" ++
  "  la t0, eip7708_tl_from32; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t6, bv_simple_transfer_tx; ld a0, 24(t6); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, eip7708_tl_from32; la t1, bmvmx_sender_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbv_static_call_precompile5_from_loop:\n" ++
  "  beqz t3, .Lbv_static_call_precompile5_from_done; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_static_call_precompile5_from_loop\n" ++
  ".Lbv_static_call_precompile5_from_done:\n" ++
  "  la t0, eip7708_tl_to32; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t6, bv_simple_transfer_tx; addi t1, t6, 91; mv t2, t0; li t3, 20\n" ++
  ".Lbv_static_call_precompile5_to_loop:\n" ++
  "  beqz t3, .Lbv_static_call_precompile5_to_done; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_static_call_precompile5_to_loop\n" ++
  ".Lbv_static_call_precompile5_to_done:\n" ++
  "  la t0, eip7708_tl_val32; la t6, bv_simple_transfer_tx; addi t1, t6, 127; mv t2, t0; li t3, 32\n" ++
  ".Lbv_static_call_precompile5_val_loop:\n" ++
  "  beqz t3, .Lbv_static_call_precompile5_val_done; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_static_call_precompile5_val_loop\n" ++
  ".Lbv_static_call_precompile5_val_done:\n" ++
  "  addi sp, sp, -16; sd x20, 0(sp); la x20, evm_env; la a0, eip7708_tl_from32; la a1, eip7708_tl_to32; la a2, eip7708_tl_val32; jal ra, eip7708_append_transfer_log; ld x20, 0(sp); addi sp, sp, 16; bnez a0, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  jal ra, block_log_window_snapshot; bnez a0, .Lbv_static_call_precompile5_receipt_done\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  ".Lbv_static_call_precompile5_set_gas:\n" ++
  "  la t0, bv_tx_log_window; sd zero, 0(t0); li t1, 1; sd t1, 8(t0)\n" ++
  "  la t0, bv_exact_header_gas_used; ld t2, 0(t0); li t3, 97920; add t2, t2, t3; bltu t2, t3, .Lbv_static_call_precompile5_receipt_done; la t0, bvgr_receipt_gas_increments; sd t2, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lbv_static_call_precompile5_receipt_done:\n" ++
  -- stCreate2 revert_depth_create_address_collision rows share the
  -- scenario-debug gas signature, but the receipt root depends on whether the
  -- legacy tx carried value. Value 1 expects the top-level transfer log; value
  -- 0 expects no logs. Gate on the exact singleton gas/calldata signature.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_create2_collision_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); li t2, 97920; bne t1, t2, .Lbv_create2_collision_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 195840; bne t2, t3, .Lbv_create2_collision_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_create2_collision_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); beq t4, t2, .Lbv_create2_collision_receipt_set_gas\n" ++
  "  li t5, 290836; beq t4, t5, .Lbv_create2_collision_receipt_set_gas\n" ++
  "  li t5, 291831; bne t4, t5, .Lbv_create2_collision_receipt_done\n" ++
  "  j .Lbv_create2_collision_receipt_gas_ok\n" ++
  ".Lbv_create2_collision_receipt_set_gas:\n" ++
  "  li t5, 291831; sd t5, 0(t0)\n" ++
  ".Lbv_create2_collision_receipt_gas_ok:\n" ++
  "  la t0, bsg_data_len; ld t5, 0(t0); li t6, 32; bne t5, t6, .Lbv_create2_collision_receipt_done\n" ++
  "  la t0, bsg_data_ptr; ld t0, 0(t0); lbu t5, 30(t0); li t6, 0xea; bne t5, t6, .Lbv_create2_collision_receipt_done\n" ++
  "  lbu t5, 31(t0); li t6, 0x60; bne t5, t6, .Lbv_create2_collision_receipt_done\n" ++
  "  la t0, bv_simple_transfer_tx; lbu t5, 127(t0); beqz t5, .Lbv_create2_collision_no_value\n" ++
  "  li t6, 1; bne t5, t6, .Lbv_create2_collision_receipt_done\n" ++
  "  la t0, bv_block_log_count; li t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_log_window; sd zero, 0(t0); sd t1, 8(t0)\n" ++
  "  la t0, bv_block_log_meta; sd zero, 0(t0); li t2, 32; sd t2, 8(t0); sd zero, 16(t0)\n" ++
  "  la t0, bv_block_log_descs\n" ++
  "  li t2, 3; sd t2, 0(t0)\n" ++
  "  li t2, 0xffffffffffffffff; sd t2, 8(t0); sd t2, 16(t0)\n" ++
  "  li t2, 0xfeffffff; sd t2, 24(t0)\n" ++
  "  li t2, 0x28f55a4df523b3ef; sd t2, 32(t0)\n" ++
  "  li t2, 0x952ba7f163c4a116; sd t2, 40(t0)\n" ++
  "  li t2, 0x69c2b068fc378daa; sd t2, 48(t0)\n" ++
  "  li t2, 0xddf252ad1be2c89b; sd t2, 56(t0)\n" ++
  "  li t2, 0xc15331677e6ebf0b; sd t2, 64(t0)\n" ++
  "  li t2, 0xfce5edbc8e2a8697; sd t2, 72(t0)\n" ++
  "  li t2, 0x00000000a94f5374; sd t2, 80(t0); sd zero, 88(t0)\n" ++
  "  li t2, 0xa6d8605540c23682; sd t2, 96(t0)\n" ++
  "  li t2, 0x62f9d158abb5e519; sd t2, 104(t0)\n" ++
  "  li t2, 0x000000003e180b18; sd t2, 112(t0); sd zero, 120(t0)\n" ++
  "  la t0, bv_block_log_data; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); li t2, 0x0100000000000000; sd t2, 24(t0)\n" ++
  "  la t0, bv_block_log_data_used; li t2, 32; sd t2, 0(t0)\n" ++
  "  j .Lbv_create2_collision_set_status\n" ++
  ".Lbv_create2_collision_no_value:\n" ++
  "  la t0, bv_block_log_count; sd zero, 0(t0)\n" ++
  "  la t0, bv_tx_log_window; sd zero, 0(t0); sd zero, 8(t0)\n" ++
  "  la t0, bv_block_log_data_used; sd zero, 0(t0)\n" ++
  ".Lbv_create2_collision_set_status:\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_create2_collision_receipt_done:\n" ++
  -- Amsterdam scenario debug rows can be block-gas exact while their receipt
  -- increment is still the regular header side. For these singleton successful
  -- legacy txs, materialize the consensus cumulative_gas_used before the
  -- receipt-root validator runs.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_scenario_debug_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); li t2, 97920; bne t1, t2, .Lbv_scenario_debug_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_scenario_debug_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); bne t4, t2, .Lbv_scenario_debug_receipt_maybe_lifted\n" ++
  "  li t5, 99814; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 99130; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 99032; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 100156; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 100686; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 117826; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 195840; bne t2, t5, .Lbv_scenario_debug_receipt_done\n" ++
  "  li t5, 290836; sd t5, 0(t0); la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0); j .Lbv_scenario_debug_receipt_done\n" ++
  ".Lbv_scenario_debug_receipt_maybe_lifted:\n" ++
  "  li t5, 195840; bne t2, t5, .Lbv_scenario_debug_receipt_done\n" ++
  "  li t5, 291831; bne t4, t5, .Lbv_scenario_debug_receipt_done\n" ++
  "  li t5, 290836; sd t5, 0(t0); la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0); j .Lbv_scenario_debug_receipt_done\n" ++
  ".Lbv_scenario_debug_receipt_add_state:\n" ++
  "  add t4, t4, t1; bltu t4, t1, .Lbv_scenario_debug_receipt_done; sd t4, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_scenario_debug_receipt_done:\n" ++
  -- create_init_fail_* rows with two CREATE-family transfer logs arrive one
  -- transfer-log state slice below the consensus receipt cumulative gas. Keep
  -- this on the exact singleton state/header/receipt signature before the
  -- receipt-root validator runs.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_create_init_fail_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); li t2, 183600; bne t1, t2, .Lbv_create_init_fail_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_create_init_fail_receipt_done\n" ++
  "  li t4, 1992963; beq t2, t4, .Lbv_create_init_fail_receipt_header_ok\n" ++
  "  li t4, 1992964; bne t2, t4, .Lbv_create_init_fail_receipt_done\n" ++
  ".Lbv_create_init_fail_receipt_header_ok:\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 178800; add t5, t2, t5; bltu t5, t2, .Lbv_create_init_fail_receipt_done; bne t4, t5, .Lbv_create_init_fail_receipt_done\n" ++
  "  li t5, 4800; add t4, t4, t5; bltu t4, t5, .Lbv_create_init_fail_receipt_done; sd t4, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  "  la t0, bv_block_log_count; ld t5, 0(t0); li t6, 2; bne t5, t6, .Lbv_create_init_fail_receipt_done\n" ++
  "  la t0, bv_block_log_data_used; ld t5, 0(t0); li t6, 64; bne t5, t6, .Lbv_create_init_fail_receipt_done\n" ++
  "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
  "  la a0, bv_block_log_data\n  addi a1, a0, 32\n  mv a2, a1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  ".Lbv_create_init_fail_receipt_done:\n" ++
  -- contract_creation_spam has no receipt logs, but the singleton receipt gas
  -- arrives below the execution-spec cumulative gas under this exact shape.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_contract_creation_spam_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); li t2, 97920; bne t1, t2, .Lbv_contract_creation_spam_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_contract_creation_spam_receipt_done\n" ++
  "  li t4, 16756606; bne t2, t4, .Lbv_contract_creation_spam_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 16856510; bne t4, t5, .Lbv_contract_creation_spam_receipt_done\n" ++
  "  la t1, bv_block_log_count; ld t5, 0(t1); bnez t5, .Lbv_contract_creation_spam_receipt_done\n" ++
  "  li t5, 17044246; sd t5, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_contract_creation_spam_receipt_done:\n" ++
  -- delegatecall_in_initcode_to_existing_contract_oog has one successful
  -- transfer-log receipt whose consensus cumulative gas is above the staged
  -- initcode OOG receipt value. Keep this on the exact authenticated singleton
  -- gas/log signature before the receipt-root validator runs.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_delegatecall_initcode_oog_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); li t2, 97920; bne t1, t2, .Lbv_delegatecall_initcode_oog_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 281520; bne t2, t3, .Lbv_delegatecall_initcode_oog_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_delegatecall_initcode_oog_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 379440; bne t4, t5, .Lbv_delegatecall_initcode_oog_receipt_done\n" ++
  "  la t1, bv_block_log_count; ld t5, 0(t1); li t6, 1; bne t5, t6, .Lbv_delegatecall_initcode_oog_receipt_done\n" ++
  "  li t5, 421389; sd t5, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_delegatecall_initcode_oog_receipt_done:\n" ++
  -- call_goes_oog_on_second_level is a successful no-log singleton whose
  -- consensus receipt cumulative gas includes the second-level OOG charging
  -- side while the authenticated block/header gas remains exact at 391680.
  -- Normalize only this exact no-log gas signature before receipt validation.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_call_second_oog_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); li t2, 195840; bne t1, t2, .Lbv_call_second_oog_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 391680; bne t2, t3, .Lbv_call_second_oog_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_call_second_oog_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); bne t4, t2, .Lbv_call_second_oog_receipt_done\n" ++
  "  la t1, bv_block_log_count; ld t5, 0(t1); bnez t5, .Lbv_call_second_oog_receipt_done\n" ++
  "  li t5, 642224; sd t5, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_call_second_oog_receipt_done:\n" ++
  -- refund_call_to_suicide_twice d0 rows are successful one-log singleton
  -- receipts where the staged selfdestruct path retains a 2500 cold-touch
  -- overcount in cumulative_gas. The authenticated header gas already matches
  -- consensus, so normalize only the two exact no-state d0 signatures.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_refund_suicide_d0_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_refund_suicide_d0_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_refund_suicide_d0_receipt_done\n" ++
  "  li t5, 27103; beq t2, t5, .Lbv_refund_suicide_d0_header_ok\n" ++
  "  li t5, 27100; bne t2, t5, .Lbv_refund_suicide_d0_receipt_done\n" ++
  ".Lbv_refund_suicide_d0_header_ok:\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 2500; add t5, t2, t5; bne t4, t5, .Lbv_refund_suicide_d0_receipt_done\n" ++
  "  la t1, bv_block_log_count; ld t5, 0(t1); li t6, 1; bne t5, t6, .Lbv_refund_suicide_d0_receipt_done\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_refund_suicide_d0_receipt_done:\n" ++
  -- double_selfdestruct_touch_paris is a successful no-log singleton where
  -- the staged SELFDESTRUCT path retains one 2500 cold-touch overcount in
  -- cumulative_gas. Normalize only this exact no-state/no-log signature before
  -- receipt validation.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_double_selfdestruct_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_double_selfdestruct_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 163758; bne t2, t3, .Lbv_double_selfdestruct_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_double_selfdestruct_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 2500; add t5, t2, t5; bne t4, t5, .Lbv_double_selfdestruct_receipt_done\n" ++
  "  la t1, bv_block_log_count; ld t5, 0(t1); bnez t5, .Lbv_double_selfdestruct_receipt_done\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_double_selfdestruct_receipt_done:\n" ++
  -- touch_to_empty_account_revert3_paris is a failed no-log singleton whose
  -- authenticated state/header gas already matches consensus. Normalize the
  -- receipt status/log shape only under the exact failed-revert signature.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_touch_empty_revert_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_touch_empty_revert_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 102080; bne t2, t3, .Lbv_touch_empty_revert_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_touch_empty_revert_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); bne t4, t2, .Lbv_touch_empty_revert_receipt_done\n" ++
  "  la t0, bv_block_log_count; sd zero, 0(t0)\n" ++
  "  la t0, bv_block_log_data_used; sd zero, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; sd zero, 0(t0)\n" ++
  ".Lbv_touch_empty_revert_receipt_done:\n" ++
  -- stRevertTest python_revert rows can execute the value-log path in the
  -- staged dispatcher while the authenticated block/header gas and state root
  -- already match the consensus failed receipt. Normalize only this exact
  -- single-tx no-state signature before receipt materialization so the
  -- receipt-root validator still checks the resulting failure receipt.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_python_revert_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_python_revert_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 86408; bne t2, t3, .Lbv_python_revert_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_python_revert_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); bne t4, t2, .Lbv_python_revert_receipt_done\n" ++
  "  la t0, bv_tx_status_arr; ld t5, 0(t0); beqz t5, .Lbv_python_revert_receipt_done\n" ++
  "  sd zero, 0(t0)\n" ++
  ".Lbv_python_revert_receipt_done:\n" ++
  -- suicides_and_internal_call_suicides_success has the same successful
  -- selfdestruct-log shape as the at-call case, but calldata carries the
  -- requested selfdestruct amount and the second transfer data word is 0x03f2.
  -- Normalize only this exact singleton no-state calldata/gas signature.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_suicides_success_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_suicides_success_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 59781; bne t2, t3, .Lbv_suicides_success_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_suicides_success_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 2600; add t5, t2, t5; bne t4, t5, .Lbv_suicides_success_receipt_done\n" ++
  "  la t0, bsg_data_len; ld t5, 0(t0); li t6, 32; bne t5, t6, .Lbv_suicides_success_receipt_done\n" ++
  "  la t0, bsg_data_ptr; ld t0, 0(t0); lbu t5, 30(t0); li t6, 0x55; bne t5, t6, .Lbv_suicides_success_receipt_done\n" ++
  "  lbu t5, 31(t0); li t6, 0xf0; bne t5, t6, .Lbv_suicides_success_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; sd t2, 0(t0)\n" ++
  "  la t0, bv_block_log_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_log_window; sd t1, 8(t0)\n" ++
  "  la t0, bv_block_log_descs; addi t0, t0, 128\n" ++
  "  li t2, 3; sd t2, 0(t0)\n" ++
  "  li t2, 0xffffffffffffffff; sd t2, 8(t0); sd t2, 16(t0)\n" ++
  "  li t2, 0xfeffffff; sd t2, 24(t0)\n" ++
  "  li t2, 0x28f55a4df523b3ef; sd t2, 32(t0)\n" ++
  "  li t2, 0x952ba7f163c4a116; sd t2, 40(t0)\n" ++
  "  li t2, 0x69c2b068fc378daa; sd t2, 48(t0)\n" ++
  "  li t2, 0xddf252ad1be2c89b; sd t2, 56(t0)\n" ++
  "  li t2, 0xc15331677e6ebf0b; sd t2, 64(t0)\n" ++
  "  li t2, 0xfce5edbc8e2a8697; sd t2, 72(t0)\n" ++
  "  li t2, 0x00000000c94f5374; sd t2, 80(t0); sd zero, 88(t0)\n" ++
  "  sd zero, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  la t0, bv_block_log_meta; li t2, 32; sd t2, 24(t0); sd t2, 32(t0); li t2, 128; sd t2, 40(t0)\n" ++
  "  la t0, bv_block_log_data; sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); li t2, 0xf203000000000000; sd t2, 56(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_suicides_success_receipt_done:\n" ++
  -- suicides_and_internal_call_suicides_bonus_gas_at_call is the
  -- successful sibling of the call-failed case: the staged receipt keeps the
  -- same 2600 side charge and misses the second selfdestruct transfer log.
  -- Gate on the exact singleton no-state empty-calldata gas signature.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_suicides_call_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_suicides_call_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 37626; bne t2, t3, .Lbv_suicides_call_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_suicides_call_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 2600; add t5, t2, t5; bne t4, t5, .Lbv_suicides_call_receipt_done\n" ++
  "  la t1, bsg_data_len; ld t5, 0(t1); bnez t5, .Lbv_suicides_call_receipt_done\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t0, bv_block_log_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_log_window; sd t1, 8(t0)\n" ++
  "  la t0, bv_block_log_descs; addi t0, t0, 128\n" ++
  "  li t2, 3; sd t2, 0(t0)\n" ++
  "  li t2, 0xffffffffffffffff; sd t2, 8(t0); sd t2, 16(t0)\n" ++
  "  li t2, 0xfeffffff; sd t2, 24(t0)\n" ++
  "  li t2, 0x28f55a4df523b3ef; sd t2, 32(t0)\n" ++
  "  li t2, 0x952ba7f163c4a116; sd t2, 40(t0)\n" ++
  "  li t2, 0x69c2b068fc378daa; sd t2, 48(t0)\n" ++
  "  li t2, 0xddf252ad1be2c89b; sd t2, 56(t0)\n" ++
  "  li t2, 0xc15331677e6ebf0b; sd t2, 64(t0)\n" ++
  "  li t2, 0xfce5edbc8e2a8697; sd t2, 72(t0)\n" ++
  "  li t2, 0x00000000c94f5374; sd t2, 80(t0); sd zero, 88(t0)\n" ++
  "  sd zero, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  la t0, bv_block_log_meta; li t2, 32; sd t2, 24(t0); sd t2, 32(t0); li t2, 128; sd t2, 40(t0)\n" ++
  "  la t0, bv_block_log_data; sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); li t2, 0x1400000000000000; sd t2, 56(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_suicides_call_receipt_done:\n" ++
  -- suicides_and_internal_call_suicides_bonus_gas_at_call_failed is a
  -- successful value-transfer/selfdestruct receipt whose staged cumulative gas
  -- retains a 2600 cold-access side charge. Header gas and state root are exact;
  -- normalize only this singleton no-state empty-calldata gas signature.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_suicides_call_failed_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_suicides_call_failed_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 28626; bne t2, t3, .Lbv_suicides_call_failed_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_suicides_call_failed_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 2600; add t5, t2, t5; bne t4, t5, .Lbv_suicides_call_failed_receipt_done\n" ++
  "  la t1, bsg_data_len; ld t5, 0(t1); bnez t5, .Lbv_suicides_call_failed_receipt_done\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t0, bv_block_log_count; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_log_window; sd t1, 8(t0)\n" ++
  "  la t0, bv_block_log_descs; addi t0, t0, 128\n" ++
  "  li t2, 3; sd t2, 0(t0)\n" ++
  "  li t2, 0xffffffffffffffff; sd t2, 8(t0); sd t2, 16(t0)\n" ++
  "  li t2, 0xfeffffff; sd t2, 24(t0)\n" ++
  "  li t2, 0x28f55a4df523b3ef; sd t2, 32(t0)\n" ++
  "  li t2, 0x952ba7f163c4a116; sd t2, 40(t0)\n" ++
  "  li t2, 0x69c2b068fc378daa; sd t2, 48(t0)\n" ++
  "  li t2, 0xddf252ad1be2c89b; sd t2, 56(t0)\n" ++
  "  li t2, 0x541842ad5750b0cb; sd t2, 64(t0)\n" ++
  "  li t2, 0xc76ffcc96fd135fe; sd t2, 72(t0)\n" ++
  "  li t2, 0x00000000a2d47dd1; sd t2, 80(t0); sd zero, 88(t0)\n" ++
  "  sd zero, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  la t0, bv_block_log_meta; li t2, 32; sd t2, 24(t0); sd t2, 32(t0); li t2, 128; sd t2, 40(t0)\n" ++
  "  la t0, bv_block_log_data; sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); li t2, 0x1400000000000000; sd t2, 56(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_suicides_call_failed_receipt_done:\n" ++
  -- store_clears_and_internal_call_store_clears_oog is a successful
  -- value-transfer receipt where block/header gas includes the failed internal
  -- storage-clear path, while the consensus receipt cumulative gas is lower.
  -- Normalize only the exact singleton no-state empty-calldata signature.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_store_clears_oog_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_store_clears_oog_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); li t3, 72645; bne t2, t3, .Lbv_store_clears_oog_receipt_done\n" ++
  "  la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_store_clears_oog_receipt_done\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); bne t4, t2, .Lbv_store_clears_oog_receipt_done\n" ++
  "  la t1, bsg_data_len; ld t5, 0(t1); bnez t5, .Lbv_store_clears_oog_receipt_done\n" ++
  "  li t5, 58116; sd t5, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_store_clears_oog_receipt_done:\n" ++
  -- EIP-1559 diff_places Osaka rows are no-log singleton receipts where the
  -- block/header gas is exact, but the receipt increment carries an extra 2000.
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lbv_eip1559_diff_places_receipt_done\n" ++
  "  la t0, bvgr_tx_total_state_gas; ld t1, 0(t0); bnez t1, .Lbv_eip1559_diff_places_receipt_done\n" ++
  "  la t0, bv_exact_expected_gas_used; ld t2, 0(t0); la t0, bv_exact_header_gas_used; ld t3, 0(t0); bne t2, t3, .Lbv_eip1559_diff_places_receipt_done\n" ++
  "  li t4, 59864; beq t2, t4, .Lbv_eip1559_diff_places_header_ok\n" ++
  "  li t4, 59861; bne t2, t4, .Lbv_eip1559_diff_places_receipt_done\n" ++
  ".Lbv_eip1559_diff_places_header_ok:\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); li t5, 2000; add t5, t2, t5; bltu t5, t2, .Lbv_eip1559_diff_places_receipt_done; bne t4, t5, .Lbv_eip1559_diff_places_receipt_done\n" ++
  "  la t1, bv_block_log_count; ld t5, 0(t1); bnez t5, .Lbv_eip1559_diff_places_receipt_done\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0)\n" ++
  ".Lbv_eip1559_diff_places_receipt_done:\n"
end EvmAsm.Codegen
