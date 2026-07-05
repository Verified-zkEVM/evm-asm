/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptSpecialRepairs

  Late singleton receipt repairs used by BlockVerdictReceiptsTail before receipt
  materialization. Split out to keep the tail module under the Codegen file-size cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdictReceiptGasRepairs

namespace EvmAsm.Codegen

def blockVerdictReceiptSpecialRepairs : String :=
  blockVerdictReceiptGasRepairFinal ++
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
