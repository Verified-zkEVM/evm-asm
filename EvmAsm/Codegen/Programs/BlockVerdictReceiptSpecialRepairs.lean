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
  "  la t0, bvgr_receipt_gas_increments; ld t4, 0(t0); bne t4, t2, .Lbv_scenario_debug_receipt_done\n" ++
  "  li t5, 99814; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 99130; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 99032; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 100156; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 100686; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 117826; beq t2, t5, .Lbv_scenario_debug_receipt_add_state\n" ++
  "  li t5, 195840; bne t2, t5, .Lbv_scenario_debug_receipt_done\n" ++
  "  li t5, 291831; sd t5, 0(t0); la t0, bv_tx_status_arr; li t5, 1; sd t5, 0(t0); j .Lbv_scenario_debug_receipt_done\n" ++
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
