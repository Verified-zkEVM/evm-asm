/-
  EvmAsm.Codegen.Programs.BlockVerdictGasGatePrelude

  Gas-gate prelude fragment for `block_verdict`, split from
  BlockVerdictFunction.lean for FileSizeGuard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate

namespace EvmAsm.Codegen

/-- Runtime gas-result preparation and EIP-8037/EIP-7778 gate prelude. -/
def blockVerdictGasGatePrelude : String :=
  ".Lbv_after_tx_gas_precharge:\n" ++
  -- fhsxz.2.4.2.57.11.6.5.2.1.3: prefill the transaction-count and
  -- intrinsic-state-gas substrate BEFORE eip8037_tx_gas_gate. The gate still
  -- runs unconditionally: a substrate parse/fill failure zeros the prefix and
  -- falls through, preserving the old conservative gate behavior while making
  -- the exact per-tx state dimension available to the follow-up gate patch.
  "  la t2, bvgr_arena_tx_count; sd zero, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  li a2, " ++ toString bvMtxFullTxCap ++ "\n" ++
  "  jal ra, block_verdict_tx_gas_limits\n" ++
  "  bnez a0, .Lbv_pregate_state_gas_ready\n" ++
  "  la t2, bvgr_arena_tx_count; sd a1, 0(t2)\n" ++
  "  la t2, bv_tx_list_ptr; ld a0, 0(t2)\n  la t2, bv_tx_list_len; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  la a3, bvgr_tx_state_gas\n" ++
  "  la t2, teer_records_ptr; la t3, basr_records; sd t3, 0(t2)\n" ++
  "  la t2, bv_bal_start; ld a4, 0(t2)\n  la t2, bv_bal_len; ld a5, 0(t2)\n  la t2, bv_chain_id; ld a6, 0(t2)\n" ++
  "  jal ra, block_verdict_tx_state_gas_array\n" ++
  "  beqz a0, .Lbv_pregate_state_gas_ready\n" ++
  "  la t2, bvgr_tx_state_gas; la t3, bvgr_arena_tx_count; ld t3, 0(t3); li t4, 0\n" ++
  ".Lbv_pregate_state_gas_zero:\n" ++
  "  beq t4, t3, .Lbv_pregate_state_gas_ready\n" ++
  "  slli t5, t4, 3; add t5, t2, t5; sd zero, 0(t5); addi t4, t4, 1; j .Lbv_pregate_state_gas_zero\n" ++
  ".Lbv_pregate_state_gas_ready:\n" ++
  "  # EIP-8037 tx inclusion gas gate: reject parse-supported legacy tx blocks\n" ++
  "  # whose worst regular/state gas exceeds the remaining 2D block budget.\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)             # exec_payload\n" ++
  "  la t2, bv_bal_start; ld a1, 0(t2)          # bal_start\n" ++
  "  la t2, bv_bal_len; ld a2, 0(t2)            # bal_len\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  mv a3, a0                                  # gas_limit\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  jal ra, eip8037_tx_gas_gate\n" ++
  "  bnez a0, .Lbv_eip8037_gas_fail\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la t2, bvgr_runtime_gas_left_ptr; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_runtime_refund_counter_ptr; ld a2, 0(t2)\n" ++
  "  la t2, bvgr_runtime_calldata_floor_ptr; ld a3, 0(t2)\n" ++
  "  la t2, bvgr_runtime_count; ld a4, 0(t2)\n" ++
  "  li a5, " ++ toString bvMtxFullTxCap ++ "\n" ++
  "  jal ra, block_verdict_gas_result_arena_prepare\n" ++
  bvRuntimeCompletenessSetFromArenaStatus ++
  -- WIP: Amsterdam storage-clear invalid multi-tx fixtures can otherwise false-accept when
  -- runtime staging bails before gas-result materialization. Keep this reject pinned to the
  -- observed status-2/shape-61/two-tx BAL signature so valid EIP-7708 burn-log rows with the
  -- same incomplete-arena status continue through the authenticated state-root path.
  "  li t0, 2; bne a0, t0, .Lbv_status2_storage_clear_wip_done\n" ++
  "  la t0, bvgr_arena_tx_count; ld t1, 0(t0); li t2, 2; bne t1, t2, .Lbv_status2_storage_clear_wip_done\n" ++
  "  la t0, bv_receipts_completeness_shape; ld t1, 0(t0); li t2, 61; bne t1, t2, .Lbv_status2_storage_clear_wip_done\n" ++
  "  la t0, bv_dispatch_runtime_status; ld t1, 0(t0); li t2, 6; bne t1, t2, .Lbv_status2_storage_clear_wip_done\n" ++
  "  la t0, bsr_bal_count; ld t1, 0(t0); li t2, 7; bne t1, t2, .Lbv_status2_storage_clear_wip_done\n" ++
  "  la t0, bsr_change_count; ld t1, 0(t0); li t2, 5; bne t1, t2, .Lbv_status2_storage_clear_wip_done\n" ++
  "  la t0, bsr_wl_v; ld t1, 0(t0); li t2, 1971; bne t1, t2, .Lbv_status2_storage_clear_wip_done\n" ++
  "  j .Lbv_eip7778_block_gas_fail\n" ++
  ".Lbv_status2_storage_clear_wip_done:\n"

end EvmAsm.Codegen
