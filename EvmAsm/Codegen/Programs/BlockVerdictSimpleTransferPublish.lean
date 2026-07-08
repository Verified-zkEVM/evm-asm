/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPublish

  Simple-transfer runtime publication assembly, split from BlockVerdictFunction.
-/

import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

namespace EvmAsm.Codegen

def blockVerdictSimpleTransferPublishAsm : String :=
  ".Lbv_simple_transfer_precompile_fail:\n" ++
  "  addi sp, sp, -48\n  sd ra, 0(sp)\n" ++
  "  la a0, bv_simple_transfer_tx; jal ra, simple_transfer_intrinsic_gas\n  bnez a0, .Lbv_simple_transfer_runtime_publish_fail\n  sd a2, 24(sp)\n  jal ra, block_log_window_snapshot\n" ++
  "  la t4, bv_runtime_gas_left; sd zero, 0(t4)\n  la t4, bv_runtime_refund_counter; sd zero, 0(t4)\n  ld t5, 24(sp)\n  la t4, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  la t4, bv_tx_status_arr; sd zero, 0(t4)\n  la t4, bv_tx_is_creation_arr; sd zero, 0(t4)\n  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  ld ra, 0(sp)\n  addi sp, sp, 48\n" ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_no_log_then_after_tx_gas_precharge:\n" ++
  "  addi sp, sp, -48\n  sd ra, 0(sp)\n  sd t6, 8(sp)\n" ++
  "  la a0, bv_simple_transfer_tx; jal ra, simple_transfer_intrinsic_gas\n" ++
  "  bnez a0, .Lbv_simple_transfer_runtime_publish_fail\n" ++
  "  sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  "  j .Lbv_simple_transfer_after_log_snapshot\n" ++
  ".Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge:\n" ++
  "  addi sp, sp, -48\n  sd ra, 0(sp)\n  sd t6, 8(sp)\n" ++
  "  la a0, bv_simple_transfer_tx; jal ra, simple_transfer_intrinsic_gas\n" ++
  "  bnez a0, .Lbv_simple_transfer_runtime_publish_fail\n" ++
  "  sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)\n" ++
  "  jal ra, bv_emit_single_tx_tl7708\n" ++
  "  jal ra, dispatcher_reemit_pending_tl\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  ".Lbv_simple_transfer_after_log_snapshot:\n" ++
  topLevelValueRecipientStateGasAsm "bv_st" "bv_simple_transfer_tx" ++
  "  sd t0, 40(sp)\n" ++
  "  ld t6, 8(sp)\n" ++
  "  ld t4, 16(sp)\n" ++
  "  ld t3, 32(sp)\n" ++
  "  ld t0, 40(sp)\n" ++
  "  la t1, evm_state_gas_used; sd t0, 0(t1)\n" ++
  "  la t5, bv_simple_transfer_tx; ld t5, 40(t5); add t6, t6, t4; add t6, t6, t3; add t6, t6, t0\n" ++
  "  bltu t5, t6, .Lbv_simple_transfer_gas_exhausted\n" ++
  "  sub t5, t5, t6; j .Lbv_simple_transfer_gas_have_left\n" ++
  ".Lbv_simple_transfer_gas_exhausted:\n" ++
  "  li t5, 0\n" ++
  ".Lbv_simple_transfer_gas_have_left:\n" ++
  "  la t4, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bv_runtime_refund_counter; sd zero, 0(t4)\n" ++
  "  ld t5, 24(sp)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bv_tx_status_arr; sd t5, 0(t4)\n" ++
  "  la t4, bv_tx_is_creation_arr; sd zero, 0(t4)\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  ld ra, 0(sp)\n  addi sp, sp, 48\n" ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_simple_transfer_runtime_publish_fail:\n" ++
  "  ld ra, 0(sp)\n  addi sp, sp, 48\n" ++
  "  j .Lbv_after_tx_gas_precharge\n"

end EvmAsm.Codegen
