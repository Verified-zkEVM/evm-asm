/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPublish

  Simple-transfer runtime publication assembly, split from BlockVerdictFunction.
-/

import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

namespace EvmAsm.Codegen

def blockVerdictSimpleTransferPublishAsmFor (ctxLabel : String) : String :=
  ".Lbv_simple_transfer_precompile_fail:\n" ++
  -- Mode 2 has already paid the transaction-level intrinsic/upfront gas in
  -- the shared dispatcher.  Jump straight to its exceptional-halt join and
  -- avoid the legacy direct-publication wrapper.
  "  la t0, bv_mtx_precompile_lane; ld t0, 0(t0); li t1, 2; beq t0, t1, .Ldtrc_mtx_precompile_failure\n" ++
  "  addi sp, sp, -48\n  sd ra, 0(sp)\n" ++
  "  la a0, " ++ ctxLabel ++ "; jal ra, simple_transfer_intrinsic_gas\n  bnez a0, .Lbv_simple_transfer_runtime_publish_fail\n  sd a2, 24(sp)\n  jal ra, block_log_window_snapshot\n" ++
  -- An exceptional top-frame halt burns regular gas, but
  -- `refill_frame_state_gas` restores the whole state reservoir.  The
  -- shortcut publishes one effective gas-left scalar, so retain exactly the
  -- reservoir carved out above TX_MAX_GAS_LIMIT (the intrinsic-regular term
  -- cancels from `execution_gas - regular_gas`).
  "  la t4, " ++ ctxLabel ++ "; ld t5, 40(t4); li t6, 16777216\n" ++
  "  bleu t5, t6, .Lbv_simple_transfer_precompile_fail_no_reservoir\n" ++
  "  sub t5, t5, t6; j .Lbv_simple_transfer_precompile_fail_have_gas_left\n" ++
  ".Lbv_simple_transfer_precompile_fail_no_reservoir:\n  li t5, 0\n" ++
  ".Lbv_simple_transfer_precompile_fail_have_gas_left:\n" ++
  "  la t4, bv_runtime_gas_left; sd t5, 0(t4)\n  la t4, bv_runtime_refund_counter; sd zero, 0(t4)\n  ld t5, 24(sp)\n  la t4, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  -- A failed direct precompile is the depth-0 frame error case. Mirror
  -- `refill_frame_state_gas` into both the dispatcher counter and its per-tx
  -- published array; otherwise a preceding top-frame value charge survives as
  -- executed state gas even though the transaction rolled back.
  "  la t4, evm_state_gas_used; sd zero, 0(t4)\n  la t4, evm_state_gas_spilled; sd zero, 0(t4)\n" ++
  directTransferStateGasBaselineAsm "bv_st_precompile" ++
  "  la t0, bv_mtx_precompile_lane; ld t0, 0(t0); bnez t0, .Lbv_mtx_precompile_fail_publish\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n  jal ra, dispatcher_capture_exec_state_gas_differential\n" ++
  "  la t4, bv_tx_status_arr; sd zero, 0(t4)\n  la t4, bv_tx_is_creation_arr; sd zero, 0(t4)\n  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  li a0, 0; li a1, 0; jal ra, block_verdict_tx_state_gas_inline_finalize\n" ++
  "  ld ra, 0(sp)\n  addi sp, sp, 48\n" ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_mtx_precompile_fail_publish:\n" ++
  -- The shared kernel computed the exceptional halt in scalar scratch. Publish
  -- it at the current MTx index and let the common MTx postlude finalize once.
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t2, t1, 3\n" ++
  "  la t3, bv_runtime_gas_left; ld t4, 0(t3); la t3, bv_mtx_gas_left; add t3, t3, t2; sd t4, 0(t3)\n" ++
  "  la t3, bv_runtime_refund_counter; ld t4, 0(t3); la t3, bv_mtx_refund; add t3, t3, t2; sd t4, 0(t3)\n" ++
  "  la t3, bv_runtime_calldata_floor; ld t4, 0(t3); la t3, bv_mtx_calldata; add t3, t3, t2; sd t4, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t2; sd zero, 0(t3); la t3, bv_tx_is_creation_arr; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  slli t2, t1, 4; la t3, bv_tx_log_window; add t3, t3, t2; la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3); la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  "  mv a0, t1; jal ra, dispatcher_capture_exec_state_gas\n  jal ra, dispatcher_capture_exec_state_gas_differential\n" ++
  "  la t0, bv_mtx_precompile_lane; sd zero, 0(t0)\n" ++
  "  li a4, 0\n" ++
  "  ld ra, 0(sp); addi sp, sp, 48; j .Lbv_mtx_effects_kept\n" ++
  ".Lbv_simple_transfer_no_log_then_after_tx_gas_precharge:\n" ++
  "  addi sp, sp, -48\n  sd ra, 0(sp)\n  sd t6, 8(sp)\n" ++
  "  la a0, " ++ ctxLabel ++ "; jal ra, simple_transfer_intrinsic_gas\n" ++
  "  bnez a0, .Lbv_simple_transfer_runtime_publish_fail\n" ++
  directTransferStateGasBaselineAsm "bv_st_no_log" ++
  "  la t4, tgbpv_direct_oog; sd zero, 0(t4)\n" ++
  "  sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)\n" ++
  topLevelValueRecipientStateGasAsm "bv_st_publish_pre_no_log" ctxLabel ++
  "  sd t0, 40(sp)\n" ++
  "  beqz t0, .Lbv_simple_transfer_no_log_state_pre_ok\n" ++
  "  ld t6, 8(sp); ld t4, 16(sp); ld t3, 32(sp); ld t0, 40(sp)\n" ++
  "  la t5, " ++ ctxLabel ++ "; ld t5, 40(t5); add t6, t6, t4; add t6, t6, t3; add t6, t6, t0\n" ++
  "  bltu t5, t6, .Lbv_simple_transfer_state_oog_no_log\n" ++
  ".Lbv_simple_transfer_no_log_state_pre_ok:\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  "  j .Lbv_simple_transfer_after_log_snapshot\n" ++
  ".Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge:\n" ++
  -- The shared dispatcher owns intrinsic gas, state-gas rollback, and the
  -- final MTx publication for mode 2; only the selector's cost in t6 is new.
  "  la t0, bv_mtx_precompile_lane; ld t0, 0(t0); li t1, 2; beq t0, t1, .Ldtrc_mtx_precompile_success\n" ++
  "  addi sp, sp, -48\n  sd ra, 0(sp)\n  sd t6, 8(sp)\n" ++
  "  la a0, " ++ ctxLabel ++ "; jal ra, simple_transfer_intrinsic_gas\n" ++
  "  bnez a0, .Lbv_simple_transfer_runtime_publish_fail\n" ++
  directTransferStateGasBaselineAsm "bv_st_emit" ++
  "  la t4, tgbpv_direct_oog; sd zero, 0(t4)\n" ++
  "  sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)\n" ++
  topLevelValueRecipientStateGasAsm "bv_st_publish_pre_emit" ctxLabel ++
  "  sd t0, 40(sp)\n" ++
  "  beqz t0, .Lbv_simple_transfer_emit_state_pre_ok\n" ++
  "  ld t6, 8(sp); ld t4, 16(sp); ld t3, 32(sp); ld t0, 40(sp)\n" ++
  "  la t5, " ++ ctxLabel ++ "; ld t5, 40(t5); add t6, t6, t4; add t6, t6, t3; add t6, t6, t0\n" ++
  "  bltu t5, t6, .Lbv_simple_transfer_state_oog_no_log\n" ++
  ".Lbv_simple_transfer_emit_state_pre_ok:\n" ++
  -- #10685 PR2: bv_emit_single_tx_tl7708 deleted (never-written bv_simple_transfer_tx;
  -- mode-2 bypass; early-exit no-op). Live TL staging is MTx/CREATE → eip7708_tl_*.
  "  jal ra, dispatcher_reemit_pending_tl\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  "  j .Lbv_simple_transfer_after_log_snapshot\n" ++
  ".Lbv_simple_transfer_state_oog_no_log:\n" ++
  "  la t0, tgbpv_skip_value; li t1, 1; sd t1, 0(t0)\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  ".Lbv_simple_transfer_after_log_snapshot:\n" ++
  topLevelValueRecipientStateGasAsm "bv_st" ctxLabel ++
  "  sd t0, 40(sp)\n" ++
  "  ld t0, 40(sp)\n" ++
  "  la t2, tgbpv_skip_value; ld t2, 0(t2); beqz t2, .Lbv_simple_transfer_state_publish_ok\n" ++
  "  la t1, evm_state_gas_used; sd zero, 0(t1)\n" ++
  "  li t5, 0; j .Lbv_simple_transfer_gas_have_left\n" ++
  ".Lbv_simple_transfer_state_publish_ok:\n" ++
  directTransferStateGasChargeAsm "bv_st" ++
  "  ld t6, 8(sp)\n" ++
  "  ld t4, 16(sp)\n" ++
  "  ld t3, 32(sp)\n" ++
  "  la t5, " ++ ctxLabel ++ "; ld t5, 40(t5); add t6, t6, t4; add t6, t6, t3; add t6, t6, t0\n" ++
  "  bltu t5, t6, .Lbv_simple_transfer_gas_exhausted\n" ++
  "  sub t5, t5, t6; j .Lbv_simple_transfer_gas_have_left\n" ++
  ".Lbv_simple_transfer_gas_exhausted:\n" ++
  -- v0.6.0 (C8): charge-point OOG -- failed tx, all gas burned, prep
  -- state charges refill.
  "  li t5, 0\n" ++
  "  la t4, tgbpv_direct_oog; li t6, 1; sd t6, 0(t4)\n" ++
  "  la t4, evm_state_gas_used; sd zero, 0(t4)\n" ++
  ".Lbv_simple_transfer_gas_have_left:\n" ++
  "  la t4, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bv_runtime_refund_counter; sd zero, 0(t4)\n" ++
  "  ld t5, 24(sp)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  la t4, tgbpv_skip_value; ld t5, 0(t4); beqz t5, .Lbv_simple_transfer_publish_status_success\n" ++
  "  li t5, 0; j .Lbv_simple_transfer_publish_status_store\n" ++
  ".Lbv_simple_transfer_publish_status_success:\n" ++
  "  la t4, tgbpv_direct_oog; ld t5, 0(t4); beqz t5, .Lbv_stp_status_one\n" ++
  "  li t5, 0; j .Lbv_simple_transfer_publish_status_store\n" ++
  ".Lbv_stp_status_one:\n" ++
  "  li t5, 1\n" ++
  ".Lbv_simple_transfer_publish_status_store:\n" ++
  "  la t0, bv_mtx_precompile_lane; ld t0, 0(t0); bnez t0, .Lbv_mtx_precompile_publish\n" ++
  "  la t4, bv_tx_status_arr; sd t5, 0(t4)\n" ++
  "  la t4, bv_tx_is_creation_arr; sd zero, 0(t4)\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 0(t4)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); la t4, bv_tx_log_window; sd t5, 8(t4)\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n  jal ra, dispatcher_capture_exec_state_gas_differential\n" ++
  "  li a0, 0; la t0, bv_tx_status_arr; ld a1, 0(t0); jal ra, block_verdict_tx_state_gas_inline_finalize\n" ++
  "  ld ra, 0(sp)\n  addi sp, sp, 48\n" ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_mtx_precompile_publish:\n" ++
  -- `t5` is the shared kernel's final status. Transfer scalar outputs to the
  -- current MTx record; never clobber transaction zero for tx i > 0.
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t2, t1, 3\n" ++
  "  la t3, bv_runtime_gas_left; ld t4, 0(t3); la t3, bv_mtx_gas_left; add t3, t3, t2; sd t4, 0(t3)\n" ++
  "  la t3, bv_runtime_refund_counter; ld t4, 0(t3); la t3, bv_mtx_refund; add t3, t3, t2; sd t4, 0(t3)\n" ++
  "  la t3, bv_runtime_calldata_floor; ld t4, 0(t3); la t3, bv_mtx_calldata; add t3, t3, t2; sd t4, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t2; sd t5, 0(t3); la t3, bv_tx_is_creation_arr; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  slli t2, t1, 4; la t3, bv_tx_log_window; add t3, t3, t2; la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3); la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  "  mv a0, t1; jal ra, dispatcher_capture_exec_state_gas\n  jal ra, dispatcher_capture_exec_state_gas_differential\n" ++
  "  la t0, bv_mtx_precompile_lane; sd zero, 0(t0)\n" ++
  "  la t0, bv_tx_status_arr; slli t2, t1, 3; add t0, t0, t2; ld a4, 0(t0)\n" ++
  "  ld ra, 0(sp); addi sp, sp, 48; j .Lbv_mtx_effects_kept\n" ++
  ".Lbv_simple_transfer_runtime_publish_fail:\n" ++
  "  ld ra, 0(sp)\n  addi sp, sp, 48\n" ++
  "  j .Lbv_after_tx_gas_precharge\n"

def blockVerdictSimpleTransferPublishAsm : String :=
  blockVerdictSimpleTransferPublishAsmFor "bv_simple_transfer_tx"

end EvmAsm.Codegen
