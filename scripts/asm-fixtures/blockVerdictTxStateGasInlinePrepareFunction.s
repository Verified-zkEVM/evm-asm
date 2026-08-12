block_verdict_tx_state_gas_inline_prepare:
  addi sp, sp, -64; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp); sd a6, 56(sp)
  slli t0, a6, 3; la t1, bvgr_tx_state_gas; add a2, t1, t0; la t1, runtime_tx_state_gas_ptr; sd a2, 0(t1); ld a0, 8(sp); ld a1, 16(sp); jal ra, tx_intrinsic_state_gas
  bnez a0, .Lbvtgip_restore
  ld t0, 56(sp); slli t0, t0, 3; la t1, bvgr_tx_state_gas; add t1, t1, t0; ld t2, 0(t1)
  la t3, exec_nonstorage_effect_count; ld t4, 0(t3); la t3, runtime_tx_auth_effect_count_checkpoint; sd t4, 0(t3); la t3, exec_nonstorage_effect_overflow; ld t4, 0(t3); la t3, runtime_tx_auth_effect_overflow_checkpoint; sd t4, 0(t3); la t3, exec_code_effect_count; ld t4, 0(t3); la t3, runtime_tx_auth_code_effect_count_checkpoint; sd t4, 0(t3); la t3, exec_code_effect_next; ld t4, 0(t3); la t3, runtime_tx_auth_code_effect_next_checkpoint; sd t4, 0(t3); la t3, exec_code_effect_overflow; ld t4, 0(t3); la t3, runtime_tx_auth_code_effect_overflow_checkpoint; sd t4, 0(t3)
  la a0, bv_mtx_ctx; jal ra, simple_transfer_intrinsic_gas
  bnez a0, .Lbvtgip_restore
  mv t2, a1
  la t0, runtime_tx_calldata_floor; sd a2, 0(t0); la t0, bv_runtime_calldata_floor; sd a2, 0(t0)
  ld t0, 56(sp); slli t0, t0, 3; la t1, bvgr_tx_state_gas; add t1, t1, t0; ld t3, 0(t1)
  la t0, bv_mtx_ctx; ld t4, 40(t0)
  add t5, t2, t3
  bltu t4, t5, .Lbvtgip_restore
  sub t5, t4, t5
  li t6, 16777216
  bgeu t2, t6, .Lbvtgip_restore
  sub t6, t6, t2
  la t1, evm_state_gas_left; sd zero, 0(t1)
  bleu t5, t6, .Lbvtgip_a4_no_res
  sub t0, t5, t6
  sd t0, 0(t1)
  mv a4, t6
  j .Lbvtgip_baseline
.Lbvtgip_a4_no_res:
  mv a4, t5
.Lbvtgip_baseline:
  la t1, evm_state_gas_spilled; ld t0, 0(t1)
  la t1, runtime_tx_state_gas_message_spilled; sd t0, 0(t1)
  la t1, evm_state_gas_left; ld t0, 0(t1)
  la t1, runtime_tx_state_gas_message_left; sd t0, 0(t1)
  la t1, runtime_tx_state_reservoir_initial; sd t0, 0(t1)
  li t0, 1; la t1, runtime_tx_state_gas_entry_valid; sd t0, 0(t1)
.Lbvtgip_call_auth:
  ld a0, 24(sp); ld a1, 32(sp); ld a2, 40(sp); ld a3, 48(sp); jal ra, eip7702_auth_state_prepare
  la t0, evm_state_gas_left; ld t1, 0(t0)
  la t0, runtime_tx_state_gas_message_left; ld t2, 0(t0); sub t2, t2, t1
  la t0, evm_state_gas_spilled; ld t3, 0(t0); add t2, t2, t3
  la t0, runtime_tx_state_gas_message_spilled; ld t3, 0(t0); sub t2, t2, t3
  la t0, runtime_tx_auth_state_used; sd t2, 0(t0)
  la t0, runtime_tx_state_gas_message_left; sd t1, 0(t0)
  la t0, evm_state_gas_spilled; sd zero, 0(t0)
  la t0, runtime_tx_state_gas_message_spilled; sd zero, 0(t0)
  beqz a0, .Lbvtgip_auth_ok
  li t1, 2; beq a0, t1, .Lbvtgip_auth_oog
  j .Lbvtgip_restore
.Lbvtgip_auth_oog:
  la t0, runtime_tx_auth_phase_halted; li t1, 1; sd t1, 0(t0)
  la t3, runtime_tx_auth_effect_count_checkpoint; ld t4, 0(t3); la t3, exec_nonstorage_effect_count; sd t4, 0(t3); la t3, runtime_tx_auth_effect_overflow_checkpoint; ld t4, 0(t3); la t3, exec_nonstorage_effect_overflow; sd t4, 0(t3); la t3, runtime_tx_auth_code_effect_count_checkpoint; ld t4, 0(t3); la t3, exec_code_effect_count; sd t4, 0(t3); la t3, runtime_tx_auth_code_effect_next_checkpoint; ld t4, 0(t3); la t3, exec_code_effect_next; sd t4, 0(t3); la t3, runtime_tx_auth_code_effect_overflow_checkpoint; ld t4, 0(t3); la t3, exec_code_effect_overflow; sd t4, 0(t3)
  la t3, runtime_tx_auth_regular_refund; sd zero, 0(t3); la t3, runtime_tx_top_frame_regular_gas; sd zero, 0(t3); la t3, teer_success_count; sd zero, 0(t3)
  li a0, 0; j .Lbvtgip_ret
.Lbvtgip_auth_ok:
  ld t0, 48(sp); li t1, 4; bne t0, t1, .Lbvtgip_ret
  li t1, 1; la t0, runtime_tx_auth_prepared; sd t1, 0(t0); j .Lbvtgip_ret
.Lbvtgip_restore:
  la t0, runtime_tx_auth_phase_halted; li t1, 1; sd t1, 0(t0)
.Lbvtgip_ret:
  ld ra, 0(sp); addi sp, sp, 64; ret
