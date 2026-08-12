block_verdict_tx_state_gas_inline_finalize:
  slli t0, a0, 3; la t1, bvgr_tx_state_gas; add t1, t1, t0; ld t2, 0(t1)
  bnez a1, .Lbvtgif_exec
  la t3, runtime_tx_auth_phase_halted; ld t3, 0(t3); beqz t3, .Lbvtgif_store; sd zero, 0(t1); li t2, 0
  la t3, runtime_tx_auth_effect_count_checkpoint; ld t4, 0(t3); la t3, exec_nonstorage_effect_count; sd t4, 0(t3); la t3, runtime_tx_auth_effect_overflow_checkpoint; ld t4, 0(t3); la t3, exec_nonstorage_effect_overflow; sd t4, 0(t3); la t3, runtime_tx_auth_code_effect_count_checkpoint; ld t4, 0(t3); la t3, exec_code_effect_count; sd t4, 0(t3); la t3, runtime_tx_auth_code_effect_next_checkpoint; ld t4, 0(t3); la t3, exec_code_effect_next; sd t4, 0(t3); la t3, runtime_tx_auth_code_effect_overflow_checkpoint; ld t4, 0(t3); la t3, exec_code_effect_overflow; sd t4, 0(t3)
  .Lbvtgif_clear_regular: la t3, runtime_tx_auth_regular_refund; sd zero, 0(t3); la t3, runtime_tx_top_frame_regular_gas; sd zero, 0(t3); j .Lbvtgif_store
.Lbvtgif_exec:
  la t3, bvgr_tx_exec_state_gas; add t3, t3, t0; ld t3, 0(t3); add t2, t2, t3
.Lbvtgif_store:
  la t1, bvgr_tx_total_state_gas; add t1, t1, t0; sd t2, 0(t1); li a0, 0; ret
