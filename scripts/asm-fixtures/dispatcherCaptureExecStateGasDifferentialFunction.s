dispatcher_capture_exec_state_gas_differential:
  la t0, evm_state_gas_used; ld t0, 0(t0)
  la t1, runtime_tx_state_gas_entry_valid; ld t1, 0(t1)
  beqz t1, .Lcesg_diff_not_derivable
.Lcesg_diff_post_preparation:
  la t1, runtime_tx_state_gas_message_left; ld t1, 0(t1)
  la t2, evm_state_gas_left; ld t2, 0(t2); sub t1, t1, t2
  la t2, evm_state_gas_spilled; ld t2, 0(t2); add t1, t1, t2
  la t2, runtime_tx_state_gas_message_spilled; ld t2, 0(t2); sub t1, t1, t2
  slli t3, a0, 3
  la t2, bvgr_tx_exec_state_gas_derived; add t2, t2, t3; sd t1, 0(t2)
  la t2, bvgr_tx_exec_state_gas_diff; add t2, t2, t3
  bne t0, t1, .Lcesg_diff_mismatch
  sd zero, 0(t2)
  la t2, bvgr_tx_exec_state_gas_nonderivable; add t2, t2, t3; sd zero, 0(t2)
  ret
.Lcesg_diff_mismatch:
  li t4, 1; sd t4, 0(t2)
  la t2, bvgr_tx_exec_state_gas_nonderivable; add t2, t2, t3; sd zero, 0(t2); ret
.Lcesg_diff_not_derivable:
  slli t3, a0, 3
  la t2, bvgr_tx_exec_state_gas_derived; add t2, t2, t3; sd zero, 0(t2)
  la t2, bvgr_tx_exec_state_gas_diff; add t2, t2, t3; sd zero, 0(t2)
  la t2, bvgr_tx_exec_state_gas_nonderivable; add t2, t2, t3; li t4, 1; sd t4, 0(t2); ret
