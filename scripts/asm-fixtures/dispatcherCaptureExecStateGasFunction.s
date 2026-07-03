dispatcher_capture_exec_state_gas:
  la t0, evm_state_gas_used
  ld t0, 0(t0)               # raw tx_output.state_gas_used for this tx
  la t1, bvgr_tx_exec_state_gas
  slli t2, a0, 3             # i * 8 (8-aligned)
  add t1, t1, t2
  sd t0, 0(t1)               # bvgr_tx_exec_state_gas[i] = state_gas_used
  ret
