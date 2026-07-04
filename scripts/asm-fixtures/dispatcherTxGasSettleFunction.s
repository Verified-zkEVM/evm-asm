dispatcher_tx_gas_settle:
  li t0, 0xa0010000
  ld t1, 32(t0)               # halt_kind
  la t0, evm_env
  ld t0, 568(t0)              # gas_left
  la t2, evm_state_gas_left
  ld t2, 0(t2)
  la t3, evm_refund_acc
  ld a1, 0(t3)
  li a2, 1                    # tx success bit (receipt `succeeded`)
  beqz t1, .Ldtgs_success
  li t3, 1
  beq t1, t3, .Ldtgs_success
  li t3, 5
  beq t1, t3, .Ldtgs_success
  li a1, 0                    # error: refund counter discarded
  li a2, 0                    # error: receipt status = 0
  la t3, evm_state_gas_used
  ld t3, 0(t3)
  add t2, t2, t3              # error: state_gas_left += state_gas_used
  li t3, 2
  beq t1, t3, .Ldtgs_success  # REVERT keeps gas_left
  li t0, 0                    # exceptional halt burns remaining regular gas
.Ldtgs_success:
  add a0, t0, t2
  ret
