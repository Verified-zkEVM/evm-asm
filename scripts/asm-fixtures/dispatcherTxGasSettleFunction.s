dispatcher_tx_gas_settle:
  la x5, rdg_halt_kind
  ld x6, 0(x5)
  addi x0, x0, 0
  la x5, evm_env
  ld x5, 568(x5)
  la x7, evm_state_gas_left
  ld x7, 0(x7)
  la x28, evm_refund_acc
  ld x11, 0(x28)
  li x12, 1
  beq x6, x0, .Lsettle_finish
  li x28, 1
  beq x6, x28, .Lsettle_finish
  li x28, 5
  beq x6, x28, .Lsettle_finish
  li x11, 0
  li x12, 0
  la x30, evm_state_gas_used
  ld x28, 0(x30)
  la x31, evm_state_gas_spilled
  ld x29, 0(x31)
  bne x12, x0, .Lsettle_pools
  sd x0, 0(x30)
  sd x0, 0(x31)
  la x30, evm_state_gas_left
  addi x30, x30, 24
  ld x7, 0(x30)
  addi x30, x30, -24
  sd x7, 0(x30)
  j .Lsettle_refund
.Lsettle_pools:
  bgeu x29, x28, .Lsettle_refund
  sub x28, x28, x29
  add x7, x7, x28
  jal x0, .Lsettle_refund
.Lsettle_refund:
  li x28, 2
  bne x6, x28, .Lsettle_zero
  add x5, x5, x29
  jal x0, .Lsettle_finish
.Lsettle_zero:
  li x5, 0
.Lsettle_finish:
  add x10, x5, x7
  jalr x0, 0(x1)
