dispatcher_tx_gas_settle:
  lui x5, 0xa
  addiw x5, x5, 1
  slli x5, x5, 16
  ld x6, 32(x5)
  la x5, evm_env
  ld x5, 568(x5)
  la x7, evm_state_gas_left
  ld x7, 0(x7)
  la x28, evm_refund_acc
  ld x11, 0(x28)
  li x12, 1
  beq x6, x0, .+96
  li x28, 1
  beq x6, x28, .+88
  li x28, 5
  beq x6, x28, .+80
  li x11, 0
  li x12, 0
  la x30, evm_state_gas_used
  ld x28, 0(x30)
  la x31, evm_state_gas_spilled
  ld x29, 0(x31)
  sd x0, 0(x30)
  sd x0, 0(x31)
  bgeu x29, x28, .+16
  sub x28, x28, x29
  add x7, x7, x28
  jal x0, .+4
  li x28, 2
  bne x6, x28, .+12
  add x5, x5, x29
  jal x0, .+8
  li x5, 0
  add x10, x5, x7
  jalr x0, 0(x1)
