dispatcher_tx_gas_settle:
  lui x5, 0xa
  addiw x5, x5, 1
  slli x5, x5, 16
  ld x6, 32(x5)
  la x5, evm_env
  ld x5, 568(x5)
  la x27, runtime_tx_top_frame_regular_gas
  ld x27, 0(x27)
  beq x27, x0, .+8
  add x5, x27, x0
  la x7, evm_state_gas_left
  ld x7, 0(x7)
  la x28, evm_refund_acc
  ld x11, 0(x28)
  li x12, 1
  beq x6, x0, .+152
  li x28, 1
  beq x6, x28, .+144
  li x28, 5
  beq x6, x28, .+136
  li x11, 0
  li x12, 0
  la x30, evm_state_gas_used
  ld x28, 0(x30)
  la x31, evm_state_gas_spilled
  li x29, 2
  bne x6, x29, .+48
  ld x29, 0(x31)
  bgeu x29, x28, .+12
  sub x28, x28, x29
  jal x0, .+8
  li x28, 0
  sd x28, 0(x30)
  sd x0, 0(x31)
  add x7, x7, x28
  add x5, x5, x29
  jal x0, .+60
  addi x0, x0, 0
  ld x29, 0(x31)
  bgeu x28, x29, .+16
  li x28, 0
  sd x28, 0(x30)
  jal x0, .+16
  addi x0, x0, 0
  sub x28, x28, x29
  sd x28, 0(x30)
  lui x27, 0x1000
  bgeu x5, x27, .+12
  li x5, 0
  jal x0, .+8
  sub x5, x5, x27
  add x10, x5, x0
  jalr x0, 0(x1)
  addi x0, x0, 0