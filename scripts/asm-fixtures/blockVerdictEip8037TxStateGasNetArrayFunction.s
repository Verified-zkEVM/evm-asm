block_verdict_eip8037_tx_state_gas_net_array:
  addi x2, x2, -48
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  li x20, 0
  beq x20, x18, .+52
  slli x5, x20, 3
  add x6, x8, x5
  ld x10, 0(x6)
  add x6, x9, x5
  ld x11, 0(x6)
  addi x0, x0, 0
  addi x0, x0, 0
  addi x0, x0, 0
  add x15, x19, x5
  jal x1, eip8037_tx_state_gas
  addi x20, x20, 1
  jal x0, .-48
  li x10, 0
  li x11, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  addi x2, x2, 48
  jalr x0, 0(x1)
