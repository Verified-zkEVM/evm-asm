block_verdict_tx_state_gas_array:
  addi x2, x2, -112
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  sd x23, 64(x2)
  sd x24, 72(x2)
  sd x25, 80(x2)
  sd x26, 88(x2)
  sd x27, 96(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  mv x24, x14
  mv x25, x15
  mv x26, x16
  li x5, 4
  bltu x9, x5, .+216
  mv x10, x8
  jal x1, bgv_u32le
  andi x5, x10, 3
  bne x5, x0, .+200
  bltu x9, x10, .+196
  srli x20, x10, 2
  bne x20, x18, .+196
  beq x20, x0, .+176
  mv x21, x0
  beq x21, x20, .+168
  slli x5, x21, 2
  add x10, x8, x5
  jal x1, bgv_u32le
  mv x22, x10
  slli x5, x20, 2
  bltu x22, x5, .+152
  bltu x9, x22, .+148
  addi x5, x21, 1
  beq x5, x20, .+24
  slli x6, x5, 2
  add x10, x8, x6
  jal x1, bgv_u32le
  mv x23, x10
  jal x0, .+8
  mv x23, x9
  bltu x23, x22, .+112
  bltu x9, x23, .+108
  add x10, x8, x22
  sub x11, x23, x22
  slli x5, x21, 3
  add x12, x19, x5
  jal x1, tx_intrinsic_state_gas
  bne x10, x0, .+100
  beq x24, x0, .+64
  add x10, x8, x22
  sub x11, x23, x22
  mv x12, x24
  mv x13, x25
  mv x14, x26
  addi x15, x21, 1
  jal x1, tx_eip7702_existing_authority_refund
  slli x5, x21, 3
  add x6, x19, x5
  ld x7, 0(x6)
  add x7, x7, x10
  sd x7, 0(x6)
  jal x0, .+12
  jal x0, .+8
  sd x0, 0(x6)
  addi x21, x21, 1
  jal x0, .-164
  li x10, 0
  jal x0, .+24
  li x10, 1
  jal x0, .+16
  li x10, 2
  jal x0, .+8
  li x10, 3
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  ld x22, 56(x2)
  ld x23, 64(x2)
  ld x24, 72(x2)
  ld x25, 80(x2)
  ld x26, 88(x2)
  ld x27, 96(x2)
  addi x2, x2, 112
  jalr x0, 0(x1)
