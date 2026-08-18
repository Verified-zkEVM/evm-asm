account_resolve_pre_state:
  addi x2, x2, -208
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
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  mv x20, x14
  mv x21, x15
  sd x0, 0(x9)
  sd x0, 8(x9)
  sd x0, 16(x9)
  sd x0, 24(x9)
  sd x0, 32(x9)
  li x23, 0
  la x5, account_writes_count
  ld x6, 0(x5)
  lui x7, 0x1
  addiw x7, x7, 1975
  slli x7, x7, 19
  li x28, 0
  bgeu x28, x6, .+136
  slli x29, x28, 7
  add x30, x7, x29
  li x31, 20
  mv x10, x30
  mv x11, x8
  beq x31, x0, .+40
  lbu x12, 0(x10)
  lbu x13, 0(x11)
  bne x12, x13, .+20
  addi x10, x10, 1
  addi x11, x11, 1
  addi x31, x31, -1
  jal x0, .-28
  addi x28, x28, 1
  jal x0, .-60
  mv x22, x30
  ld x5, 112(x22)
  mv x23, x5
  andi x6, x5, 8
  beq x6, x0, .+56
  ld x6, 72(x22)
  beq x6, x0, .+204
  ld x6, 32(x22)
  sd x6, 8(x9)
  ld x6, 40(x22)
  sd x6, 16(x9)
  ld x6, 48(x22)
  sd x6, 24(x9)
  ld x6, 56(x22)
  sd x6, 32(x9)
  ld x6, 64(x22)
  sd x6, 0(x9)
  jal x0, .+152
  mv x10, x18
  mv x11, x19
  mv x12, x8
  li x13, 20
  mv x14, x20
  mv x15, x21
  addi x16, x2, 96
  jal x1, account_at_header_state_root_tracked
  li x5, 1
  bltu x5, x10, .+128
  beq x10, x0, .+8
  jal x0, .+48
  addi x5, x2, 96
  ld x6, 8(x5)
  sd x6, 8(x9)
  ld x6, 16(x5)
  sd x6, 16(x9)
  ld x6, 24(x5)
  sd x6, 24(x9)
  ld x6, 32(x5)
  sd x6, 32(x9)
  ld x6, 0(x5)
  sd x6, 0(x9)
  andi x6, x23, 1
  beq x6, x0, .+36
  ld x6, 32(x22)
  sd x6, 8(x9)
  ld x6, 40(x22)
  sd x6, 16(x9)
  ld x6, 48(x22)
  sd x6, 24(x9)
  ld x6, 56(x22)
  sd x6, 32(x9)
  andi x6, x23, 2
  beq x6, x0, .+12
  ld x6, 64(x22)
  sd x6, 0(x9)
  li x10, 0
  jal x0, .+16
  li x10, 0
  jal x0, .+8
  li x10, 1
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
  addi x2, x2, 208
  jalr x0, 0(x1)
