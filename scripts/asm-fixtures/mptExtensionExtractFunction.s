mpt_extension_extract:
  addi x2, x2, -80
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  mv x20, x14
  mv x21, x15
  sd x0, 0(x19)
  sd x0, 0(x20)
  sd x0, 0(x21)
  mv x10, x8
  mv x11, x9
  jal x1, rlp_walk_init
  bne x12, x0, .+256
  sd x10, 64(x2)
  sd x11, 72(x2)
  ld x10, 64(x2)
  ld x11, 72(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+232
  sub x6, x10, x12
  sub x6, x6, x8
  la x5, mee_path_off
  sd x6, 0(x5)
  la x5, mee_path_len
  sd x12, 0(x5)
  sd x10, 64(x2)
  la x5, mee_path_len
  ld x31, 0(x5)
  beq x31, x0, .+180
  la x5, mee_path_off
  ld x30, 0(x5)
  add x22, x8, x30
  lbu x5, 0(x22)
  srli x6, x5, 4
  andi x7, x6, 2
  bne x7, x0, .+140
  andi x28, x6, 1
  mv x29, x18
  li x30, 0
  beq x28, x0, .+20
  andi x31, x5, 15
  sb x31, 0(x29)
  addi x29, x29, 1
  addi x30, x30, 1
  la x5, mee_path_len
  ld x6, 0(x5)
  addi x6, x6, -1
  addi x31, x22, 1
  beq x6, x0, .+44
  lbu x5, 0(x31)
  srli x7, x5, 4
  andi x28, x5, 15
  sb x7, 0(x29)
  sb x28, 1(x29)
  addi x29, x29, 2
  addi x30, x30, 2
  addi x31, x31, 1
  addi x6, x6, -1
  bne x6, x0, .-36
  sd x30, 0(x19)
  ld x10, 64(x2)
  ld x11, 72(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+32
  sub x6, x10, x12
  sd x6, 0(x20)
  sd x12, 0(x21)
  li x10, 0
  jal x0, .+16
.Lmee_st2:
  li x10, 2
  jal x0, .+8
.Lmee_st1:
  li x10, 1
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  ld x22, 56(x2)
  addi x2, x2, 80
  jalr x0, 0(x1)
