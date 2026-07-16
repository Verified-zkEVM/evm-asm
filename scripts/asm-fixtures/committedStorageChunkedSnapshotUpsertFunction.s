bv_mtx_committed_chunked_snapshot_upsert:
  li x5, 0
  beq x5, x12, .+384
  slli x6, x5, 7
  add x6, x11, x6
  li x29, 0
  li x30, 20
  beq x29, x30, .+40
  add x30, x6, x29
  lbu x30, 0(x30)
  li x31, 19
  sub x31, x31, x29
  add x31, x10, x31
  lbu x31, 0(x31)
  bne x30, x31, .+308
  addi x29, x29, 1
  jal x0, .-40
  lwu x30, 20(x6)
  bne x30, x0, .+292
  ld x30, 24(x6)
  bne x30, x0, .+284
  li x7, 0
  beq x7, x14, .+112
  slli x28, x7, 7
  add x28, x13, x28
  li x29, 0
  li x30, 20
  beq x29, x30, .+32
  add x30, x10, x29
  lbu x30, 0(x30)
  add x31, x28, x29
  lbu x31, 0(x31)
  bne x30, x31, .+64
  addi x29, x29, 1
  jal x0, .-32
  ld x30, 32(x6)
  ld x31, 32(x28)
  bne x30, x31, .+44
  ld x30, 40(x6)
  ld x31, 40(x28)
  bne x30, x31, .+32
  ld x30, 48(x6)
  ld x31, 48(x28)
  bne x30, x31, .+20
  ld x30, 56(x6)
  ld x31, 56(x28)
  bne x30, x31, .+8
  jal x0, .+80
  addi x7, x7, 1
  jal x0, .-108
  bgeu x14, x15, .+172
  slli x28, x14, 7
  add x28, x13, x28
  sd x0, 0(x28)
  sd x0, 8(x28)
  sd x0, 16(x28)
  sd x0, 24(x28)
  li x29, 0
  li x30, 20
  beq x29, x30, .+28
  add x30, x10, x29
  lbu x31, 0(x30)
  add x30, x28, x29
  sb x31, 0(x30)
  addi x29, x29, 1
  jal x0, .-28
  addi x14, x14, 1
  ld x29, 32(x6)
  sd x29, 32(x28)
  ld x29, 40(x6)
  sd x29, 40(x28)
  ld x29, 48(x6)
  sd x29, 48(x28)
  ld x29, 56(x6)
  sd x29, 56(x28)
  ld x29, 64(x6)
  sd x29, 64(x28)
  ld x29, 72(x6)
  sd x29, 72(x28)
  ld x29, 80(x6)
  sd x29, 80(x28)
  ld x29, 88(x6)
  sd x29, 88(x28)
  ld x29, 96(x6)
  sd x29, 96(x28)
  ld x29, 104(x6)
  sd x29, 104(x28)
  ld x29, 112(x6)
  sd x29, 112(x28)
  ld x29, 120(x6)
  sd x29, 120(x28)
  addi x5, x5, 1
  jal x0, .-360
  li x5, 1
  sd x5, 0(x16)
  mv x10, x14
  li x11, 1
  jalr x0, 0(x1)
  mv x10, x14
  li x11, 0
  jalr x0, 0(x1)
