stage_runtime_payload_code:
  addi x2, x2, -72
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  sd x23, 64(x2)
  mv x8, x11
  mv x9, x10
  mv x18, x12
  mv x19, x13
  mv x20, x14
  mv x22, x15
  mv x23, x16
  ld x5, 0(x9)
  beq x5, x0, .+12
  li x10, 1
  jal x0, .+844
  addi x5, x20, 7
  andi x5, x5, -8
  ld x17, 64(x9)
  addi x31, x17, 7
  andi x31, x31, -8
  slli x16, x23, 6
  add x6, x5, x31
  add x6, x6, x16
  addi x6, x6, 80
  la x30, m28_blob_stage_count
  ld x30, 0(x30)
  slli x30, x30, 5
  add x6, x6, x30
  la x30, m29_stage_count
  ld x30, 0(x30)
  slli x30, x30, 5
  add x6, x6, x30
  la x30, srpc_env_base
  sd x6, 0(x30)
  addi x7, x6, 504
  addi x7, x7, 7
  andi x7, x7, -8
  mv x28, x8
  beq x7, x0, .+20
  sd x0, 0(x28)
  addi x28, x28, 8
  addi x7, x7, -8
  jal x0, .-16
  sd x20, 0(x8)
  addi x28, x8, 8
  mv x29, x19
  mv x30, x20
  beq x30, x0, .+28
  lbu x31, 0(x29)
  sb x31, 0(x28)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x30, x30, -1
  jal x0, .-24
  add x28, x8, x5
  ld x17, 64(x9)
  sd x17, 8(x28)
  addi x28, x28, 16
  ld x29, 56(x9)
  mv x30, x17
  beq x30, x0, .+28
  lbu x31, 0(x29)
  sb x31, 0(x28)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x30, x30, -1
  jal x0, .-24
  add x28, x8, x5
  ld x17, 64(x9)
  addi x31, x17, 7
  andi x31, x31, -8
  add x28, x28, x31
  sd x23, 16(x28)
  addi x28, x28, 24
  mv x29, x22
  slli x30, x23, 6
  beq x30, x0, .+28
  lbu x31, 0(x29)
  sb x31, 0(x28)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x30, x30, -1
  jal x0, .-24
  mv x21, x28
  addi x10, x18, 520
  jal x1, bgv_u64le
  mv x11, x21
  jal x1, amsterdam_blob_gas_price_u256
  mv x28, x21
  la x29, m28_blob_stage_count
  ld x5, 0(x29)
  sd x5, 32(x28)
  addi x29, x28, 40
  la x30, m28_blob_stage_table
  slli x31, x5, 5
  beq x31, x0, .+28
  lbu x15, 0(x30)
  sb x15, 0(x29)
  addi x30, x30, 1
  addi x29, x29, 1
  addi x31, x31, -1
  jal x0, .-24
  slli x5, x5, 5
  la x29, m29_stage_cur
  ld x30, 0(x29)
  add x29, x28, x5
  sd x30, 40(x29)
  la x29, m29_stage_count
  ld x31, 0(x29)
  add x29, x28, x5
  sd x31, 48(x29)
  add x29, x28, x5
  addi x29, x29, 56
  la x30, m29_stage_table
  slli x31, x31, 5
  beq x31, x0, .+28
  lbu x15, 0(x30)
  sb x15, 0(x29)
  addi x30, x30, 1
  addi x29, x29, 1
  addi x31, x31, -1
  jal x0, .-24
  la x6, srpc_env_base
  ld x6, 0(x6)
  add x21, x8, x6
  addi x28, x18, 32
  addi x29, x21, 192
  li x30, 0
  li x31, 20
  beq x30, x31, .+36
  add x15, x28, x30
  lbu x16, 0(x15)
  li x15, 19
  sub x15, x15, x30
  add x15, x29, x15
  sb x16, 0(x15)
  addi x30, x30, 1
  jal x0, .-36
  ld x28, 404(x18)
  sd x28, 256(x21)
  ld x28, 428(x18)
  sd x28, 224(x21)
  addi x28, x18, 372
  addi x29, x21, 288
  li x30, 0
  li x31, 32
  beq x30, x31, .+36
  add x15, x28, x30
  lbu x16, 0(x15)
  li x15, 31
  sub x15, x15, x30
  add x15, x29, x15
  sb x16, 0(x15)
  addi x30, x30, 1
  jal x0, .-36
  ld x28, 412(x18)
  sd x28, 320(x21)
  addi x28, x18, 440
  ld x29, 0(x28)
  sd x29, 352(x21)
  ld x29, 8(x28)
  sd x29, 360(x21)
  ld x29, 16(x28)
  sd x29, 368(x21)
  ld x29, 24(x28)
  sd x29, 376(x21)
  la x28, bv_chain_id
  ld x29, 0(x28)
  sd x29, 384(x21)
  addi x28, x9, 72
  mv x29, x21
  li x30, 0
  li x31, 20
  beq x30, x31, .+36
  li x15, 19
  sub x15, x15, x30
  add x15, x28, x15
  lbu x16, 0(x15)
  add x15, x29, x30
  sb x16, 0(x15)
  addi x30, x30, 1
  jal x0, .-36
  addi x28, x9, 96
  addi x29, x21, 96
  li x30, 0
  li x31, 32
  beq x30, x31, .+36
  add x15, x28, x30
  lbu x16, 0(x15)
  li x15, 31
  sub x15, x15, x30
  add x15, x29, x15
  sb x16, 0(x15)
  addi x30, x30, 1
  jal x0, .-36
  li x28, 0
  li x29, 0
  li x30, 8
  beq x29, x30, .+36
  add x30, x18, x29
  addi x30, x30, 532
  lbu x31, 0(x30)
  slli x15, x29, 3
  sll x31, x31, x15
  or x28, x28, x31
  addi x29, x29, 1
  jal x0, .-36
  sd x28, 416(x21)
  ld x28, 40(x9)
  sd x28, 448(x21)
  li x28, 1
  sd x28, 456(x21)
  ld x28, 48(x9)
  sd x28, 464(x21)
  li x10, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  ld x22, 56(x2)
  ld x23, 64(x2)
  addi x2, x2, 72
  jalr x0, 0(x1)
