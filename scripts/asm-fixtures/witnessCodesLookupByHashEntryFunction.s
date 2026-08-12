witness_codes_lookup_by_hash:
  addi x2, x2, -64
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
  la x5, wclh_lookup_calls
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  la x5, wcidx_enabled
  ld x5, 0(x5)
  beq x5, x0, .+132
  la x5, wcidx_section_ptr
  ld x5, 0(x5)
  bne x8, x5, .+116
  la x5, wcidx_section_len
  ld x5, 0(x5)
  bne x9, x5, .+100
  mv x10, x8
  mv x11, x9
  mv x12, x18
  mv x13, x19
  mv x14, x20
  la x5, wclh_indexed_calls
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  jal x1, witness_codes_lookup_by_hash_indexed
  bne x10, x0, .+28
  la x5, wclh_indexed_hits
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  jal x0, .+388
  la x5, wclh_indexed_misses
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  jal x0, .+364
  la x5, wclh_linear_calls
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  la x5, wclh_linear_last_section_len
  sd x9, 0(x5)
  la x5, wclh_linear_max_section_len
  ld x6, 0(x5)
  bgeu x6, x9, .+8
  sd x9, 0(x5)
  beq x9, x0, .+284
  li x5, 4
  bltu x9, x5, .+276
  lwu x5, 0(x8)
  andi x6, x5, 3
  bne x6, x0, .+264
  bltu x9, x5, .+260
  srli x21, x5, 2
  li x22, 0
  beq x22, x21, .+248
  slli x5, x22, 2
  add x6, x8, x5
  lwu x7, 0(x6)
  bltu x9, x7, .+232
  add x10, x8, x7
  addi x28, x22, 1
  beq x28, x21, .+28
  slli x28, x28, 2
  add x28, x8, x28
  lwu x29, 0(x28)
  bltu x9, x29, .+204
  add x29, x8, x29
  jal x0, .+8
  add x29, x8, x9
  bltu x29, x10, .+188
  sub x11, x29, x10
  la x12, wclh_scratch_hash
  la x5, wclh_linear_iterations
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  jal x1, zkvm_keccak256
  la x5, wclh_scratch_hash
  mv x6, x18
  ld x7, 0(x5)
  ld x28, 0(x6)
  bne x7, x28, .+120
  ld x7, 8(x5)
  ld x28, 8(x6)
  bne x7, x28, .+108
  ld x7, 16(x5)
  ld x28, 16(x6)
  bne x7, x28, .+96
  ld x7, 24(x5)
  ld x28, 24(x6)
  bne x7, x28, .+84
  slli x5, x22, 2
  add x6, x8, x5
  lwu x7, 0(x6)
  sd x7, 0(x19)
  addi x28, x22, 1
  beq x28, x21, .+24
  slli x28, x28, 2
  add x28, x8, x28
  lwu x29, 0(x28)
  sub x29, x29, x7
  jal x0, .+8
  sub x29, x9, x7
  sd x29, 0(x20)
  la x5, wclh_linear_hits
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  li x10, 0
  jal x0, .+36
  addi x22, x22, 1
  jal x0, .-244
  la x5, wclh_linear_misses
  ld x6, 0(x5)
  addi x6, x6, 1
  sd x6, 0(x5)
  li x10, 1
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  ld x22, 56(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
