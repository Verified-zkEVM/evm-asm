witness_codes_index_build:
  addi x2, x2, -96
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
  la x5, wcidx_enabled
  sd x0, 0(x5)
  mv x8, x10
  mv x9, x11
  la x5, wcidx_build_status
  sd x0, 0(x5)
  la x5, wcidx_build_section_len
  sd x9, 0(x5)
  la x5, wcidx_build_count
  sd x0, 0(x5)
  la x5, wclh_lookup_calls
  sd x0, 0(x5)
  la x5, wclh_indexed_calls
  sd x0, 0(x5)
  la x5, wclh_indexed_hits
  sd x0, 0(x5)
  la x5, wclh_indexed_misses
  sd x0, 0(x5)
  la x5, wclh_linear_calls
  sd x0, 0(x5)
  la x5, wclh_linear_hits
  sd x0, 0(x5)
  la x5, wclh_linear_misses
  sd x0, 0(x5)
  la x5, wclh_linear_iterations
  sd x0, 0(x5)
  la x5, wclh_linear_last_section_len
  sd x0, 0(x5)
  la x5, wclh_linear_max_section_len
  sd x0, 0(x5)
  beq x9, x0, .+168
  li x5, 4
  bltu x9, x5, .+328
  lwu x5, 0(x8)
  andi x6, x5, 3
  bne x6, x0, .+316
  bltu x9, x5, .+312
  srli x18, x5, 2
  la x6, wcidx_build_count
  sd x18, 0(x6)
  lui x6, 0x20
  bltu x6, x18, .+288
  mv x19, x5
  li x20, 0
  beq x20, x18, .+112
  slli x5, x20, 2
  add x6, x8, x5
  lwu x21, 0(x6)
  bltu x21, x19, .+260
  bltu x9, x21, .+256
  addi x7, x20, 1
  beq x7, x18, .+24
  slli x28, x7, 2
  add x28, x8, x28
  lwu x22, 0(x28)
  bltu x9, x22, .+232
  jal x0, .+8
  mv x22, x9
  bltu x22, x21, .+220
  sub x23, x22, x21
  mv x10, x20
  jal x1, wcidx_record_ptr
  mv x24, x10
  add x10, x8, x21
  mv x11, x23
  mv x12, x24
  jal x1, zkvm_keccak256
  sd x21, 32(x24)
  sd x23, 40(x24)
  addi x20, x20, 1
  jal x0, .-104
  li x18, 0
  li x5, 2
  bltu x18, x5, .+100
  srli x20, x18, 1
  beq x20, x0, .+24
  addi x20, x20, -1
  mv x10, x20
  mv x11, x18
  jal x1, wcidx_sift_down
  jal x0, .-20
  mv x20, x18
  li x5, 1
  bgeu x5, x20, .+60
  addi x20, x20, -1
  li x10, 0
  jal x1, wcidx_record_ptr
  mv x24, x10
  mv x10, x20
  jal x1, wcidx_record_ptr
  mv x25, x10
  mv x10, x24
  mv x11, x25
  jal x1, wcidx_swap_records
  li x10, 0
  mv x11, x20
  jal x1, wcidx_sift_down
  jal x0, .-60
  la x5, wcidx_section_ptr
  sd x8, 0(x5)
  la x5, wcidx_section_len
  sd x9, 0(x5)
  la x5, wcidx_count
  sd x18, 0(x5)
  li x6, 1
  la x5, wcidx_enabled
  sd x6, 0(x5)
  li x10, 0
  jal x0, .+24
  li x6, 1
  la x5, wcidx_build_status
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
  ld x23, 64(x2)
  ld x24, 72(x2)
  ld x25, 80(x2)
  addi x2, x2, 96
  jalr x0, 0(x1)
