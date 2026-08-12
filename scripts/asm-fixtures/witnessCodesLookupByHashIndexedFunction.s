witness_codes_lookup_by_hash_indexed:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  mv x8, x12
  mv x9, x13
  mv x18, x14
  li x19, 0
  la x5, wcidx_count
  ld x20, 0(x5)
  bgeu x19, x20, .+92
  add x21, x19, x20
  srli x21, x21, 1
  mv x10, x21
  jal x1, wcidx_record_ptr
  mv x22, x10
  mv x10, x22
  mv x11, x8
  jal x1, wcidx_cmp32
  li x5, 1
  beq x10, x5, .+28
  li x5, 0
  beq x10, x5, .+12
  mv x20, x21
  jal x0, .-56
  addi x19, x21, 1
  jal x0, .-64
  ld x5, 32(x22)
  sd x5, 0(x9)
  ld x5, 40(x22)
  sd x5, 0(x18)
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
  addi x2, x2, 64
  jalr x0, 0(x1)
