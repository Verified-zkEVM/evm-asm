wcidx_sift_down:
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
  slli x18, x8, 1
  addi x18, x18, 1
  bgeu x18, x9, .+160
  mv x19, x8
  mv x10, x19
  jal x1, wcidx_record_ptr
  mv x20, x10
  mv x10, x18
  jal x1, wcidx_record_ptr
  mv x21, x10
  mv x10, x20
  mv x11, x21
  jal x1, wcidx_cmp32
  li x5, 0
  bne x10, x5, .+8
  mv x19, x18
  addi x22, x18, 1
  bgeu x22, x9, .+52
  mv x10, x19
  jal x1, wcidx_record_ptr
  mv x20, x10
  mv x10, x22
  jal x1, wcidx_record_ptr
  mv x21, x10
  mv x10, x20
  mv x11, x21
  jal x1, wcidx_cmp32
  li x5, 0
  bne x10, x5, .+8
  mv x19, x22
  beq x19, x8, .+48
  mv x10, x8
  jal x1, wcidx_record_ptr
  mv x20, x10
  mv x10, x19
  jal x1, wcidx_record_ptr
  mv x21, x10
  mv x10, x20
  mv x11, x21
  jal x1, wcidx_swap_records
  mv x8, x19
  jal x0, .-164
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
