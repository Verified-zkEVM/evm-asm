blk2_ld_le64:
  li t0, 0
  addi t1, a0, 7
  li t2, 8
.Lblk2_ld_byte:
  slli t0, t0, 8
  lbu a0, 0(t1)
  or t0, t0, a0
  addi t1, t1, -1
  addi t2, t2, -1
  bnez t2, .Lblk2_ld_byte
  mv a0, t0
  ret
