blk2_st_le64:
  mv t0, a1
  mv t1, a0
  li t2, 8
.Lblk2_st_byte:
  andi a1, t0, 0xff
  sb a1, 0(t1)
  srli t0, t0, 8
  addi t1, t1, 1
  addi t2, t2, -1
  bnez t2, .Lblk2_st_byte
  ret
