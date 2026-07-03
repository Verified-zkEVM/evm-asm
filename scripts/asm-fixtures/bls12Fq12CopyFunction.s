blq_copy:
  li t2, 72
.Lblq_copy_loop:
  ld t3, 0(a0)
  sd t3, 0(a1)
  addi a0, a0, 8
  addi a1, a1, 8
  addi t2, t2, -1
  bnez t2, .Lblq_copy_loop
  ret
