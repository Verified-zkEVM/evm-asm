blq_zero:
  li t2, 72
.Lblq_zero_loop:
  sd zero, 0(a0)
  addi a0, a0, 8
  addi t2, t2, -1
  bnez t2, .Lblq_zero_loop
  ret
