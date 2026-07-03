blq_set_one:
  addi sp, sp, -16
  sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a0
  jal ra, blq_zero
  li t0, 1
  sd t0, 0(s0)
  ld ra, 0(sp); ld s0, 8(sp)
  addi sp, sp, 16
  ret
