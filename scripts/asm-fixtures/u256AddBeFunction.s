u256_add_be:
  li t0, 31                  # byte index (LSB first)
  li t1, 0                   # carry
.Lu256a_loop:
  add t2, a0, t0
  add t3, a1, t0
  add t4, a2, t0
  lbu t5, 0(t2)
  lbu t6, 0(t3)
  add t5, t5, t6
  add t5, t5, t1             # + carry-in
  srli t1, t5, 8             # carry-out
  andi t5, t5, 0xff          # masked sum byte
  sb t5, 0(t4)
  beqz t0, .Lu256a_done
  addi t0, t0, -1
  j .Lu256a_loop
.Lu256a_done:
  mv a0, t1                  # final carry = overflow flag
  ret
