u256_sub_be:
  li t0, 31                  # byte index (LSB first)
  li t1, 0                   # borrow
.Lu256s_loop:
  add t2, a0, t0
  add t3, a1, t0
  add t4, a2, t0
  lbu t5, 0(t2)
  lbu t6, 0(t3)
  sub t5, t5, t6
  sub t5, t5, t1             # - borrow-in
  sltz t1, t5                # borrow-out = (t5 < 0)
  andi t5, t5, 0xff          # masked diff byte
  sb t5, 0(t4)
  beqz t0, .Lu256s_done
  addi t0, t0, -1
  j .Lu256s_loop
.Lu256s_done:
  mv a0, t1                  # final borrow = underflow flag
  ret
