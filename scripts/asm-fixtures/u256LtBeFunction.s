u256_lt_be:
  li t0, 32                  # byte counter (MSB-first)
  mv t1, a0                  # a cursor
  mv t2, a1                  # b cursor
.Lulb_loop:
  beqz t0, .Lulb_equal
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bltu t3, t4, .Lulb_less
  bltu t4, t3, .Lulb_greater
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  j .Lulb_loop
.Lulb_less:
  li t5, 1
  sd t5, 0(a2)
  li a0, 0
  ret
.Lulb_greater:
.Lulb_equal:
  sd zero, 0(a2)
  li a0, 0
  ret
