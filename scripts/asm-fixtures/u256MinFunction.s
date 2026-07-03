u256_min:
  li t0, 0                   # byte index
  li t6, 32
.Lumin_lt_loop:
  beq t0, t6, .Lumin_pick_a  # all bytes equal → return a
  add t1, a0, t0
  add t2, a1, t0
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bltu t3, t4, .Lumin_pick_a # a < b → return a
  bgtu t3, t4, .Lumin_pick_b # a > b → return b
  addi t0, t0, 1
  j .Lumin_lt_loop
.Lumin_pick_a:
  mv t0, a0
  j .Lumin_copy
.Lumin_pick_b:
  mv t0, a1
.Lumin_copy:
  ld t1,  0(t0); sd t1,  0(a2)
  ld t1,  8(t0); sd t1,  8(a2)
  ld t1, 16(t0); sd t1, 16(a2)
  ld t1, 24(t0); sd t1, 24(a2)
  li a0, 0
  ret
