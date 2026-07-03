u256_max:
  li t0, 0                   # byte index
  li t6, 32
.Lumax_loop:
  beq t0, t6, .Lumax_pick_a  # all bytes equal → return a
  add t1, a0, t0
  add t2, a1, t0
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bgtu t3, t4, .Lumax_pick_a # a > b → return a
  bltu t3, t4, .Lumax_pick_b # a < b → return b
  addi t0, t0, 1
  j .Lumax_loop
.Lumax_pick_a:
  mv t0, a0
  j .Lumax_copy
.Lumax_pick_b:
  mv t0, a1
.Lumax_copy:
  ld t1,  0(t0); sd t1,  0(a2)
  ld t1,  8(t0); sd t1,  8(a2)
  ld t1, 16(t0); sd t1, 16(a2)
  ld t1, 24(t0); sd t1, 24(a2)
  li a0, 0
  ret
