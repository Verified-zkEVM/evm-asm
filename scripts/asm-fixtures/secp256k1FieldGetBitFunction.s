secf_get_bit_lsb:
  srli t0, a1, 3             # byte index from the LSB
  li t1, 31
  sub t0, t1, t0             # BE byte offset
  add t0, a0, t0
  lbu t1, 0(t0)
  andi t2, a1, 7
  srl t1, t1, t2
  andi a0, t1, 1
  ret
