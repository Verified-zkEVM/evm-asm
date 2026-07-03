nibbles_common_prefix_len:
  # min(a_count, b_count)
  bltu a1, a3, .Lncpl_min_ok
  mv a1, a3
.Lncpl_min_ok:
  li t0, 0                   # cpl accumulator
  mv t1, a0                  # a cursor
  mv t2, a2                  # b cursor
.Lncpl_loop:
  bge t0, a1, .Lncpl_done
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bne t3, t4, .Lncpl_done
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, 1
  j .Lncpl_loop
.Lncpl_done:
  sd t0, 0(a4)
  li a0, 0
  ret
