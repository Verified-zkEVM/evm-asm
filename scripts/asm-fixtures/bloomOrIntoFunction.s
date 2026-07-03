bloom_or_into:
  li t0, 32                  # 256 bytes / 8 bytes per word
  mv t1, a0                  # dst cursor
  mv t2, a1                  # src cursor
.Lboi_loop:
  beqz t0, .Lboi_done
  ld t3, 0(t1)
  ld t4, 0(t2)
  or t3, t3, t4
  sd t3, 0(t1)
  addi t1, t1, 8
  addi t2, t2, 8
  addi t0, t0, -1
  j .Lboi_loop
.Lboi_done:
  li a0, 0
  ret
