running_bloom_zero:
  li t0, 32                  # 256 bytes / 8 bytes per word
  mv t1, a0                  # bloom cursor
.Lrbz_loop:
  beqz t0, .Lrbz_done
  sd zero, 0(t1)
  addi t1, t1, 8
  addi t0, t0, -1
  j .Lrbz_loop
.Lrbz_done:
  li a0, 0
  ret
