bloom_eq:
  li t0, 32                  # 256 bytes / 8 bytes per word
  mv t1, a0
  mv t2, a1
  li t5, 0                   # diff_accumulator
.Lbeq_loop:
  beqz t0, .Lbeq_done
  ld t3, 0(t1)
  ld t4, 0(t2)
  xor t3, t3, t4
  or  t5, t5, t3             # accumulate any nonzero diff
  addi t1, t1, 8
  addi t2, t2, 8
  addi t0, t0, -1
  j .Lbeq_loop
.Lbeq_done:
  # is_equal = (diff_accumulator == 0)
  seqz t5, t5
  sd t5, 0(a2)
  li a0, 0
  ret
