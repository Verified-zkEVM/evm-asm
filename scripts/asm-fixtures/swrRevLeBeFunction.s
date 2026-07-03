swr_rev_le_be:
  add t0, a0, a1
  mv t1, a2
  mv t2, a1
.Lswrrev_loop:
  beqz t2, .Lswrrev_done
  addi t0, t0, -1
  lbu t3, 0(t0); sb t3, 0(t1)
  addi t1, t1, 1; addi t2, t2, -1
  j .Lswrrev_loop
.Lswrrev_done:
  ret
