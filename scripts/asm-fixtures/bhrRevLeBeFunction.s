bhr_rev_le_be:
  add t0, a0, a1              # src end
  mv t1, a2                   # dst
  mv t2, a1
.Lbhrev_loop:
  beqz t2, .Lbhrev_done
  addi t0, t0, -1
  lbu t3, 0(t0)
  sb t3, 0(t1)
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lbhrev_loop
.Lbhrev_done:
  ret
