bytes_to_nibbles:
  mv t0, a0                  # src cursor
  mv t1, a2                  # dst cursor
  mv t2, a1                  # remaining
  li t6, 0                   # emitted count
.Lbtn_loop:
  beqz t2, .Lbtn_done
  lbu t3, 0(t0)
  srli t4, t3, 4
  andi t5, t3, 0xf
  sb t4, 0(t1)
  sb t5, 1(t1)
  addi t0, t0, 1
  addi t1, t1, 2
  addi t2, t2, -1
  addi t6, t6, 2
  j .Lbtn_loop
.Lbtn_done:
  mv a0, t6
  ret
