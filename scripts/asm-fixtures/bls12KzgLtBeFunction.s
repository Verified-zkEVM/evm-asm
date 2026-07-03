blsk_lt_be:
  mv t0, a0
  mv t1, a1
  mv t2, a2
.Lblsk_ltbe_loop:
  beqz t2, .Lblsk_ltbe_no        # equal => not less
  lbu t3, 0(t0)
  lbu t4, 0(t1)
  bltu t3, t4, .Lblsk_ltbe_yes
  bltu t4, t3, .Lblsk_ltbe_no
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lblsk_ltbe_loop
.Lblsk_ltbe_yes:
  li a0, 1
  ret
.Lblsk_ltbe_no:
  li a0, 0
  ret
