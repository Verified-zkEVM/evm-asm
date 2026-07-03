bnf_lt_p:
  la t0, bnf_p_be
  li t1, 32
  mv t2, a0
.Lbnf_ltp_loop:
  beqz t1, .Lbnf_ltp_no       # equal => not less
  lbu t3, 0(t2)
  lbu t4, 0(t0)
  bltu t3, t4, .Lbnf_ltp_yes
  bltu t4, t3, .Lbnf_ltp_no
  addi t2, t2, 1
  addi t0, t0, 1
  addi t1, t1, -1
  j .Lbnf_ltp_loop
.Lbnf_ltp_yes:
  li a0, 1
  ret
.Lbnf_ltp_no:
  li a0, 0
  ret
