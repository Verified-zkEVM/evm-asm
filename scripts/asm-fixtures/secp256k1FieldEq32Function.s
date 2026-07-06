secf_eq32:
  li t0, 32
  mv t1, a0
  mv t2, a1
.Lsecf_eq_loop:
  beqz t0, .Lsecf_eq_yes
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bne t3, t4, .Lsecf_eq_no
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  j .Lsecf_eq_loop
.Lsecf_eq_yes:
  li a0, 1
  ret
.Lsecf_eq_no:
  li a0, 0
  ret
