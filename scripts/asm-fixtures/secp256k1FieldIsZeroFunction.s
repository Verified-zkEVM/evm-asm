secf_is_zero32:
  li t0, 32
  mv t1, a0
.Lsecf_is_zero_loop:
  beqz t0, .Lsecf_is_zero_yes
  lbu t2, 0(t1)
  bnez t2, .Lsecf_is_zero_no
  addi t1, t1, 1
  addi t0, t0, -1
  j .Lsecf_is_zero_loop
.Lsecf_is_zero_yes:
  li a0, 1
  ret
.Lsecf_is_zero_no:
  li a0, 0
  ret
