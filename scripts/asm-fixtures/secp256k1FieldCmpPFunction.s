secf_cmp_p:
  la t0, secp256k1_p_be
  li t1, 32
  mv t2, a0
.Lsecf_cmp_loop:
  beqz t1, .Lsecf_cmp_equal
  lbu t3, 0(t2)
  lbu t4, 0(t0)
  bltu t3, t4, .Lsecf_cmp_less
  bltu t4, t3, .Lsecf_cmp_greater
  addi t2, t2, 1
  addi t0, t0, 1
  addi t1, t1, -1
  j .Lsecf_cmp_loop
.Lsecf_cmp_less:
  sd zero, 0(a1)
  li a0, 0
  ret
.Lsecf_cmp_equal:
  li t0, 1
  sd t0, 0(a1)
  li a0, 0
  ret
.Lsecf_cmp_greater:
  li t0, 2
  sd t0, 0(a1)
  li a0, 0
  ret
