secf_reduce_once_n:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  mv a0, s0
  la a1, secf_n_be
  la a2, secf_cmp
  jal ra, u256_lt_be
  la t0, secf_cmp
  ld t1, 0(t0)
  bnez t1, .Lsecf_reducen_copy
  mv a0, s0
  la a1, secf_n_be
  mv a2, s1
  jal ra, u256_sub_be
  li a0, 1
  j .Lsecf_reducen_done
.Lsecf_reducen_copy:
  mv a0, s0
  mv a1, s1
  jal ra, secf_copy32
  li a0, 0
.Lsecf_reducen_done:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  addi sp, sp, 32
  ret
