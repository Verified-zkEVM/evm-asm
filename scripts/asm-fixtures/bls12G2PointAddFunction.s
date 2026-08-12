blsg2_point_add:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  mv a0, s0
  li a1, 192
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg2_add_p_finite
  mv a0, s1
  mv a1, s2
  jal ra, blsg2_copy192          # P = inf: result = Q
  mv a0, s2
  li a1, 192
  jal ra, blsg_is_zero_n
  j .Lblsg2_add_ret
.Lblsg2_add_p_finite:
  mv a0, s1
  li a1, 192
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg2_add_q_finite
  mv a0, s0
  mv a1, s2
  jal ra, blsg2_copy192          # Q = inf: result = P (finite)
  li a0, 0
  j .Lblsg2_add_ret
.Lblsg2_add_q_finite:
  mv a0, s0
  mv a1, s1
  li a2, 96
  jal ra, blsg2_eq_n
  beqz a0, .Lblsg2_add_distinct_x
  addi a0, s0, 96
  addi a1, s1, 96
  li a2, 96
  jal ra, blsg2_eq_n
  beqz a0, .Lblsg2_add_inf       # x equal, y opposite: P + (-P) = inf
  mv a0, s0
  mv a1, s2
  jal ra, blsg2_point_dbl        # x and y equal: P + P
  j .Lblsg2_add_ret
.Lblsg2_add_distinct_x:
  addi a0, s1, 96
  la a1, blsg2_lam
  li a2, 12
  jal ra, blsf_copy_quads        # lam = y2
  la a0, blsg2_lam
  addi a1, s0, 96
  jal ra, blsg2_fp2_sub          # lam = y2 - y1
  mv a0, s1
  la a1, blsg2_den
  li a2, 12
  jal ra, blsf_copy_quads        # den = x2
  la a0, blsg2_den
  mv a1, s0
  jal ra, blsg2_fp2_sub          # den = x2 - x1
  la a0, blsg2_den
  la a1, blsg2_inv_out
  jal ra, blsg2_fp2_inv
  la a0, blsg2_lam
  la a1, blsg2_inv_out
  jal ra, blsg2_fp2_mul          # lam = (y2-y1)/(x2-x1)
  mv a0, s0
  mv a1, s1
  mv a2, s2
  jal ra, blsg2_chord_tail
  li a0, 0
  j .Lblsg2_add_ret
.Lblsg2_add_inf:
  mv a0, s2
  jal ra, blsg2_zero192
  li a0, 1
.Lblsg2_add_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
