blsg_le_add:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  mv a0, s0
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg_ladd_p_finite
  mv a0, s1
  mv a1, s2
  jal ra, blsg_copy96            # P = inf: result = Q
  mv a0, s2
  li a1, 96
  jal ra, blsg_is_zero_n
  j .Lblsg_ladd_ret
.Lblsg_ladd_p_finite:
  mv a0, s1
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg_ladd_q_finite
  mv a0, s0
  mv a1, s2
  jal ra, blsg_copy96            # Q = inf: result = P (finite)
  li a0, 0
  j .Lblsg_ladd_ret
.Lblsg_ladd_q_finite:
  mv a0, s0
  mv a1, s1
  jal ra, blsg_eq48              # byte equality works on LE too
  beqz a0, .Lblsg_ladd_distinct
  addi a0, s0, 48
  addi a1, s1, 48
  jal ra, blsg_eq48
  beqz a0, .Lblsg_ladd_inf       # x equal, y opposite: inf
  mv a0, s0
  mv a1, s2
  jal ra, blsg_le_dbl            # x and y equal: P + P
  j .Lblsg_ladd_ret
.Lblsg_ladd_distinct:
  mv a0, s0
  la a1, blsf_p1
  li a2, 12
  jal ra, blsf_copy_quads
  mv a0, s1
  la a1, blsf_p2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blsf_curve_params
  .4byte 0x80c52073              # csrs 0x80C, a0 -> Bls12_381CurveAdd
  la a0, blsf_p1
  mv a1, s2
  li a2, 12
  jal ra, blsf_copy_quads
  li a0, 0
  j .Lblsg_ladd_ret
.Lblsg_ladd_inf:
  mv a0, s2
  jal ra, blsg_zero96
  li a0, 1
.Lblsg_ladd_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
