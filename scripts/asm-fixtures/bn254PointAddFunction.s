bnc_point_add:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  mv a0, s0
  jal ra, bnc_is_inf64
  beqz a0, .Lbnc_add_p_finite
  mv a0, s1
  mv a1, s2
  jal ra, bnc_copy64            # P = inf: result = Q
  mv a0, s2
  jal ra, bnc_is_inf64
  j .Lbnc_add_ret
.Lbnc_add_p_finite:
  mv a0, s1
  jal ra, bnc_is_inf64
  beqz a0, .Lbnc_add_q_finite
  mv a0, s0
  mv a1, s2
  jal ra, bnc_copy64            # Q = inf: result = P (finite)
  li a0, 0
  j .Lbnc_add_ret
.Lbnc_add_q_finite:
  mv a0, s0
  mv a1, s1
  jal ra, bnf_eq32
  beqz a0, .Lbnc_add_distinct_x
  addi a0, s0, 32
  addi a1, s1, 32
  jal ra, bnf_eq32
  beqz a0, .Lbnc_add_inf        # x equal, y opposite: P + (-P) = inf
  mv a0, s0
  mv a1, s2
  jal ra, bnc_point_dbl         # x and y equal: P + P
  j .Lbnc_add_ret
.Lbnc_add_distinct_x:
  mv a0, s0
  la a1, bnc_le_p1
  jal ra, bnf_be_to_le          # p1.x
  addi a0, s0, 32
  la a1, bnc_le_p1
  addi a1, a1, 32
  jal ra, bnf_be_to_le          # p1.y
  mv a0, s1
  la a1, bnc_le_p2
  jal ra, bnf_be_to_le          # p2.x
  addi a0, s1, 32
  la a1, bnc_le_p2
  addi a1, a1, 32
  jal ra, bnf_be_to_le          # p2.y
  la t0, bnc_add_params
  .4byte 0x8062a073             # csrs 0x806, t0 -> Bn254CurveAdd
  la a0, bnc_le_p1
  mv a1, s2
  jal ra, bnf_le_to_be          # out.x
  la a0, bnc_le_p1
  addi a0, a0, 32
  addi a1, s2, 32
  jal ra, bnf_le_to_be          # out.y
  li a0, 0
  j .Lbnc_add_ret
.Lbnc_add_inf:
  mv a0, s2
  jal ra, bnc_zero64
  li a0, 1
.Lbnc_add_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
