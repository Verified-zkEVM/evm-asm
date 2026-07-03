secp256k1_recover_r:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  mv s0, a0                 # r pointer
  mv s1, a1                 # recid
  mv s2, a2                 # output: x at s2, y at s2+32
  andi t0, s1, 2
  beqz t0, .Lrec_x_is_r
  # candidate x = r + n
  mv a0, s0
  la a1, secp256k1_n_be
  mv a2, s2
  jal ra, u256_add_be
  beqz a0, .Lrec_check_range
  li a0, 2                  # carry: x >= 2^256
  j .Lrec_done
.Lrec_check_range:
  mv a0, s2
  la a1, secp256k1_p_be
  la a2, secf_recover_cmp
  jal ra, u256_lt_be        # [cmp] = 1 iff x < p
  la t0, secf_recover_cmp
  ld t1, 0(t0)
  bnez t1, .Lrec_have_x
  li a0, 2                  # x >= p
  j .Lrec_done
.Lrec_x_is_r:
  mv a0, s0
  mv a1, s2
  jal ra, secf_copy32
.Lrec_have_x:
  # rhs = x^3 + 7
  mv a0, s2
  la a2, secf_recover_t
  jal ra, secf_square_mod_p     # t = x^2
  la a0, secf_recover_t
  mv a1, s2
  la a2, secf_recover_t
  jal ra, secf_mul_mod_p        # t = x^3
  la a0, secf_recover_t
  la a1, secp256k1_b_be
  la a2, secf_recover_rhs
  jal ra, secf_add_mod_p        # rhs = x^3 + 7
  # y = sqrt(rhs) into y slot
  la a0, secf_recover_rhs
  addi a1, s2, 32
  jal ra, secf_sqrt_mod_p
  beqz a0, .Lrec_have_y
  li a0, 1                  # rhs is not a quadratic residue
  j .Lrec_done
.Lrec_have_y:
  # match parity: desired = recid & 1, current = LSB of y
  addi t0, s2, 32
  lbu t1, 31(t0)            # least-significant byte of y
  andi t1, t1, 1
  andi t2, s1, 1
  beq t1, t2, .Lrec_ok
  # flip parity: y = p - y
  la a0, secp256k1_p_be
  addi a1, s2, 32
  addi a2, s2, 32
  jal ra, u256_sub_be
.Lrec_ok:
  li a0, 0
.Lrec_done:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  addi sp, sp, 48
  ret
