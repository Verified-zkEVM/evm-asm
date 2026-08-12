blsk_decompress_g1:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0
  mv s1, a1
  lbu s2, 0(s0)                  # flag byte: c/b/a at bits 7/6/5
  andi t0, s2, 0x80
  beqz t0, .Lblsk_dec_bad        # c_flag must be 1
  andi t0, s2, 0x40
  beqz t0, .Lblsk_dec_finite
  li t0, 0xc0
  bne s2, t0, .Lblsk_dec_bad     # infinity needs a_flag = 0
  addi a0, s0, 1
  li a1, 47
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsk_dec_bad        # infinity needs a zero payload
  mv a0, s1
  jal ra, blsg_zero96            # compact infinity = (0,0)
  li a0, 1
  j .Lblsk_dec_ret
.Lblsk_dec_finite:
  mv t1, s0
  mv t2, s1
  li t0, 48
.Lblsk_dec_copyx:
  lbu t3, 0(t1)
  sb t3, 0(t2)
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  bnez t0, .Lblsk_dec_copyx
  lbu t3, 0(s1)
  andi t3, t3, 0x1f
  sb t3, 0(s1)
  mv a0, s1
  jal ra, blsg_lt_p
  beqz a0, .Lblsk_dec_bad        # x >= p
  mv a0, s1
  la a1, blsk_x_le
  jal ra, blsg_be_to_le
  la a0, blsk_x_le
  la a1, blsk_x_le
  la a2, blsk_rhs_le
  jal ra, blsg2_fp_mul           # x^2
  la a0, blsk_rhs_le
  la a1, blsk_x_le
  la a2, blsk_rhs_le
  jal ra, blsg2_fp_mul           # x^3
  la a0, blsk_rhs_le
  la a1, blsg2_b_le
  la a2, blsk_rhs_le
  jal ra, blsg2_fp_add           # x^3 + 4
  la a0, blsk_rhs_le
  la a1, blsk_y_le
  jal ra, blsk_fp_pow_q14
  la a0, blsk_y_le
  la a1, blsk_y_le
  la a2, blsk_t_le
  jal ra, blsg2_fp_mul
  la a0, blsk_t_le
  la a1, blsk_rhs_le
  li a2, 48
  jal ra, blsg2_eq_n
  beqz a0, .Lblsk_dec_bad        # x^3 + 4 is not a square
  la a0, blsk_y_le
  addi a1, s1, 48
  jal ra, blsg_le_to_be
  addi a0, s1, 48
  la a1, blsk_phalf_be
  li a2, 48
  jal ra, blsk_lt_be             # 1 iff y < (p+1)/2
  xori t0, a0, 1                 # t0 = (2y)//p
  srli t1, s2, 5
  andi t1, t1, 1                 # t1 = a_flag
  beq t0, t1, .Lblsk_dec_signok
  la a0, blsk_y_le
  la a1, blsg2_pm1_le
  la a2, blsk_y_le
  jal ra, blsg2_fp_mul           # y = p - y
  la a0, blsk_y_le
  addi a1, s1, 48
  jal ra, blsg_le_to_be
.Lblsk_dec_signok:
  li a0, 0
  j .Lblsk_dec_ret
.Lblsk_dec_bad:
  li a0, 2
.Lblsk_dec_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
