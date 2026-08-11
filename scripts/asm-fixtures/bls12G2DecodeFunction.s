blsg2_decode_g2:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0
  mv s1, a1
  li s2, 0                       # felt index 0..3
.Lblsg2_dec_felt:
  slli t0, s2, 6
  add a0, s0, t0
  li a1, 16
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg2_dec_bad       # pad nonzero
  slli t0, s2, 6
  add a0, s0, t0
  addi a0, a0, 16
  jal ra, blsg_lt_p
  beqz a0, .Lblsg2_dec_bad       # value >= p
  slli t0, s2, 6
  add a0, s0, t0
  addi a0, a0, 16
  slli t0, s2, 4
  slli t1, s2, 5
  add t0, t0, t1                 # 48 * felt index
  add a1, s1, t0
  jal ra, blsg_be_to_le
  addi s2, s2, 1
  li t0, 4
  bne s2, t0, .Lblsg2_dec_felt
  mv a0, s1
  li a1, 192
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg2_dec_finite
  li a0, 1                       # all-zero = infinity, valid
  j .Lblsg2_dec_ret
.Lblsg2_dec_finite:
  mv a0, s1
  la a1, blsg2_oc_t
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blsg2_oc_t
  mv a1, s1
  jal ra, blsg2_fp2_mul          # x^2
  la a0, blsg2_oc_t
  mv a1, s1
  jal ra, blsg2_fp2_mul          # x^3
  la a0, blsg2_oc_t
  la a1, blsg2_b_le
  jal ra, blsg2_fp2_add          # x^3 + (4 + 4u)
  addi a0, s1, 96
  la a1, blsg2_oc_y2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blsg2_oc_y2
  addi a1, s1, 96
  jal ra, blsg2_fp2_mul          # y^2
  la a0, blsg2_oc_t
  la a1, blsg2_oc_y2
  li a2, 96
  jal ra, blsg2_eq_n
  beqz a0, .Lblsg2_dec_bad
  li a0, 0
  j .Lblsg2_dec_ret
.Lblsg2_dec_bad:
  li a0, 2
.Lblsg2_dec_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
