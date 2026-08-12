blsg_decode_g1:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  mv a0, s0
  li a1, 16
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg_dec_bad        # x pad nonzero
  addi a0, s0, 64
  li a1, 16
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg_dec_bad        # y pad nonzero
  addi t1, s0, 16
  mv t2, s1
  li t0, 48
.Lblsg_dec_cx:
  lbu t3, 0(t1)
  sb t3, 0(t2)
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  bnez t0, .Lblsg_dec_cx
  addi t1, s0, 80
  addi t2, s1, 48
  li t0, 48
.Lblsg_dec_cy:
  lbu t3, 0(t1)
  sb t3, 0(t2)
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  bnez t0, .Lblsg_dec_cy
  mv a0, s1
  jal ra, blsg_lt_p
  beqz a0, .Lblsg_dec_bad        # x >= p
  addi a0, s1, 48
  jal ra, blsg_lt_p
  beqz a0, .Lblsg_dec_bad        # y >= p
  mv a0, s1
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg_dec_finite
  li a0, 1                       # (0,0) = infinity, valid
  j .Lblsg_dec_ret
.Lblsg_dec_finite:
  mv a0, s1
  jal ra, blsg_on_curve
  beqz a0, .Lblsg_dec_bad
  li a0, 0
  j .Lblsg_dec_ret
.Lblsg_dec_bad:
  li a0, 2
.Lblsg_dec_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
