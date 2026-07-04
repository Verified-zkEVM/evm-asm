blsk_neg_scalar:
  addi sp, sp, -16
  sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a0
  la a1, blsg_n_be
  li a2, 32
  jal ra, blsk_lt_be
  beqz a0, .Lblsk_negs_bad       # v >= BLS_MODULUS
  la t1, blsk_scal_be
  li t0, 16
.Lblsk_negs_pad:
  sb zero, 0(t1)
  addi t1, t1, 1
  addi t0, t0, -1
  bnez t0, .Lblsk_negs_pad
  mv t2, s0
  li t0, 32
.Lblsk_negs_copy:
  lbu t3, 0(t2)
  sb t3, 0(t1)
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  bnez t0, .Lblsk_negs_copy
  la a0, blsk_scal_be
  la a1, blsk_scal_le
  jal ra, blsg_be_to_le
  la a0, blsk_negn_params
  .4byte 0x80b52073              # d = (v*(n-1) + 0) mod n = (n-v) mod n
  la a0, blsk_scal_le
  la a1, blsk_scal_be
  jal ra, blsg_le_to_be
  li a0, 0
  j .Lblsk_negs_ret
.Lblsk_negs_bad:
  li a0, 1
.Lblsk_negs_ret:
  ld ra, 0(sp); ld s0, 8(sp)
  addi sp, sp, 16
  ret
