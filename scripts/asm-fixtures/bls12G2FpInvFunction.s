blsg2_fp_inv:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                      # base
  mv s1, a1                      # result
  la a0, blsf_le_one
  la a1, blsg2_facc
  li a2, 6
  jal ra, blsf_copy_quads        # acc = 1
  li s2, 0                       # exponent byte index
.Lblsg2_inv_byte:
  li t0, 48
  bgeu s2, t0, .Lblsg2_inv_done
  la t0, blsg2_p_minus_2_be
  add t0, t0, s2
  lbu s3, 0(t0)
  li s4, 128
.Lblsg2_inv_bit:
  beqz s4, .Lblsg2_inv_next
  la a0, blsg2_facc
  la a1, blsg2_facc
  la a2, blsg2_facc
  jal ra, blsg2_fp_mul           # acc = acc^2
  and t0, s3, s4
  beqz t0, .Lblsg2_inv_skip
  la a0, blsg2_facc
  mv a1, s0
  la a2, blsg2_facc
  jal ra, blsg2_fp_mul           # acc *= base
.Lblsg2_inv_skip:
  srli s4, s4, 1
  j .Lblsg2_inv_bit
.Lblsg2_inv_next:
  addi s2, s2, 1
  j .Lblsg2_inv_byte
.Lblsg2_inv_done:
  la a0, blsg2_facc
  mv a1, s1
  li a2, 6
  jal ra, blsf_copy_quads
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
