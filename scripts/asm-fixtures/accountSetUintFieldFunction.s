account_set_uint_field:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # account ptr
  mv s1, a1                   # account len
  mv s2, a2                   # field index
  mv s3, a3                   # value ptr
  mv s4, a4                   # value len
  mv s5, a5                   # out ptr
  mv s6, a6                   # out len ptr
  li t0, 32; bgtu s4, t0, .Lasuf_fail
  mv a0, s3; mv a1, s4; la a2, aab_enc
  jal ra, rlp_encode_uint_be
  la t0, aab_enc_len; sd a0, 0(t0)
  mv a0, s0; mv a1, s1; mv a2, s2
  la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0)
  mv a5, s5; mv a6, s6
  jal ra, mpt_splice_slot
  j .Lasuf_ret
.Lasuf_fail:
  li a0, 1
.Lasuf_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 80
  ret
