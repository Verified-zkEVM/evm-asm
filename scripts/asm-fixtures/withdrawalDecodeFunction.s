withdrawal_decode:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                  # wd_rlp ptr
  mv s1, a1                  # wd_rlp_len
  mv s2, a2                  # struct out
  # Field 0: index (u64 at offset 0)
  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2
  jal ra, rlp_field_to_u64
  bnez a0, .Lwd_fail
  # Field 1: validator_index (u64 at offset 8)
  mv a0, s0; mv a1, s1; li a2, 1
  addi a3, s2, 8
  jal ra, rlp_field_to_u64
  bnez a0, .Lwd_fail
  # Field 2: address (20 bytes at offset 16)
  mv a0, s0; mv a1, s1; li a2, 2
  la a3, wd_offset; la a4, wd_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lwd_fail
  la t0, wd_length; ld t1, 0(t0)
  li t2, 20
  bne t1, t2, .Lwd_fail
  la t0, wd_offset; ld t3, 0(t0); add t3, s0, t3
  addi t4, s2, 16
  ld t5,  0(t3); sd t5,  0(t4)
  ld t5,  8(t3); sd t5,  8(t4)
  lwu t5, 16(t3); sw t5, 16(t4)
  # Pad bytes 20..24 of address slot (struct 36..40) are zero (from caller zeroing).
  # Field 3: amount (u64 at offset 40)
  mv a0, s0; mv a1, s1; li a2, 3
  addi a3, s2, 40
  jal ra, rlp_field_to_u64
  bnez a0, .Lwd_fail
  li a0, 0
  j .Lwd_ret
.Lwd_fail:
  li a0, 1
.Lwd_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
