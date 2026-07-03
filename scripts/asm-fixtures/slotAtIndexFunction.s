slot_at_index:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a5                  # u256 out ptr
  la a5, si_value_scratch
  la a6, si_value_len
  jal ra, mpt_lookup_by_key
  mv s1, a0
  beqz a0, .Lsi_decode
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  mv a0, s1
  j .Lsi_ret
.Lsi_decode:
  la a0, si_value_scratch
  la t0, si_value_len; ld a1, 0(t0)
  mv a2, s0
  jal ra, slot_decode_u256
  beqz a0, .Lsi_done
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  li a0, 3
  j .Lsi_ret
.Lsi_done:
  li a0, 0
.Lsi_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
