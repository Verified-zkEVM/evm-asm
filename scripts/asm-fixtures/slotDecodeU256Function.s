slot_decode_u256:
  # a0 = val_bytes ptr, a1 = val_len, a2 = 32-byte BE out ptr.
  # Returns 0 (ok) / 1 (fail). Output is zeroed on every path.
  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)
  beqz a1, .Lsdu_fail        # empty input: malformed encoded value
  lbu t0, 0(a0)
  li t1, 0x80
  bltu t0, t1, .Lsdu_single  # b0 < 0x80: single byte
  beq t0, t1, .Lsdu_zero     # b0 == 0x80: empty string ⇒ 0
  li t1, 0xa1
  bgeu t0, t1, .Lsdu_fail    # b0 ≥ 0xa1: too long for a u256
  # Short string of n bytes (1 ≤ n ≤ 32).
  li t1, 0x80
  sub t2, t0, t1             # n
  addi t3, a1, -1
  bltu t3, t2, .Lsdu_fail    # not enough bytes for declared length
  li t4, 32
  sub t4, t4, t2             # 32 - n
  add t5, a2, t4             # dst (right-aligned)
  addi t6, a0, 1             # src
  mv t3, t2                  # remaining
.Lsdu_copy:
  beqz t3, .Lsdu_ok
  lbu t1, 0(t6)
  sb  t1, 0(t5)
  addi t5, t5, 1
  addi t6, t6, 1
  addi t3, t3, -1
  j .Lsdu_copy
.Lsdu_single:
  sb t0, 31(a2)              # write u256 = b0 at byte 31 (BE LSB)
.Lsdu_zero:
.Lsdu_ok:
  li a0, 0
  ret
.Lsdu_fail:
  li a0, 1
  ret
