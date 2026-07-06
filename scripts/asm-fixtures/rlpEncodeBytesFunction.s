rlp_encode_bytes:
  # t0 = data cursor; t1 = remaining; t2 = out cursor.
  mv t0, a0
  mv t1, a1
  mv t2, a2
  # Single-byte short-cut: len == 1 AND byte < 0x80.
  li t3, 1
  bne t1, t3, .Lreb_check_short
  lbu t4, 0(t0)
  li t5, 0x80
  bgeu t4, t5, .Lreb_check_short
  sb t4, 0(t2)
  li t6, 1
  sd t6, 0(a3)
  li a0, 0
  ret
.Lreb_check_short:
  li t3, 56
  bgeu t1, t3, .Lreb_long
  # Short string: prefix = 0x80 + len, then data.
  addi t3, t1, 0x80
  sb t3, 0(t2)
  addi t2, t2, 1
  mv t4, t1                   # bytes to copy
.Lreb_short_copy:
  beqz t4, .Lreb_short_done
  lbu t3, 0(t0)
  sb t3, 0(t2)
  addi t0, t0, 1
  addi t2, t2, 1
  addi t4, t4, -1
  j .Lreb_short_copy
.Lreb_short_done:
  addi t6, t1, 1              # out_len = 1 + len
  sd t6, 0(a3)
  li a0, 0
  ret
.Lreb_long:
  # Long string: prefix = 0xb7 + bc, then bc-byte BE len, then data.
  # Compute bc = effective byte count of t1 (1..8).
  # Write t1 as 8 BE bytes to a small scratch on the stack (or use
  # shifts directly into the out buffer). Use direct write approach:
  # determine bc, then write bc BE bytes from t1 by shifting right.
  li t3, 1
  li t4, 0x100                # 2^8
  bltu t1, t4, .Lreb_have_bc
  li t3, 2
  slli t4, t4, 8              # 2^16
  bltu t1, t4, .Lreb_have_bc
  li t3, 3
  slli t4, t4, 8              # 2^24
  bltu t1, t4, .Lreb_have_bc
  li t3, 4
  slli t4, t4, 8              # 2^32
  bltu t1, t4, .Lreb_have_bc
  li t3, 5
  slli t4, t4, 8              # 2^40
  bltu t1, t4, .Lreb_have_bc
  li t3, 6
  slli t4, t4, 8              # 2^48
  bltu t1, t4, .Lreb_have_bc
  li t3, 7
  slli t4, t4, 8              # 2^56
  bltu t1, t4, .Lreb_have_bc
  li t3, 8
.Lreb_have_bc:
  # t3 = bc. Write prefix 0xb7 + bc.
  addi t4, t3, 0xb7
  sb t4, 0(t2)
  addi t2, t2, 1
  # Write bc bytes of t1 in BE order. Use a counter i = bc-1..0,
  # shift t1 right by 8*i, store low byte.
  addi t4, t3, -1             # i = bc-1
.Lreb_emit_be:
  bltz t4, .Lreb_be_done
  slli t5, t4, 3              # 8 * i
  srl t6, t1, t5
  sb t6, 0(t2)
  addi t2, t2, 1
  addi t4, t4, -1
  j .Lreb_emit_be
.Lreb_be_done:
  # Copy data bytes.
  mv t4, t1
.Lreb_long_copy:
  beqz t4, .Lreb_long_done
  lbu t5, 0(t0)
  sb t5, 0(t2)
  addi t0, t0, 1
  addi t2, t2, 1
  addi t4, t4, -1
  j .Lreb_long_copy
.Lreb_long_done:
  # out_len = 1 + bc + len
  addi t5, t3, 1
  add t5, t5, t1
  sd t5, 0(a3)
  li a0, 0
  ret
