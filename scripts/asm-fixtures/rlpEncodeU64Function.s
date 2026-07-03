rlp_encode_u64:
  beqz a0, .Lreu64_zero
  li t0, 0x80
  bgeu a0, t0, .Lreu64_multi
  # Single-byte form (value in 0x01..0x7f).
  sb a0, 0(a1)
  li t1, 1
  sd t1, 0(a2)
  li a0, 0
  ret
.Lreu64_zero:
  li t0, 0x80
  sb t0, 0(a1)
  li t1, 1
  sd t1, 0(a2)
  li a0, 0
  ret
.Lreu64_multi:
  # Compute effective byte length (1..8) by finding the top non-zero byte.
  # We already know value >= 0x80, so len >= 1.
  li t0, 1                   # effective_len candidate
  li t1, 0x100
  bltu a0, t1, .Lreu64_have_len
  li t0, 2
  slli t1, t1, 8
  bltu a0, t1, .Lreu64_have_len
  li t0, 3
  slli t1, t1, 8
  bltu a0, t1, .Lreu64_have_len
  li t0, 4
  slli t1, t1, 8
  bltu a0, t1, .Lreu64_have_len
  li t0, 5
  slli t1, t1, 8
  bltu a0, t1, .Lreu64_have_len
  li t0, 6
  slli t1, t1, 8
  bltu a0, t1, .Lreu64_have_len
  li t0, 7
  slli t1, t1, 8
  bltu a0, t1, .Lreu64_have_len
  li t0, 8
.Lreu64_have_len:
  # Write prefix 0x80 + effective_len.
  addi t2, t0, 0x80
  sb t2, 0(a1)
  # Write effective_len BE bytes of value into a1+1..a1+1+len.
  addi t3, a1, 1                 # dst cursor
  addi t4, t0, -1                # shift_byte_index = len - 1
.Lreu64_emit:
  bltz t4, .Lreu64_done
  slli t5, t4, 3                 # bit shift = 8 * byte_index
  srl t6, a0, t5
  sb t6, 0(t3)
  addi t3, t3, 1
  addi t4, t4, -1
  j .Lreu64_emit
.Lreu64_done:
  addi t1, t0, 1                 # bytes_written = 1 + effective_len
  sd t1, 0(a2)
  li a0, 0
  ret
