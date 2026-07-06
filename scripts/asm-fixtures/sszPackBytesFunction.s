ssz_pack_bytes:
  # a0 = src, a1 = L, a2 = dst.
  # First copy L bytes from src to dst (byte-wise).
  mv t0, a0                  # t0 = src cursor
  mv t1, a2                  # t1 = dst cursor
  mv t2, a1                  # t2 = remaining bytes
.Lszpb_copy:
  beqz t2, .Lszpb_check_pad
  lbu t3, 0(t0)
  sb  t3, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lszpb_copy
.Lszpb_check_pad:
  # remainder = L & 31; if zero, skip pad. else pad = 32 - remainder.
  andi t2, a1, 31
  beqz t2, .Lszpb_count
  li t3, 32
  sub t2, t3, t2             # t2 = pad bytes
.Lszpb_pad:
  beqz t2, .Lszpb_count
  sb zero, 0(t1)
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lszpb_pad
.Lszpb_count:
  # chunks = ceil(L / 32) = (L + 31) >> 5
  addi t0, a1, 31
  srli a0, t0, 5
  ret
