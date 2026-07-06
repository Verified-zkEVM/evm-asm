headers_parent_hash:
  # a0 = header ptr, a1 = header_len, a2 = out ptr
  lbu t0, 0(a0)                # first byte
  li t1, 0xc0
  bltu t0, t1, .Lhph_fail      # not an RLP list (< 0xc0)
  li t1, 0xf8
  bltu t0, t1, .Lhph_short     # 0xc0..0xf7 → short list, 1-byte prefix
  # long list: t0 in [0xf8..0xff].
  # length_of_length = t0 - 0xf7. Outer prefix = 1 + length_of_length bytes.
  li t1, 0xf7
  sub t2, t0, t1               # length_of_length
  li t3, 2                     # cap: support 0xf8 (LoL=1), 0xf9 (LoL=2)
  bltu t3, t2, .Lhph_fail      # LoL > 2 → unsupported
  addi t2, t2, 1               # prefix bytes = LoL + 1
  add a0, a0, t2               # skip prefix
  sub a1, a1, t2
  j .Lhph_after_prefix
.Lhph_short:
  addi a0, a0, 1               # skip 1-byte prefix
  addi a1, a1, -1
.Lhph_after_prefix:
  # Expect 0xa0 Bytes32 prefix.
  li t0, 33
  bltu a1, t0, .Lhph_fail      # not enough bytes for 0xa0 + 32
  lbu t1, 0(a0)
  li t2, 0xa0
  bne t1, t2, .Lhph_fail       # not a Bytes32 string
  # Copy 32 bytes from a0+1 to a2.
  ld t0,  1(a0); sd t0,  0(a2)
  ld t0,  9(a0); sd t0,  8(a2)
  ld t0, 17(a0); sd t0, 16(a2)
  ld t0, 25(a0); sd t0, 24(a2)
  li a0, 0
  ret
.Lhph_fail:
  li a0, 1
  ret
