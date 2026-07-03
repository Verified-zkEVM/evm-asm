extract_parent_header_and_state_root:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # SSZ_BASE
  mv s1, a1                   # this.parent_hash
  mv s2, a2                   # out hdr ptr
  mv s3, a3                   # out hdr len
  mv s4, a4                   # out state_root
  # witness = SSZ_BASE + outer.offsets[1]
  addi a0, s0, 4
  jal ra, eph_u32le
  add s5, s0, a0              # s5 = witness
  # witness_end = SSZ_BASE + outer.offsets[2]
  addi a0, s0, 8
  jal ra, eph_u32le
  add s6, s0, a0              # s6 = witness_end
  # headers_ptr = witness + inner.offsets[2]
  addi a0, s5, 8
  jal ra, eph_u32le
  add s0, s5, a0              # s0 = headers_ptr (SSZ_BASE no longer needed)
  # find parent header: witness_lookup_by_hash(headers, len, parent_hash).
  mv a0, s0
  sub a1, s6, s0             # headers_len = witness_end - headers_ptr
  mv a2, s1
  la a3, eph_off; la a4, eph_len
  jal ra, witness_lookup_by_hash
  bnez a0, .Leph_notfound
  la t0, eph_off; ld t1, 0(t0); add t2, s0, t1   # parent_hdr_ptr
  la t0, eph_len; ld t3, 0(t0)                   # parent_hdr_len
  sd t2, 0(s2); sd t3, 0(s3)
  # state_root = header_extract_state_root(parent_hdr_ptr, len).
  mv a0, t2; mv a1, t3; mv a2, s4
  jal ra, header_extract_state_root
  # a0 = 0/1/2 from the extractor (1/2 => parse issue); map nonzero to 2.
  beqz a0, .Leph_ret
  li a0, 2
  j .Leph_ret
.Leph_notfound:
  li a0, 1
.Leph_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
