chain_extract_number_range:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # N
  mv s1, a1                   # header_lengths
  mv s2, a2                   # headers
  mv s3, a3                   # min out
  mv s4, a4                   # max out
  beqz s0, .Lcenr_empty
  # min = headers[0].number
  ld a1, 0(s1)
  mv a0, s2
  li a2, 8                    # field 8 = number
  mv a3, s3
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Lcenr_propagate
  # Advance to last header: skip the first (N-1) headers
  mv t1, s2
  mv t2, s1
  addi t3, s0, -1             # iterations = N-1
.Lcenr_skip:
  beqz t3, .Lcenr_at_last
  ld t4, 0(t2)
  add t1, t1, t4
  addi t2, t2, 8
  addi t3, t3, -1
  j .Lcenr_skip
.Lcenr_at_last:
  ld a1, 0(t2)                # length of last header
  mv a0, t1
  li a2, 8
  mv a3, s4
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Lcenr_propagate
  li a0, 0
  j .Lcenr_ret
.Lcenr_empty:
  li a0, 1
  j .Lcenr_ret
.Lcenr_propagate:
  addi a0, a0, 1              # remap rlp_field_to_u64 1/2 -> 2/3
.Lcenr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
