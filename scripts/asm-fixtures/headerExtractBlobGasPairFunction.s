header_extract_blob_gas_pair:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_len
  mv s2, a2                  # output 16B ptr
  # Field 17: blob_gas_used → out[0..8]
  mv a0, s0; mv a1, s1; li a2, 17
  mv a3, s2
  jal ra, rlp_field_to_u64_strict
  beqz a0, .Lhebgp_f18
  sd zero, 0(s2); sd zero, 8(s2)
  li a0, 1
  j .Lhebgp_ret
.Lhebgp_f18:
  # Field 18: excess_blob_gas → out[8..16]
  mv a0, s0; mv a1, s1; li a2, 18
  addi a3, s2, 8
  jal ra, rlp_field_to_u64_strict
  beqz a0, .Lhebgp_ok
  sd zero, 0(s2); sd zero, 8(s2)
  li a0, 2
  j .Lhebgp_ret
.Lhebgp_ok:
  li a0, 0
.Lhebgp_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
