header_compute_summary_struct:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp)
  sd s5, 48(sp)
  mv s0, a0; mv s1, a1                # header
  mv s2, a2                            # output struct
  # 1. block_hash -> out[0..32]
  mv a0, s0; mv a1, s1; mv a2, s2
  jal ra, block_hash_from_header
  # 2. Initialize one cursor walk over the header RLP.
  mv a0, s0; mv a1, s1
  jal ra, rlp_walk_init
  bnez a2, .Lhcss_parse_fail
  mv s3, a0                            # cursor
  mv s4, a1                            # end
  # Skip fields 0, 1, 2.
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  # Field 3: state_root -> out[32..64].
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail
  li t0, 32; bne a2, t0, .Lhcss_size_fail
  sub t1, a0, a2                       # content ptr
  ld t2,  0(t1); sd t2, 32(s2)
  ld t2,  8(t1); sd t2, 40(s2)
  ld t2, 16(t1); sd t2, 48(s2)
  ld t2, 24(t1); sd t2, 56(s2)
  mv s3, a0
  # Skip fields 4, 5, 6, 7.
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  # Field 8: number -> out[64..72].
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail
  sub t0, a0, a2; mv s5, a0; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64_strict; bnez a1, .Lhcss_int_fail
  sd a0, 64(s2); mv s3, s5
  # Skip field 9.
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  # Field 10: gas_used -> out[80..88].
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail
  sub t0, a0, a2; mv s3, a0; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64_strict; bnez a1, .Lhcss_int_fail
  sd a0, 80(s2)
  # Field 11: timestamp -> out[72..80].
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail
  sub t0, a0, a2; mv s3, a0; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64_strict; bnez a1, .Lhcss_int_fail
  sd a0, 72(s2)
  # Skip fields 12, 13, 14.
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0
  # Field 15: base_fee_per_gas -> out[88..96].
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail
  sub t0, a0, a2; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64_strict; bnez a1, .Lhcss_int_fail
  sd a0, 88(s2)
  li a0, 0
  j .Lhcss_ret
.Lhcss_parse_fail:
  li a0, 1; j .Lhcss_ret
.Lhcss_size_fail:
  li a0, 2; j .Lhcss_ret
.Lhcss_int_fail:
  li a0, 2
.Lhcss_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp)
  ld s5, 48(sp)
  addi sp, sp, 56
  ret
