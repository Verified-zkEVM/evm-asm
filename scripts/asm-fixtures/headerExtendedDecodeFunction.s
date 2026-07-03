header_extended_decode:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                  # header_rlp ptr (base)
  mv s2, a2                  # struct out
  jal ra, rlp_walk_init      # a0=ptr,a1=len -> cursor,end,status
  bnez a2, .Lhed_fail
  mv s1, a1                  # end
  mv s3, a0                  # cursor
  # field 0: parent_hash (32 bytes @ struct+0)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  li t0, 32; bne a2, t0, .Lhed_fail
  sub t3, a0, a2
  ld t4,  0(t3); sd t4,  0(s2)
  ld t4,  8(t3); sd t4,  8(s2)
  ld t4, 16(t3); sd t4, 16(s2)
  ld t4, 24(t3); sd t4, 24(s2)
  # fields 1..2: skip
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  # field 3: state_root (32 bytes @ struct+32)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  li t0, 32; bne a2, t0, .Lhed_fail
  sub t3, a0, a2
  ld t4,  0(t3); sd t4, 32(s2)
  ld t4,  8(t3); sd t4, 40(s2)
  ld t4, 16(t3); sd t4, 48(s2)
  ld t4, 24(t3); sd t4, 56(s2)
  # fields 4..7: skip
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  # field 8: number (u64 @ struct+64)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lhed_fail
  sd a0, 64(s2)
  # field 9: gas_limit (u64 @ struct+80)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lhed_fail
  sd a0, 80(s2)
  # field 10: gas_used (u64 @ struct+88)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lhed_fail
  sd a0, 88(s2)
  # field 11: timestamp (u64 @ struct+72)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lhed_fail
  sd a0, 72(s2)
  # fields 12..14: skip
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  # field 15: base_fee_per_gas (u256 @ struct+96)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  sub a0, a0, a2; mv a1, a2; addi a2, s2, 96
  jal ra, rlp_content_to_u256_be
  bnez a0, .Lhed_fail
  # field 16: skip
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  # field 17: blob_gas_used (u64 @ struct+128)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lhed_fail
  sd a0, 128(s2)
  # field 18: excess_blob_gas (u64 @ struct+136)
  mv a0, s3; mv a1, s1; jal ra, rlp_walk_next
  mv s3, a0; bnez a1, .Lhed_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lhed_fail
  sd a0, 136(s2)
  li a0, 0
  j .Lhed_ret
.Lhed_fail:
  li a0, 1
.Lhed_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 64
  ret
