tx_eip2930_decode:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                  # inner_rlp ptr (list base)
  mv s2, a2                  # struct out
  jal ra, rlp_walk_init      # a0=cursor, a1=end, a2=status
  bnez a2, .Lt29_fail
  mv s1, a1                  # end
  mv s3, a0                  # cursor
  # Field 0: chain_id (u64 at offset 0)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next      # a0=advanced, a1=status, a2=content_len
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2             # content_ptr = advanced - len
  mv a1, a2                  # content_len
  jal ra, rlp_content_to_u64_strict # a0=u64, a1=status
  bnez a1, .Lt29_fail
  sd a0, 0(s2)
  # Field 1: nonce (u64 at offset 8)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64_strict
  bnez a1, .Lt29_fail
  sd a0, 8(s2)
  # Field 2: gas_price (u256 at offset 16)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 16
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt29_fail
  # Field 3: gas_limit (u64 at offset 48)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64_strict
  bnez a1, .Lt29_fail
  sd a0, 48(s2)
  # Field 4: to (0 or 20 bytes at 56; to_present u32 at 76)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  beqz a2, .Lt29_to_creation
  li t0, 20
  bne a2, t0, .Lt29_fail
  sub t3, a0, a2             # content_ptr
  addi t4, s2, 56
  ld t5,  0(t3); sd t5, 0(t4)
  ld t5,  8(t3); sd t5, 8(t4)
  lwu t5, 16(t3); sw t5, 16(t4)
  li t5, 1
  sw t5, 76(s2)              # to_present = 1
  j .Lt29_after_to
.Lt29_to_creation:
  addi t4, s2, 56
  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)
  sw zero, 76(s2)            # to_present = 0
.Lt29_after_to:
  # Field 5: value (u256 at offset 80)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 80
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt29_fail
  # Field 6: data (offset+length u64 at 112/120)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub t3, a0, a2             # content_ptr
  sub t1, t3, s0             # offset = content_ptr - base
  sd t1, 112(s2)
  sd a2, 120(s2)             # content_len
  # Field 7: access_list (offset+length u64 at 128/136; full encoded item)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub t3, a0, a2             # content_ptr
  sub t1, t3, s0             # offset = content_ptr - base
  sd t1, 128(s2)
  sd a2, 136(s2)             # content_len (full span)
  # Field 8: y_parity (u64 at offset 144)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64_strict
  bnez a1, .Lt29_fail
  sd a0, 144(s2)
  # Field 9: r (u256 at offset 152)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 152
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt29_fail
  # Field 10: s (u256 at offset 184)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt29_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 184
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt29_fail
  li a0, 0
  j .Lt29_ret
.Lt29_fail:
  li a0, 1
.Lt29_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 64
  ret
