tx_eip4844_decode:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                  # inner_rlp ptr (list base)
  mv s2, a2                  # struct out
  jal ra, rlp_walk_init      # a0=cursor, a1=end, a2=status
  bnez a2, .Lt48_fail
  mv s1, a1                  # end
  mv s3, a0                  # cursor
  # Field 0: chain_id (u64 at offset 0)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next      # a0=advanced, a1=status, a2=content_len
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2             # content_ptr = advanced - len
  mv a1, a2                  # content_len
  jal ra, rlp_content_to_u64_strict # a0=u64, a1=status
  bnez a1, .Lt48_fail
  sd a0, 0(s2)
  # Field 1: nonce (u64 at offset 8)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64_strict
  bnez a1, .Lt48_fail
  sd a0, 8(s2)
  # Field 2: max_priority_fee_per_gas (u256 at offset 16)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 16
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt48_fail
  # Field 3: max_fee_per_gas (u256 at offset 48)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 48
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt48_fail
  # Field 4: gas_limit (u64 at offset 80)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64_strict
  bnez a1, .Lt48_fail
  sd a0, 80(s2)
  # Field 5: to (0 or 20 bytes at 88; to_present u32 at 108)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  beqz a2, .Lt48_to_creation
  li t0, 20
  bne a2, t0, .Lt48_fail
  sub t3, a0, a2             # content_ptr
  addi t4, s2, 88
  ld t5,  0(t3); sd t5, 0(t4)
  ld t5,  8(t3); sd t5, 8(t4)
  lwu t5, 16(t3); sw t5, 16(t4)
  li t5, 1
  sw t5, 108(s2)             # to_present = 1
  j .Lt48_after_to
.Lt48_to_creation:
  addi t4, s2, 88
  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)
  sw zero, 108(s2)           # to_present = 0
.Lt48_after_to:
  # Field 6: value (u256 at offset 112)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 112
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt48_fail
  # Field 7: data (offset+length u32 at 144/148)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub t3, a0, a2             # content_ptr
  sub t1, t3, s0             # offset = content_ptr - base
  sw t1, 144(s2)
  sw a2, 148(s2)             # content_len
  # Field 8: access_list (offset+length u32 at 152/156; full encoded item)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub t3, a0, a2             # content_ptr
  sub t1, t3, s0             # offset = content_ptr - base
  sw t1, 152(s2)
  sw a2, 156(s2)             # content_len (full span)
  # Field 9: max_fee_per_blob_gas (u256). Write the full BE u256 directly
  # to tcbg_blob_fee_be (no sp+32 scratch needed), then BE-decode the low
  # 64 bits (bytes 24..31) into the u64 view at struct offset 160.
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  la a2, tcbg_blob_fee_be
  jal ra, rlp_content_to_u256_be_strict  # persists full u256 BE -> tcbg; a0=status
  bnez a0, .Lt48_fail
  la t0, tcbg_blob_fee_be
  lbu t1, 24(t0); slli t1, t1, 56
  lbu t2, 25(t0); slli t2, t2, 48; or t1, t1, t2
  lbu t2, 26(t0); slli t2, t2, 40; or t1, t1, t2
  lbu t2, 27(t0); slli t2, t2, 32; or t1, t1, t2
  lbu t2, 28(t0); slli t2, t2, 24; or t1, t1, t2
  lbu t2, 29(t0); slli t2, t2, 16; or t1, t1, t2
  lbu t2, 30(t0); slli t2, t2,  8; or t1, t1, t2
  lbu t2, 31(t0);                  or t1, t1, t2
  sd t1, 160(s2)
  # Field 10: blob_versioned_hashes (offset+length u32 at 168/172; full encoded item)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub t3, a0, a2             # content_ptr
  sub t1, t3, s0             # offset = content_ptr - base
  sw t1, 168(s2)
  sw a2, 172(s2)             # content_len (full span)
  # Field 11: y_parity (u64 at offset 176)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64_strict
  bnez a1, .Lt48_fail
  sd a0, 176(s2)
  # Field 12: r (u256 at offset 184)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 184
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt48_fail
  # Field 13: s (u256 at offset 216)
  mv a0, s3; mv a1, s1
  jal ra, rlp_walk_next
  mv s3, a0
  bnez a1, .Lt48_fail
  sub a0, a0, a2; mv a1, a2
  addi a2, s2, 216
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Lt48_fail
  li a0, 0
  j .Lt48_ret
.Lt48_fail:
  li a0, 1
.Lt48_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 64
  ret
