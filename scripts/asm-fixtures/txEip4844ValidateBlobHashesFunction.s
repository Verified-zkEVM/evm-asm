tx_eip4844_validate_blob_hashes:
  addi sp, sp, -72
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # inner_rlp ptr
  mv s1, a2                   # max_blob_count
  mv s2, a3                   # count out ptr
  sd zero, 0(s2)
  # Step 1: decode inner EIP-4844 body into tcbg_struct.
  la a2, tcbg_struct
  mv t0, a2; li t1, 31
.Lt48v_zinit:
  beqz t1, .Lt48v_zdone
  sd zero, 0(t0)
  addi t0, t0, 8
  addi t1, t1, -1
  j .Lt48v_zinit
.Lt48v_zdone:
  jal ra, tx_eip4844_decode
  bnez a0, .Lt48v_decode_fail
  la t0, tcbg_struct
  lwu t1, 168(t0)             # blob_versioned_hashes_offset
  lwu t2, 172(t0)             # blob_versioned_hashes_length
  add s3, s0, t1              # blob list ptr
  mv s4, t2                   # blob list length
  # Step 2: count top-level blob hashes.
  mv a0, s3; mv a1, s4
  la a2, bgvh_count_scratch
  jal ra, rlp_list_count_items
  bnez a0, .Lt48v_count_fail
  la t0, bgvh_count_scratch
  ld s6, 0(t0)                # blob hash count
  sd s6, 0(s2)
  beqz s6, .Lt48v_zero_blobs
  bltu s1, s6, .Lt48v_too_many
  # Step 3: validate each item length and KZG version byte.
  li s5, 0
.Lt48v_loop:
  beq s5, s6, .Lt48v_ok
  mv a0, s3; mv a1, s4; mv a2, s5
  la a3, t48_offset
  la a4, t48_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lt48v_bad_item
  la t0, t48_length
  ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Lt48v_bad_item
  la t0, t48_offset
  ld t2, 0(t0)
  add t2, s3, t2
  lbu t3, 0(t2)
  li t4, 1
  bne t3, t4, .Lt48v_bad_version
  addi s5, s5, 1
  j .Lt48v_loop
.Lt48v_ok:
  li a0, 0
  j .Lt48v_ret
.Lt48v_decode_fail:
  li a0, 1
  j .Lt48v_ret
.Lt48v_count_fail:
  li a0, 2
  j .Lt48v_ret
.Lt48v_zero_blobs:
  li a0, 3
  j .Lt48v_ret
.Lt48v_too_many:
  li a0, 4
  j .Lt48v_ret
.Lt48v_bad_item:
  li a0, 5
  j .Lt48v_ret
.Lt48v_bad_version:
  li a0, 6
.Lt48v_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 72
  ret
