access_list_count:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # outer list ptr
  mv s1, a1                   # outer list len
  mv s2, a2                   # num_addresses out
  mv s3, a3                   # num_storage_keys out
  sd zero, 0(s2); sd zero, 0(s3)
  # Step 1: outer count → s4 = N.
  mv a0, s0; mv a1, s1
  la a2, alc_scratch
  jal ra, rlp_list_count_items
  bnez a0, .Lalc_fail
  la t0, alc_scratch; ld s4, 0(t0)
  beqz s4, .Lalc_done
  # Step 2: iterate entries 0..N-1.
  li s5, 0                    # entry index
.Lalc_loop:
  beq s5, s4, .Lalc_done
  # Fetch entry s5 bounds in the outer list.
  mv a0, s0; mv a1, s1; mv a2, s5
  la a3, alc_entry_offset
  la a4, alc_entry_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lalc_fail
  # entry_ptr = outer_ptr + entry_offset.
  la t0, alc_entry_offset; ld t1, 0(t0)
  la t0, alc_entry_length; ld t2, 0(t0)
  add a0, s0, t1              # entry_ptr
  mv a1, t2                   # entry_len
  # Fetch entry field 1 (the slots sub-list) bounds.
  li a2, 1
  la a3, alc_keys_offset
  la a4, alc_keys_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lalc_fail
  # keys_ptr = outer_ptr + entry_offset + keys_offset.
  la t0, alc_entry_offset; ld t1, 0(t0)
  la t0, alc_keys_offset; ld t3, 0(t0)
  add t1, t1, t3
  add a0, s0, t1              # keys_ptr
  la t0, alc_keys_length; ld a1, 0(t0)
  la a2, alc_scratch
  jal ra, rlp_list_count_items
  bnez a0, .Lalc_fail
  la t0, alc_scratch; ld t1, 0(t0)
  ld t2, 0(s3)
  add t2, t2, t1
  sd t2, 0(s3)
  addi s5, s5, 1
  j .Lalc_loop
.Lalc_done:
  sd s4, 0(s2)                # num_addresses = N
  li a0, 0
  j .Lalc_ret
.Lalc_fail:
  sd zero, 0(s2); sd zero, 0(s3)
  li a0, 1
.Lalc_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
