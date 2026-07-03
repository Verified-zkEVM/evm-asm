log_bloom_add:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # bloom ptr
  mv s1, a1                   # log_rlp ptr
  mv s2, a2                   # log_rlp len
  # ---- Field 0: address (20 bytes) ----
  mv a0, s1; mv a1, s2; li a2, 0
  la a3, lba_offset; la a4, lba_length
  jal ra, rlp_list_nth_item
  bnez a0, .Llba_fail
  la t0, lba_length; ld t1, 0(t0)
  li t2, 20
  bne t1, t2, .Llba_addr_size
  la t0, lba_offset; ld t1, 0(t0)
  add a1, s1, t1               # &address bytes
  mv a0, s0; li a2, 20
  jal ra, bloom_add_value
  # ---- Field 1: topics list — get bounds (full encoded item) ----
  mv a0, s1; mv a1, s2; li a2, 1
  la a3, lba_topics_offset; la a4, lba_topics_length
  jal ra, rlp_list_nth_item
  bnez a0, .Llba_fail
  la t0, lba_topics_offset; ld s3, 0(t0)        # topics absolute offset
  la t0, lba_topics_length; ld s4, 0(t0)        # topics full encoded len
  add t0, s1, s3                                # &topics_rlp
  # ---- Count topics ----
  mv a0, t0; mv a1, s4
  la a2, lba_topic_count
  jal ra, rlp_list_count_items
  bnez a0, .Llba_fail
  la t0, lba_topic_count; ld s5, 0(t0)          # n_topics
  # ---- For each topic i in 0..n_topics-1, add to bloom ----
  li t6, 0                                      # i
.Llba_topic_loop:
  bge t6, s5, .Llba_topic_done
  # Extract topic i bounds.
  add a0, s1, s3                                # topics_rlp ptr
  mv a1, s4                                     # topics_rlp len
  mv a2, t6                                     # index
  la a3, lba_offset; la a4, lba_length
  # Save t6 across the call (caller-saved).
  addi sp, sp, -8; sd t6, 0(sp)
  jal ra, rlp_list_nth_item
  ld t6, 0(sp); addi sp, sp, 8
  bnez a0, .Llba_fail
  la t0, lba_length; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Llba_topic_size
  la t0, lba_offset; ld t1, 0(t0)               # offset (relative to topics_rlp)
  add t1, t1, s3                                # absolute offset in log_rlp
  add a1, s1, t1                                # &topic bytes
  mv a0, s0; li a2, 32
  addi sp, sp, -8; sd t6, 0(sp)
  jal ra, bloom_add_value
  ld t6, 0(sp); addi sp, sp, 8
  addi t6, t6, 1
  j .Llba_topic_loop
.Llba_topic_done:
  li a0, 0
  j .Llba_ret
.Llba_fail:
  li a0, 1
  j .Llba_ret
.Llba_addr_size:
  li a0, 2
  j .Llba_ret
.Llba_topic_size:
  li a0, 3
.Llba_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
