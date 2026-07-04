mpt_splice_slot:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # src
  mv s1, a1                   # src_len
  mv s2, a2                   # k
  mv s3, a3                   # new_ref
  mv s4, a4                   # new_ref_len
  mv s5, a5                   # out
  mv s6, a6                   # out_len ptr
  # payload_start = byte offset of item 0 (= list prefix length).
  mv a0, s0; mv a1, s1; li a2, 0
  la a3, mset_span_start; la a4, mset_span_size
  jal ra, rlp_item_span
  bnez a0, .Lsplice_fail
  la t0, mset_span_start; ld t1, 0(t0)
  la t0, mset_payload_start; sd t1, 0(t0)
  # span of item k.
  mv a0, s0; mv a1, s1; mv a2, s2
  la a3, mset_span_start; la a4, mset_span_size
  jal ra, rlp_item_span
  bnez a0, .Lsplice_fail
  la t0, mset_span_start; ld t2, 0(t0)   # slot_start
  la t0, mset_span_size;  ld t3, 0(t0)   # slot_size
  la t0, mset_payload_start; ld t1, 0(t0) # payload_start
  sub t4, t2, t1                          # head_len = slot_start - payload_start
  add t5, t2, t3                          # tail_start = slot_start + slot_size
  sub t6, s1, t5                          # tail_len = src_len - tail_start
  la t0, mset_head_len;  sd t4, 0(t0)
  la t0, mset_tail_start; sd t5, 0(t0)
  la t0, mset_tail_len;   sd t6, 0(t0)
  # new_payload_len = head_len + new_ref_len + tail_len
  add t1, t4, s4
  add t1, t1, t6
  la t0, mset_new_payload_len; sd t1, 0(t0)
  # write list prefix at out[0..].
  mv a0, t1
  mv a1, s5
  la a2, mset_prefix_len
  jal ra, rlp_encode_list_prefix
  la t0, mset_prefix_len; ld t1, 0(t0)
  add t2, s5, t1                          # cursor = out + prefix_len
  la t0, mset_cursor; sd t2, 0(t0)
  # copy head = src[payload_start .. slot_start].
  la t0, mset_cursor; ld a0, 0(t0)
  la t0, mset_payload_start; ld t1, 0(t0); add a1, s0, t1
  la t0, mset_head_len; ld a2, 0(t0)
  jal ra, mset_memcpy
  la t0, mset_cursor; ld t1, 0(t0)
  la t0, mset_head_len; ld t2, 0(t0); add t1, t1, t2
  la t0, mset_cursor; sd t1, 0(t0)
  # copy new_ref.
  la t0, mset_cursor; ld a0, 0(t0)
  mv a1, s3; mv a2, s4
  jal ra, mset_memcpy
  la t0, mset_cursor; ld t1, 0(t0); add t1, t1, s4
  la t0, mset_cursor; sd t1, 0(t0)
  # copy tail = src[tail_start .. src_len].
  la t0, mset_cursor; ld a0, 0(t0)
  la t0, mset_tail_start; ld t1, 0(t0); add a1, s0, t1
  la t0, mset_tail_len; ld a2, 0(t0)
  jal ra, mset_memcpy
  # out_len = prefix_len + new_payload_len.
  la t0, mset_prefix_len; ld t1, 0(t0)
  la t0, mset_new_payload_len; ld t2, 0(t0)
  add t1, t1, t2
  sd t1, 0(s6)
  li a0, 0
  j .Lsplice_ret
.Lsplice_fail:
  li a0, 1
.Lsplice_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
