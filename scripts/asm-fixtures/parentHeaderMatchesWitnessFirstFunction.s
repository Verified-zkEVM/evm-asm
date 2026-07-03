parent_header_matches_witness_first:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # parent_header_rlp ptr
  mv s1, a1                  # parent_header_rlp_len
  mv s2, a2                  # section ptr
  mv s3, a3                  # section_len
  mv s4, a4                  # is_match out ptr
  sd zero, 0(s4)
  beqz s3, .Lphmw_empty       # empty section -> status 1
  # Compute element 0 bounds (SSZ list).
  lwu t0, 0(s2)
  srli t0, t0, 2              # N = first_offset / 4
  beqz t0, .Lphmw_empty      # zero entries
  lwu t1, 0(s2)               # el_0 inner offset (= 4 * N)
  add s5, s2, t1              # el_0 start
  # el_0 end: if N > 1, read offset[1] (4 bytes at offset 4); else use section_end.
  li t2, 1
  bgtu t0, t2, .Lphmw_have_next
  add s6, s2, s3              # el_0_end = section_end
  j .Lphmw_compare
.Lphmw_have_next:
  lwu t2, 4(s2)
  add s6, s2, t2              # el_0_end = section + inner_off[1]
.Lphmw_compare:
  sub t0, s6, s5              # el_0 length
  # Length must match parent_header_rlp_len.
  bne t0, s1, .Lphmw_no_match_success
  # Byte-compare s0..s0+s1 against s5..s6.
  mv t1, s0
  mv t2, s5
  mv t3, s1
.Lphmw_loop:
  beqz t3, .Lphmw_match
  lbu t4, 0(t1)
  lbu t5, 0(t2)
  bne t4, t5, .Lphmw_no_match_success
  addi t1, t1, 1
  addi t2, t2, 1
  addi t3, t3, -1
  j .Lphmw_loop
.Lphmw_match:
  li t1, 1
  sd t1, 0(s4)
  li a0, 0
  j .Lphmw_ret
.Lphmw_no_match_success:
  li a0, 0
  j .Lphmw_ret
.Lphmw_empty:
  li a0, 1
.Lphmw_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
