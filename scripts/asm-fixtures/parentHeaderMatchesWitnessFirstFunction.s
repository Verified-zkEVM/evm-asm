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
  # Byte-reconstruct offset[0] (u32 LE; the section pointer may be unaligned,
  # so no lwu). N = offset[0] / 4.
  mv t6, s2
  lbu t0, 0(t6)
  addi t6, t6, 1
  lbu t1, 0(t6)
  addi t6, t6, 1
  lbu t2, 0(t6)
  addi t6, t6, 1
  lbu t3, 0(t6)
  slli t1, t1, 8
  slli t2, t2, 16
  slli t3, t3, 24
  add t0, t0, t1
  add t0, t0, t2
  add t0, t0, t3
  srli t4, t0, 2              # N = offset[0] / 4
  beqz t4, .Lphmw_empty      # zero entries -> status 1
  add s5, s2, t0              # el_0 start
  # el_0 end: if N > 1, byte-reconstruct offset[1]; else use section_end.
  li t5, 1
  bltu t5, t4, .Lphmw_multi
  add s6, s2, s3              # el_0 end = section end
  j .Lphmw_join
.Lphmw_multi:
  addi t6, s2, 4
  lbu t0, 0(t6)
  addi t6, t6, 1
  lbu t1, 0(t6)
  addi t6, t6, 1
  lbu t2, 0(t6)
  addi t6, t6, 1
  lbu t3, 0(t6)
  slli t1, t1, 8
  slli t2, t2, 16
  slli t3, t3, 24
  add t0, t0, t1
  add t0, t0, t2
  add t0, t0, t3
  add s6, s2, t0              # el_0 end = offset[1]
.Lphmw_join:
  sub t0, s6, s5              # el_0 length
  bne t0, s1, .Lphmw_len_mismatch
  # Branch-free memcmp countdown: matchFlag &= (byte_i equal) over ALL bytes.
  mv t1, s0
  mv t2, s5
  mv t3, s1
  li t0, 1                    # matchFlag
.Lphmw_loop:
  beqz t3, .Lphmw_loopdone
  lbu t4, 0(t1)
  lbu t5, 0(t2)
  xor t4, t4, t5
  sltiu t6, t4, 1
  and t0, t0, t6
  addi t1, t1, 1
  addi t2, t2, 1
  addi t3, t3, -1
  j .Lphmw_loop
.Lphmw_loopdone:
  sd t0, 0(s4)                # is_match = matchFlag
  li a0, 0
  j .Lphmw_ret
.Lphmw_len_mismatch:
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
