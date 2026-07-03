rlp_list_nth_item:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # s0 = list_ptr
  add s1, a0, a1             # s1 = list_end
  mv s2, a2                  # s2 = N
  mv s3, a3                  # s3 = out_offset_ptr
  mv s4, a4                  # s4 = out_length_ptr
  # Parse outer list prefix.
  bgeu s0, s1, .Lrln_fail
  lbu t0, 0(s0)
  li t1, 0xc0
  bltu t0, t1, .Lrln_fail    # not an RLP list
  li t1, 0xf8
  bltu t0, t1, .Lrln_short_outer
  # Long outer: prefix bytes = 1 + (t0 - 0xf7)
  li t1, 0xf7
  sub t2, t0, t1             # lol
  addi t2, t2, 1             # prefix bytes
  add s5, s0, t2             # s5 = cursor at first item
  j .Lrln_walk
.Lrln_short_outer:
  addi s5, s0, 1
.Lrln_walk:
  li s6, 0                   # i
.Lrln_loop:
  beq s6, s2, .Lrln_at_target
  bgeu s5, s1, .Lrln_fail    # walked past end of list
  # Compute size of item at s5; advance s5 by it.
  lbu t0, 0(s5)
  li t1, 0x80
  bltu t0, t1, .Lrln_skip_single
  li t1, 0xb8
  bltu t0, t1, .Lrln_skip_short_string
  li t1, 0xc0
  bltu t0, t1, .Lrln_skip_long_string
  li t1, 0xf8
  bltu t0, t1, .Lrln_skip_short_list
  # Long list: lol = t0 - 0xf7
  li t1, 0xf7
  sub t2, t0, t1             # lol
  li t3, 0                   # decoded length accumulator
  mv t4, t2                  # remaining length bytes
  addi t5, s5, 1
.Lrln_skll_be:
  beqz t4, .Lrln_skll_done
  slli t3, t3, 8
  lbu t6, 0(t5)
  or t3, t3, t6
  addi t5, t5, 1
  addi t4, t4, -1
  j .Lrln_skll_be
.Lrln_skll_done:
  addi t6, t2, 1
  add t6, t6, t3             # 1 + lol + decoded
  add s5, s5, t6
  j .Lrln_step
.Lrln_skip_short_list:
  li t1, 0xc0
  sub t6, t0, t1
  addi t6, t6, 1             # 1 + (t0 - 0xc0)
  add s5, s5, t6
  j .Lrln_step
.Lrln_skip_long_string:
  li t1, 0xb7
  sub t2, t0, t1             # lol
  li t3, 0
  mv t4, t2
  addi t5, s5, 1
.Lrln_skls_be:
  beqz t4, .Lrln_skls_done
  slli t3, t3, 8
  lbu t6, 0(t5)
  or t3, t3, t6
  addi t5, t5, 1
  addi t4, t4, -1
  j .Lrln_skls_be
.Lrln_skls_done:
  addi t6, t2, 1
  add t6, t6, t3
  add s5, s5, t6
  j .Lrln_step
.Lrln_skip_short_string:
  li t1, 0x80
  sub t6, t0, t1
  addi t6, t6, 1
  add s5, s5, t6
  j .Lrln_step
.Lrln_skip_single:
  addi s5, s5, 1
.Lrln_step:
  addi s6, s6, 1
  j .Lrln_loop
.Lrln_at_target:
  bgeu s5, s1, .Lrln_fail    # target index past last item
  lbu t0, 0(s5)
  li t1, 0x80
  bltu t0, t1, .Lrln_t_single
  li t1, 0xb8
  bltu t0, t1, .Lrln_t_short_string
  li t1, 0xc0
  bltu t0, t1, .Lrln_t_long_string
  li t1, 0xf8
  bltu t0, t1, .Lrln_t_short_list
  # Long list (full encoded form)
  li t1, 0xf7
  sub t2, t0, t1
  li t3, 0
  mv t4, t2
  addi t5, s5, 1
.Lrln_tll_be:
  beqz t4, .Lrln_tll_done
  slli t3, t3, 8
  lbu t6, 0(t5)
  or t3, t3, t6
  addi t5, t5, 1
  addi t4, t4, -1
  j .Lrln_tll_be
.Lrln_tll_done:
  addi t6, t2, 1
  add t6, t6, t3             # full encoded size
  sub t1, s5, s0
  sd t1, 0(s3)
  sd t6, 0(s4)
  j .Lrln_ok
.Lrln_t_short_list:
  li t1, 0xc0
  sub t6, t0, t1
  addi t6, t6, 1
  sub t1, s5, s0
  sd t1, 0(s3)
  sd t6, 0(s4)
  j .Lrln_ok
.Lrln_t_long_string:
  li t1, 0xb7
  sub t2, t0, t1
  li t3, 0
  mv t4, t2
  addi t5, s5, 1
.Lrln_tls_be:
  beqz t4, .Lrln_tls_done
  slli t3, t3, 8
  lbu t6, 0(t5)
  or t3, t3, t6
  addi t5, t5, 1
  addi t4, t4, -1
  j .Lrln_tls_be
.Lrln_tls_done:
  # content offset = s5 + 1 + lol - s0
  addi t6, t2, 1
  add t6, t6, s5
  sub t6, t6, s0
  sd t6, 0(s3)
  sd t3, 0(s4)               # content length = decoded
  j .Lrln_ok
.Lrln_t_short_string:
  # content offset = s5 + 1 - s0; length = t0 - 0x80
  addi t6, s5, 1
  sub t6, t6, s0
  sd t6, 0(s3)
  li t1, 0x80
  sub t1, t0, t1
  sd t1, 0(s4)
  j .Lrln_ok
.Lrln_t_single:
  # content offset = s5 - s0; length = 1
  sub t1, s5, s0
  sd t1, 0(s3)
  li t1, 1
  sd t1, 0(s4)
.Lrln_ok:
  li a0, 0
  j .Lrln_ret
.Lrln_fail:
  li a0, 1
.Lrln_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
