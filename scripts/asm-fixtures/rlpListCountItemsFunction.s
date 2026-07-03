rlp_list_count_items:
  beqz a1, .Lrlc_fail        # empty input cannot encode a list
  lbu t0, 0(a0)
  li t1, 0xc0
  bltu t0, t1, .Lrlc_fail    # not an RLP list
  li t1, 0xf8
  bltu t0, t1, .Lrlc_short_outer
  # Long outer list: prefix bytes = 1 + (t0 - 0xf7)
  li t1, 0xf7
  sub t2, t0, t1             # lol
  addi t2, t2, 1             # total prefix bytes
  add t3, a0, t2             # cursor at first item
  j .Lrlc_walk
.Lrlc_short_outer:
  addi t3, a0, 1
.Lrlc_walk:
  add t4, a0, a1             # end-of-list cursor (exclusive)
  li t5, 0                   # count
.Lrlc_loop:
  beq t3, t4, .Lrlc_done
  bgtu t3, t4, .Lrlc_fail    # cursor walked past end → malformed
  lbu t0, 0(t3)
  li t1, 0x80
  bltu t0, t1, .Lrlc_skip_single
  li t1, 0xb8
  bltu t0, t1, .Lrlc_skip_short_str
  li t1, 0xc0
  bltu t0, t1, .Lrlc_skip_long_str
  li t1, 0xf8
  bltu t0, t1, .Lrlc_skip_short_list
  # Long list at t3: lol = t0 - 0xf7
  li t1, 0xf7
  sub t2, t0, t1             # lol
  li a3, 0                   # decoded length accumulator
  mv a4, t2                  # remaining length bytes
  addi a5, t3, 1
.Lrlc_skll_be:
  beqz a4, .Lrlc_skll_done
  slli a3, a3, 8
  lbu a6, 0(a5)
  or  a3, a3, a6
  addi a5, a5, 1
  addi a4, a4, -1
  j .Lrlc_skll_be
.Lrlc_skll_done:
  addi a6, t2, 1
  add  a6, a6, a3            # 1 + lol + decoded
  add  t3, t3, a6
  j .Lrlc_step
.Lrlc_skip_short_list:
  li t1, 0xc0
  sub a6, t0, t1
  addi a6, a6, 1             # 1 + (t0 - 0xc0)
  add  t3, t3, a6
  j .Lrlc_step
.Lrlc_skip_long_str:
  li t1, 0xb7
  sub t2, t0, t1             # lol
  li a3, 0
  mv a4, t2
  addi a5, t3, 1
.Lrlc_skls_be:
  beqz a4, .Lrlc_skls_done
  slli a3, a3, 8
  lbu a6, 0(a5)
  or  a3, a3, a6
  addi a5, a5, 1
  addi a4, a4, -1
  j .Lrlc_skls_be
.Lrlc_skls_done:
  addi a6, t2, 1
  add  a6, a6, a3
  add  t3, t3, a6
  j .Lrlc_step
.Lrlc_skip_short_str:
  li t1, 0x80
  sub a6, t0, t1
  addi a6, a6, 1
  add  t3, t3, a6
  j .Lrlc_step
.Lrlc_skip_single:
  addi t3, t3, 1
.Lrlc_step:
  addi t5, t5, 1
  j .Lrlc_loop
.Lrlc_done:
  sd t5, 0(a2)
  li a0, 0
  ret
.Lrlc_fail:
  sd zero, 0(a2)
  li a0, 1
  ret
