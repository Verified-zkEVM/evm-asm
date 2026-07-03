rlp_field_to_u64:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a0                  # container ptr
  mv s1, a3                  # u64 out ptr
  la a3, rfu_offset
  la a4, rfu_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lrfu_fail
  la t0, rfu_length; ld t1, 0(t0)
  li t2, 8
  bgtu t1, t2, .Lrfu_too_long
  la t0, rfu_offset; ld t3, 0(t0); add t3, s0, t3
  li t2, 0                   # accumulator
.Lrfu_loop:
  beqz t1, .Lrfu_done
  slli t2, t2, 8
  lbu t4, 0(t3)
  or t2, t2, t4
  addi t3, t3, 1
  addi t1, t1, -1
  j .Lrfu_loop
.Lrfu_done:
  sd t2, 0(s1)               # *out = u64 LE
  li a0, 0
  j .Lrfu_ret
.Lrfu_too_long:
  sd zero, 0(s1)
  li a0, 2
  j .Lrfu_ret
.Lrfu_fail:
  sd zero, 0(s1)
  li a0, 1
.Lrfu_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
