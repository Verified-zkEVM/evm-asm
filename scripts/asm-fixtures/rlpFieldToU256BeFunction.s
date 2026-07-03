rlp_field_to_u256_be:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a0                  # container ptr
  mv s1, a3                  # u256 BE out ptr
  # Zero output up front (also covers fail/too-long paths).
  sd zero,  0(s1); sd zero,  8(s1); sd zero, 16(s1); sd zero, 24(s1)
  la a3, rfu_offset
  la a4, rfu_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lrf256_fail
  la t0, rfu_length; ld t1, 0(t0)
  li t2, 32
  bgtu t1, t2, .Lrf256_too_long
  la t0, rfu_offset; ld t3, 0(t0); add t3, s0, t3
  sub t2, t2, t1             # 32 - len
  add t4, s1, t2             # dst start (right-aligned)
.Lrf256_copy:
  beqz t1, .Lrf256_done
  lbu t5, 0(t3)
  sb  t5, 0(t4)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t1, t1, -1
  j .Lrf256_copy
.Lrf256_done:
  li a0, 0
  j .Lrf256_ret
.Lrf256_too_long:
  li a0, 2
  j .Lrf256_ret
.Lrf256_fail:
  li a0, 1
.Lrf256_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
