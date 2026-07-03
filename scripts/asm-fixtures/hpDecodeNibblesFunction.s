hp_decode_nibbles:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                  # path_bytes ptr
  mv s1, a1                  # len
  mv s2, a2                  # out nibble buf
  mv s3, a3                  # out count ptr
  mv s4, a4                  # out is_leaf ptr
  beqz s1, .Lhp_fail
  lbu t0, 0(s0)              # b0
  srli t1, t0, 4             # high nibble
  andi t2, t0, 0xf           # low nibble
  li t3, 4
  bgeu t1, t3, .Lhp_fail     # high ≥ 4 → invalid
  # is_leaf = (high & 2) >> 1
  andi t3, t1, 2
  srli t3, t3, 1
  sd t3, 0(s4)
  # is_odd = high & 1
  andi t1, t1, 1
  beqz t1, .Lhp_even
  # Odd: write low as first output nibble.
  sb t2, 0(s2)
  li t5, 1                   # nibble count so far
  addi t6, s2, 1             # output cursor
  j .Lhp_loop_init
.Lhp_even:
  bnez t2, .Lhp_fail         # even but low nibble != 0
  li t5, 0
  mv t6, s2
.Lhp_loop_init:
  li t0, 1                   # i = 1
.Lhp_loop:
  bgeu t0, s1, .Lhp_done
  add t1, s0, t0
  lbu t2, 0(t1)
  srli t3, t2, 4
  andi t4, t2, 0xf
  sb t3, 0(t6)
  sb t4, 1(t6)
  addi t6, t6, 2
  addi t5, t5, 2
  addi t0, t0, 1
  j .Lhp_loop
.Lhp_done:
  sd t5, 0(s3)
  li a0, 0
  j .Lhp_ret
.Lhp_fail:
  li a0, 1
.Lhp_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
