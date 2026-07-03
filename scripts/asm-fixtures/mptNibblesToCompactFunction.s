mpt_nibbles_to_compact:
  # parity = count & 1
  andi t0, a1, 1
  # high_nibble = (is_leaf << 1) | parity
  slli t1, a2, 1
  or t1, t1, t0
  beqz t0, .Lmnc_even
  # Odd: prefix = (high_nibble << 4) | nibbles[0]
  lbu t3, 0(a0)
  slli t2, t1, 4
  andi t3, t3, 0xf
  or t2, t2, t3
  addi t4, a0, 1               # cursor at nibble[1]
  addi t5, a1, -1              # remaining (even)
  j .Lmnc_pack
.Lmnc_even:
  slli t2, t1, 4               # prefix byte (low nibble 0)
  mv t4, a0
  mv t5, a1
.Lmnc_pack:
  sb t2, 0(a3)
  addi t6, a3, 1
.Lmnc_loop:
  beqz t5, .Lmnc_done
  lbu t0, 0(t4)
  lbu t1, 1(t4)
  andi t0, t0, 0xf
  andi t1, t1, 0xf
  slli t0, t0, 4
  or t0, t0, t1
  sb t0, 0(t6)
  addi t6, t6, 1
  addi t4, t4, 2
  addi t5, t5, -2
  j .Lmnc_loop
.Lmnc_done:
  srli t0, a1, 1
  addi t0, t0, 1
  sd t0, 0(a4)
  li a0, 0
  ret
