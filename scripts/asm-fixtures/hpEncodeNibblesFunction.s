hp_encode_nibbles:
  andi t0, a1, 1             # is_odd = nibble_count & 1
  mv t1, a3                  # cursor
  slli t2, a2, 1             # is_leaf * 2
  or t2, t2, t0              # flag = is_leaf*2 + is_odd
  slli t2, t2, 4             # flag << 4
  beqz t0, .Lhpe_even
  # Odd: byte 0 = (flag << 4) | nibbles[0]; consume one nibble.
  lbu t3, 0(a0)
  or t2, t2, t3
  sb t2, 0(t1)
  addi t1, t1, 1
  addi a0, a0, 1
  addi a1, a1, -1
  j .Lhpe_pair_loop
.Lhpe_even:
  sb t2, 0(t1)
  addi t1, t1, 1
.Lhpe_pair_loop:
  beqz a1, .Lhpe_done
  lbu t3, 0(a0)
  slli t3, t3, 4
  lbu t4, 1(a0)
  or t3, t3, t4
  sb t3, 0(t1)
  addi t1, t1, 1
  addi a0, a0, 2
  addi a1, a1, -2
  j .Lhpe_pair_loop
.Lhpe_done:
  sub a0, t1, a3
  ret
