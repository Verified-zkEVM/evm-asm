mpt_compact_to_nibbles:
  sd zero, 0(a3)              # default count = 0
  sd zero, 0(a4)              # default is_leaf = 0
  beqz a1, .Lmctn_fail
  lbu t0, 0(a0)               # prefix byte
  srli t1, t0, 4              # high nibble
  andi t2, t1, 2              # is_leaf bit
  srli t2, t2, 1
  sd t2, 0(a4)
  andi t3, t1, 1              # parity bit
  mv t4, a2                   # nibbles cursor
  li t5, 0                    # nibble count
  beqz t3, .Lmctn_even
  # Odd: first nibble = low nibble of prefix
  andi t6, t0, 0xf
  sb t6, 0(t4)
  addi t4, t4, 1
  addi t5, t5, 1
.Lmctn_even:
  addi t6, a0, 1              # cursor over packed bytes
  addi t1, a1, -1             # remaining packed bytes
.Lmctn_loop:
  beqz t1, .Lmctn_done
  lbu t0, 0(t6)
  srli t2, t0, 4              # high nibble
  andi t3, t0, 0xf            # low nibble
  sb t2, 0(t4)
  sb t3, 1(t4)
  addi t4, t4, 2
  addi t5, t5, 2
  addi t6, t6, 1
  addi t1, t1, -1
  j .Lmctn_loop
.Lmctn_done:
  sd t5, 0(a3)
  li a0, 0
  ret
.Lmctn_fail:
  li a0, 1
  ret
