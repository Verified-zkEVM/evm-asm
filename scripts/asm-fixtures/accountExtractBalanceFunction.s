account_extract_balance:
  addi sp, sp, -16
  sd ra,  0(sp)
  sd s0,  8(sp)
  mv s0, a2                   # output 32B ptr (stash)
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  # a0, a1 still hold (account_ptr, account_len).
  li a2, 1
  mv a3, s0
  jal ra, rlp_field_to_u256_be
  beqz a0, .Laeb_ret
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  li a0, 1
.Laeb_ret:
  ld ra,  0(sp)
  ld s0,  8(sp)
  addi sp, sp, 16
  ret
