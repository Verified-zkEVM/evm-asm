account_extract_nonce:
  addi sp, sp, -16
  sd ra,  0(sp)
  sd s0,  8(sp)
  mv s0, a2                   # u64 out ptr (stash)
  sd zero, 0(s0)
  # a0, a1 still hold (account_ptr, account_len).
  li a2, 0
  mv a3, s0
  jal ra, rlp_field_to_u64
  beqz a0, .Laen_ret
  sd zero, 0(s0)
  li a0, 1
.Laen_ret:
  ld ra,  0(sp)
  ld s0,  8(sp)
  addi sp, sp, 16
  ret
