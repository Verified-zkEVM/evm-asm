account_extract_nonce:
  addi sp, sp, -16
  sd ra,  0(sp)
  sd s0,  8(sp)
  mv s0, a2                   # u64 out ptr (stash)
  sd zero, 0(s0)
  # a0, a1 still hold (account_ptr, account_len).
  jal ra, rlp_walk_init
  bnez a2, .Laen_fail
  # a0 = cursor, a1 = end: advance past field 0 (nonce).
  jal ra, rlp_walk_next
  bnez a1, .Laen_fail
  sub t0, a0, a2              # content ptr = advanced cursor - content len
  mv a0, t0
  mv a1, a2
  jal ra, rlp_content_to_u64
  bnez a1, .Laen_fail
  sd a0, 0(s0)
  li a0, 0
  j .Laen_ret
.Laen_fail:
  sd zero, 0(s0)
  li a0, 1
.Laen_ret:
  ld ra,  0(sp)
  ld s0,  8(sp)
  addi sp, sp, 16
  ret
