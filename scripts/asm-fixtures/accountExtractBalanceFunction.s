account_extract_balance:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  mv s0, a2                   # output 32B ptr (stash)
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  # a0, a1 still hold (account_ptr, account_len).
  jal ra, rlp_walk_init
  bnez a2, .Laeb_fail
  mv s1, a1                   # end (rlp_walk_next returns status in a1)
  jal ra, rlp_walk_next       # skip field 0 (nonce)
  bnez a1, .Laeb_fail
  mv a1, s1
  jal ra, rlp_walk_next       # field 1 (balance)
  bnez a1, .Laeb_fail
  sub t0, a0, a2              # content ptr = advanced cursor - content len
  mv a0, t0
  mv a1, a2
  mv a2, s0                   # 32B u256 BE out
  jal ra, rlp_content_to_u256_be
  bnez a0, .Laeb_fail
  li a0, 0
  j .Laeb_ret
.Laeb_fail:
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  li a0, 1
.Laeb_ret:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  addi sp, sp, 32
  ret
