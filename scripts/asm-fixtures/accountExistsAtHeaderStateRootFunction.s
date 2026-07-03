account_exists_at_header_state_root:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # witness.state ptr
  mv s4, a4                  # witness.state len
  # Pre-zero predicate.
  la t0, aex_predicate
  sd zero, 0(t0)
  # Step 1: header.state_root -> aex_state_root.
  mv a0, s0
  mv a1, s1
  la a2, aex_state_root
  jal ra, header_extract_state_root
  beqz a0, .Laex_step2
  li a0, 4
  j .Laex_ret
.Laex_step2:
  # Step 2: account_at_address.
  mv a0, s2
  li a1, 20
  la a2, aex_state_root
  mv a3, s3
  mv a4, s4
  la s5, aex_acct_struct
  mv a5, s5
  jal ra, account_at_address
  beqz a0, .Laex_found
  # status 1 (not in trie) -> predicate 0, return 0.
  li t0, 1
  beq a0, t0, .Laex_absent
  # status 2/3 -> propagate.
  j .Laex_ret
.Laex_absent:
  # predicate already 0.
  li a0, 0
  j .Laex_ret
.Laex_found:
  la t0, aex_predicate
  li t1, 1
  sd t1, 0(t0)
  li a0, 0
.Laex_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
