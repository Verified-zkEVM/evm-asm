extcodehash_at_header_state_root:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # witness.state ptr
  mv s4, a4                  # witness.state len
  mv s5, a5                  # 32-byte output ptr
  # Pre-zero output (covers the EIP-1052 zero cases).
  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)
  # Step 1: header.state_root -> eahsr_state_root.
  mv a0, s0
  mv a1, s1
  la a2, eahsr_state_root
  jal ra, header_extract_state_root
  beqz a0, .Leahsr_step2
  li a0, 4
  j .Leahsr_ret
.Leahsr_step2:
  # Step 2: account_at_address -> eahsr_acct_struct.
  mv a0, s2
  li a1, 20
  la a2, eahsr_state_root
  mv a3, s3
  mv a4, s4
  la s6, eahsr_acct_struct
  mv a5, s6
  jal ra, account_at_address
  beqz a0, .Leahsr_check_empty
  # status 1 (not in trie) -> EIP-1052 returns 0 (output already zero).
  li t0, 1
  beq a0, t0, .Leahsr_success_zero
  # status 2/3 -> propagate.
  j .Leahsr_ret
.Leahsr_success_zero:
  li a0, 0
  j .Leahsr_ret
.Leahsr_check_empty:
  # nonce == 0 ?
  ld t1, 0(s6)
  bnez t1, .Leahsr_write_code_hash
  # balance == 0 ?  (4 x u64 at struct+8..40; zero-check is endian-blind)
  ld t1,  8(s6); bnez t1, .Leahsr_write_code_hash
  ld t1, 16(s6); bnez t1, .Leahsr_write_code_hash
  ld t1, 24(s6); bnez t1, .Leahsr_write_code_hash
  ld t1, 32(s6); bnez t1, .Leahsr_write_code_hash
  # code_hash == EMPTY_CODE_HASH ?
  la t0, eahsr_empty_code_hash
  ld t1,  0(t0); ld t2, 72(s6); bne t1, t2, .Leahsr_write_code_hash
  ld t1,  8(t0); ld t2, 80(s6); bne t1, t2, .Leahsr_write_code_hash
  ld t1, 16(t0); ld t2, 88(s6); bne t1, t2, .Leahsr_write_code_hash
  ld t1, 24(t0); ld t2, 96(s6); bne t1, t2, .Leahsr_write_code_hash
  # All three empty-conditions hold; output stays zero, return 0.
  li a0, 0
  j .Leahsr_ret
.Leahsr_write_code_hash:
  # Account is non-empty; copy code_hash to output.
  ld t1, 72(s6); sd t1,  0(s5)
  ld t1, 80(s6); sd t1,  8(s5)
  ld t1, 88(s6); sd t1, 16(s5)
  ld t1, 96(s6); sd t1, 24(s5)
  li a0, 0
.Leahsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 80
  ret
