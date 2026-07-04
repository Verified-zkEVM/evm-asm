extcodesize_at_header_state_root:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # witness.state ptr
  mv s4, a4                  # witness.state len
  mv s5, a5                  # witness.codes ptr
  mv s6, a6                  # witness.codes len
  # Pre-zero output (covers the missing/empty cases).
  la t0, ecsahsr_code_len
  sd zero, 0(t0)
  # Step 1: header.state_root -> ecsahsr_state_root.
  mv a0, s0
  mv a1, s1
  la a2, ecsahsr_state_root
  jal ra, header_extract_state_root
  beqz a0, .Lecsahsr_step2
  li a0, 4
  j .Lecsahsr_ret
.Lecsahsr_step2:
  # Step 2: account_at_address -> ecsahsr_acct_struct.
  mv a0, s2
  li a1, 20
  la a2, ecsahsr_state_root
  mv a3, s3
  mv a4, s4
  la s7, ecsahsr_acct_struct
  mv a5, s7
  jal ra, account_at_address
  beqz a0, .Lecsahsr_check_empty
  # status 1 (not in trie) -> spec returns 0 (output already zero).
  li t0, 1
  beq a0, t0, .Lecsahsr_success_zero
  # status 2/3 -> propagate.
  j .Lecsahsr_ret
.Lecsahsr_success_zero:
  li a0, 0
  j .Lecsahsr_ret
.Lecsahsr_check_empty:
  # code_hash == EMPTY_CODE_HASH ?
  la t0, ecsahsr_empty_code_hash
  ld t1,  0(t0); ld t2, 72(s7); bne t1, t2, .Lecsahsr_lookup
  ld t1,  8(t0); ld t2, 80(s7); bne t1, t2, .Lecsahsr_lookup
  ld t1, 16(t0); ld t2, 88(s7); bne t1, t2, .Lecsahsr_lookup
  ld t1, 24(t0); ld t2, 96(s7); bne t1, t2, .Lecsahsr_lookup
  # code is empty; output stays 0, return 0.
  li a0, 0
  j .Lecsahsr_ret
.Lecsahsr_lookup:
  # Step 3: witness_codes_lookup_by_hash(codes, &acct.code_hash).
  mv a0, s5
  mv a1, s6
  addi a2, s7, 72            # &acct.code_hash
  la a3, ecsahsr_dummy_offset
  la a4, ecsahsr_code_len
  jal ra, witness_codes_lookup_by_hash
  beqz a0, .Lecsahsr_ret
  # miss -> witness integrity violation (5); zero output.
  la t0, ecsahsr_code_len
  sd zero, 0(t0)
  li a0, 5
.Lecsahsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
