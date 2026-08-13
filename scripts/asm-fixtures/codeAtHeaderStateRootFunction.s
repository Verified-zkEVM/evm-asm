code_at_header_state_root:
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
  # Step 1: header.state_root -> cahsr_state_root.
  mv a0, s0
  mv a1, s1
  la a2, cahsr_state_root
  jal ra, header_extract_state_root
  beqz a0, .Lcahsr_step2
  li a0, 4
  j .Lcahsr_ret
.Lcahsr_step2:
  # Step 2: account_at_address -> cahsr_acct_struct.
  mv a0, s2
  li a1, 20
  la a2, cahsr_state_root
  mv a3, s3
  mv a4, s4
  la a5, cahsr_acct_struct
  jal ra, account_at_address
  beqz a0, .Lcahsr_step3
  # STATUS_VOCAB: account→cahsr — remap Account.unresolved(4) → Cahsr.unresolved(6)
  # (must not identity-pass 4: Cahsr.headerFail is also 4).
  li t0, 4
  bne a0, t0, .Lcahsr_ret     # absent=1 / parse=2 / decodeFail=3 pass through
  li a0, 6
  j .Lcahsr_ret
.Lcahsr_step3:
  # Step 3: witness_codes_lookup_by_hash(codes, &acct.code_hash).
  mv a0, s5
  mv a1, s6
  la a2, cahsr_acct_struct
  addi a2, a2, 72            # &acct_struct.code_hash
  la a3, cahsr_code_offset
  la a4, cahsr_code_length
  mv a5, s2                  # GH #10619: address ptr for the CodeRead tuple
  jal ra, code_read_fetch
  beqz a0, .Lcahsr_ret       # a0=0 hit
  li a0, 5                   # miss -> 5
.Lcahsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
