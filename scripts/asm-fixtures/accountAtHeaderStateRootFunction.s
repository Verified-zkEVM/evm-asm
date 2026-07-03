account_at_header_state_root:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # address_len
  mv s4, a4                  # witness ptr
  mv s5, a5                  # witness_len
  mv s6, a6                  # output struct ptr
  # Step 1: extract header.state_root -> aahsr_state_root.
  mv a0, s0
  mv a1, s1
  la a2, aahsr_state_root
  jal ra, header_extract_state_root
  beqz a0, .Laahsr_step2
  # Header parse / size fail: zero output struct, return 4.
  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)
  sd zero, 32(s6); sd zero, 40(s6); sd zero, 48(s6); sd zero, 56(s6)
  sd zero, 64(s6); sd zero, 72(s6); sd zero, 80(s6); sd zero, 88(s6)
  sd zero, 96(s6)
  li a0, 4
  j .Laahsr_ret
.Laahsr_step2:
  # Step 2: account_at_address(addr, len, &state_root, witness, len, out).
  mv a0, s2
  mv a1, s3
  la a2, aahsr_state_root
  mv a3, s4
  mv a4, s5
  mv a5, s6
  jal ra, account_at_address
  # a0 already holds account_at_address's status (0/1/2/3).
.Laahsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
