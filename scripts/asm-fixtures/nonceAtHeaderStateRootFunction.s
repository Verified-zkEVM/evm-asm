nonce_at_header_state_root:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # witness.state ptr
  mv s4, a4                  # witness.state len
  mv s5, a5                  # u64 out ptr
  # Pre-zero output -- NONCE default value.
  sd zero, 0(s5)
  # Step 1: header.state_root -> nonce_state_root.
  mv a0, s0
  mv a1, s1
  la a2, nonce_state_root
  jal ra, header_extract_state_root
  beqz a0, .Lnonce_step2
  li a0, 4
  j .Lnonce_ret
.Lnonce_step2:
  # Step 2: account_at_address -> nonce_acct_struct.
  mv a0, s2
  li a1, 20
  la a2, nonce_state_root
  mv a3, s3
  mv a4, s4
  la s6, nonce_acct_struct
  mv a5, s6
  jal ra, account_at_address
  beqz a0, .Lnonce_copy
  li t0, 1
  beq a0, t0, .Lnonce_absent
  j .Lnonce_ret
.Lnonce_absent:
  li a0, 0
  j .Lnonce_ret
.Lnonce_copy:
  # Copy nonce (struct + 0 .. + 8) to output.
  ld t1, 0(s6); sd t1, 0(s5)
  li a0, 0
.Lnonce_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
