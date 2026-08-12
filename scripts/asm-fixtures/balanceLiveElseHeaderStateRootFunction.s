balance_live_else_header_state_root:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # witness.state ptr
  mv s4, a4                  # witness.state len
  mv s5, a5                  # 32-byte u256 BE output ptr
  # Pre-zero output -- BALANCE default value.
  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)
  la t0, bal_addr_padded; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)
  mv t1, s2; mv t2, t0; li t3, 20
.Lbal_padcp:
  beqz t3, .Lbal_padcp_d; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbal_padcp
.Lbal_padcp_d:
  la a0, bal_addr_padded; mv a1, s5; li a2, 2; jal ra, account_writes_latest_balance
  beqz a0, .Lbal_live_miss     # no live effect -> fall through to the pre-state path
  li a0, 0; j .Lbal_ret        # live hit: s5 = post_balance -> success
.Lbal_live_miss:
  # Step 1: header.state_root -> bal_state_root.
  mv a0, s0
  mv a1, s1
  la a2, bal_state_root
  jal ra, header_extract_state_root
  beqz a0, .Lbal_step2
  li a0, 4
  j .Lbal_ret
.Lbal_step2:
  # Step 2: account_at_address -> bal_acct_struct.
  mv a0, s2
  li a1, 20
  la a2, bal_state_root
  mv a3, s3
  mv a4, s4
  la s6, bal_acct_struct
  mv a5, s6
  jal ra, account_at_address
  beqz a0, .Lbal_copy_balance
  li t0, 1
  beq a0, t0, .Lbal_absent  # 1 -> BALANCE returns 0
  # 2/3 propagate; output already zeroed.
  j .Lbal_ret
.Lbal_absent:
  li a0, 0
  j .Lbal_ret
.Lbal_copy_balance:
  # Account found; copy balance (struct + 8 .. + 40) to output.
  ld t1,  8(s6); sd t1,  0(s5)
  ld t1, 16(s6); sd t1,  8(s5)
  ld t1, 24(s6); sd t1, 16(s5)
  ld t1, 32(s6); sd t1, 24(s5)
  li a0, 0
.Lbal_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
