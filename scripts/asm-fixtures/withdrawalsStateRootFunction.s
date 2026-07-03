withdrawals_state_root:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # pre-state root hash
  mv s1, a1                   # witness
  mv s2, a2                   # witness_len
  mv s3, a3                   # withdrawals descriptors
  mv s4, a4                   # n_withdrawals
  mv s5, a5                   # out_root
  li s6, 0                    # i
.Lwsr_loop:
  beq s6, s4, .Lwsr_apply
  slli t0, s6, 4; add t0, s3, t0    # &wd[i]
  ld a0, 0(t0)                # wd_rlp ptr
  ld a1, 8(t0)                # wd_rlp len
  la t1, ws_path; slli t2, s6, 6; add a2, t1, t2   # path dst = ws_path + 64*i
  la a3, ws_delta
  jal ra, withdrawal_to_path_delta
  bnez a0, .Lwsr_fail
  # read current account from pre-state: mpt_walk(root, witness, path, 64).
  mv a0, s0; mv a1, s1; mv a2, s2
  la t1, ws_path; slli t2, s6, 6; add a3, t1, t2
  li a4, 64
  la a5, ws_acct; la a6, ws_acct_len
  jal ra, mpt_walk
  bnez a0, .Lwsr_insert       # not found => insert needed (unsupported)
  # new account = account_add_balance(account, delta).
  la a0, ws_acct
  la t0, ws_acct_len; ld a1, 0(t0)
  la a2, ws_delta
  la t1, ws_newacct; slli t2, s6, 7; add a3, t1, t2   # new acct dst = ws_newacct + 128*i
  la a4, ws_newacct_len
  jal ra, account_add_balance
  bnez a0, .Lwsr_fail
  # record change[i] = (path_ptr, 64, value_ptr, value_len).
  la t0, ws_changes; slli t1, s6, 5; add t0, t0, t1
  la t1, ws_path; slli t2, s6, 6; add t1, t1, t2; sd t1, 0(t0)
  li t1, 64; sd t1, 8(t0)
  la t1, ws_newacct; slli t2, s6, 7; add t1, t1, t2; sd t1, 16(t0)
  la t1, ws_newacct_len; ld t1, 0(t1); sd t1, 24(t0)
  addi s6, s6, 1
  j .Lwsr_loop
.Lwsr_apply:
  mv a0, s0; mv a1, s1; mv a2, s2
  la a3, ws_changes; mv a4, s4; mv a5, s5
  jal ra, mpt_state_root
  j .Lwsr_ret
.Lwsr_insert:
  li a0, 1
  j .Lwsr_ret
.Lwsr_fail:
  li a0, 2
.Lwsr_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
