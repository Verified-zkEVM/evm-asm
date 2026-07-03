bal_account_nonstorage_consistent:
  addi sp, sp, -32
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a2                   # exec effect record ptr
  la s1, c2nsc_finals         # 88-byte finals scratch
  mv a2, s1                   # finals out = scratch (a0/a1 still AccountChanges ptr/len)
  jal ra, bal_account_nonstorage_finals
  bnez a0, .Lc2nsc_parsefail  # BAL parse failure -> 2
  # ---- balance: reverse (exec changed -> declared) + forward (declared -> BAL==exec post) ----
  ld t0, 0(s1)                # has_balance
  addi t2, s0, 32             # exec pre_balance
  addi t3, s0, 64             # exec post_balance
  li t1, 0                    # exec_balance_changed
  ld t4, 0(t2);  ld t5, 0(t3);  bne t4, t5, .Lc2nsc_bal_chg
  ld t4, 8(t2);  ld t5, 8(t3);  bne t4, t5, .Lc2nsc_bal_chg
  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lc2nsc_bal_chg
  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lc2nsc_bal_chg
  j .Lc2nsc_bal_chk
.Lc2nsc_bal_chg:
  li t1, 1
.Lc2nsc_bal_chk:
  beqz t1, .Lc2nsc_bal_fwd    # exec unchanged -> no reverse obligation
  beqz t0, .Lc2nsc_bad        # exec changed but BAL silent -> inconsistent
.Lc2nsc_bal_fwd:
  beqz t0, .Lc2nsc_nonce      # BAL silent -> nothing to forward-check
  addi t2, s1, 8              # BAL final post_balance (32 B BE)
  addi t3, s0, 64             # exec post_balance
  ld t4, 0(t2);  ld t5, 0(t3);  bne t4, t5, .Lc2nsc_bad
  ld t4, 8(t2);  ld t5, 8(t3);  bne t4, t5, .Lc2nsc_bad
  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lc2nsc_bad
  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lc2nsc_bad
.Lc2nsc_nonce:
  # ---- nonce: reverse + forward, u64 ----
  ld t0, 40(s1)               # has_nonce
  ld t2, 96(s0)               # exec pre_nonce
  ld t3, 104(s0)              # exec post_nonce
  beq t2, t3, .Lc2nsc_nonce_fwd  # exec unchanged -> no reverse obligation
  beqz t0, .Lc2nsc_bad           # exec changed but BAL silent -> inconsistent
.Lc2nsc_nonce_fwd:
  beqz t0, .Lc2nsc_ok         # BAL silent -> nothing to forward-check
  ld t4, 48(s1)               # BAL final post_nonce (u64)
  bne t4, t3, .Lc2nsc_bad
.Lc2nsc_ok:
  li a0, 0; j .Lc2nsc_ret
.Lc2nsc_bad:
  li a0, 1; j .Lc2nsc_ret
.Lc2nsc_parsefail:
  li a0, 2
.Lc2nsc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
