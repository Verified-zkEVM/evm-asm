bal_account_nonstorage_consistent:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a2
  la a2, c2nsc_finals
  mv s1, a2
  jal ra, bal_account_nonstorage_finals
  bnez a0, .Lc2nsc_parse
  ld t0, 0(s1)
  addi t1, s0, 32
  addi t2, s0, 64
  ld t3, 0(t1); ld t4, 0(t2); bne t3, t4, .Lc2nsc_bal_net
  ld t3, 8(t1); ld t4, 8(t2); bne t3, t4, .Lc2nsc_bal_net
  ld t3, 16(t1); ld t4, 16(t2); bne t3, t4, .Lc2nsc_bal_net
  ld t3, 24(t1); ld t4, 24(t2); bne t3, t4, .Lc2nsc_bal_net
  bnez t0, .Lc2nsc_fail
  j .Lc2nsc_nonce
.Lc2nsc_bal_net:
  beqz t0, .Lc2nsc_fail
  addi t1, s1, 8
  addi t2, s0, 64
  ld t3, 0(t1); ld t4, 0(t2); bne t3, t4, .Lc2nsc_fail
  ld t3, 8(t1); ld t4, 8(t2); bne t3, t4, .Lc2nsc_fail
  ld t3, 16(t1); ld t4, 16(t2); bne t3, t4, .Lc2nsc_fail
  ld t3, 24(t1); ld t4, 24(t2); bne t3, t4, .Lc2nsc_fail
.Lc2nsc_nonce:
  ld t0, 40(s1)
  ld t1, 96(s0)
  ld t2, 104(s0)
  bne t1, t2, .Lc2nsc_nonce_net
  bnez t0, .Lc2nsc_fail
  j .Lc2nsc_ok
.Lc2nsc_nonce_net:
  beqz t0, .Lc2nsc_fail
  ld t3, 48(s1)
  bne t3, t2, .Lc2nsc_fail
.Lc2nsc_ok:
  li a0, 0; j .Lc2nsc_ret
.Lc2nsc_fail:
  li a0, 1; j .Lc2nsc_ret
.Lc2nsc_parse:
  li a0, 2
.Lc2nsc_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
