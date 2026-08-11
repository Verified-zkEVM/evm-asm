bal_builder_incorporate_touched_accounts:
  addi sp, sp, -32; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  la s0, account_reads_count; ld s1, 0(s0); li s2, 0
.Lbbita_loop:
  bgeu s2, s1, .Lbbita_done
  slli t0, s2, 5; li t1, 0xa1d1a200; add a0, t1, t0
  jal ra, bal_builder_ensure_account
  addi s2, s2, 1; j .Lbbita_loop
.Lbbita_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 32; ret
