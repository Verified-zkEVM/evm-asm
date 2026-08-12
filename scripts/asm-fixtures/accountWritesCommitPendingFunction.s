account_writes_commit_pending:
  addi sp, sp, -16; sd ra, 0(sp)
  jal ra, account_writes_apply_deletes; bnez a0, .Lawcp_over
  la t0, account_state_created_count; sd zero, 0(t0)
  la t0, account_state_delete_count; sd zero, 0(t0)
  li a0, 0; j .Lawcp_ret
.Lawcp_over:
  la t0, account_writes_overflow; li t1, 1; sd t1, 0(t0); li a0, 1
.Lawcp_ret:
  ld ra, 0(sp); addi sp, sp, 16; ret
