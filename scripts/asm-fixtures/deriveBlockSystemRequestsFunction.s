derive_block_system_requests:
  la t0, dbsr_saved_ra; sd ra, 0(t0)
  la t0, dbsr_ccode; sd a2, 0(t0)
  la t0, dbsr_in_clen; sd a3, 0(t0)
  la t0, dbsr_exec; sd a4, 0(t0)
  la t0, dbsr_staging; sd a5, 0(t0)
  mv a2, a4; mv a3, a5
  jal ra, derive_withdrawal_requests
  bnez a2, .Ldbsr_fail
  la t0, dbsr_wlen; sd a1, 0(t0)
  mv t1, a0; la t2, dbsr_wbody; mv t3, a1
.Ldbsr_wcopy:
  beqz t3, .Ldbsr_wcopy_d; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Ldbsr_wcopy
.Ldbsr_wcopy_d:
  jal ra, read_sets_incorporate_tx
  la t0, dbsr_ccode; ld a0, 0(t0); la t0, dbsr_in_clen; ld a1, 0(t0)
  la t0, dbsr_exec; ld a2, 0(t0); la t0, dbsr_staging; ld a3, 0(t0)
  jal ra, derive_consolidation_requests
  bnez a2, .Ldbsr_fail
  la t0, dbsr_clen; sd a1, 0(t0)
  mv t1, a0; la t2, dbsr_cbody; mv t3, a1
.Ldbsr_ccopy:
  beqz t3, .Ldbsr_ccopy_d; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Ldbsr_ccopy
.Ldbsr_ccopy_d:
  jal ra, read_sets_incorporate_tx
  li a0, 0; j .Ldbsr_ret
.Ldbsr_fail:
  li a0, 1
.Ldbsr_ret:
  la t0, dbsr_saved_ra; ld ra, 0(t0); ret
