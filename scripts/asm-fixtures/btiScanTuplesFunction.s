bti_scan_tuples:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  jal ra, rlp_walk_init
  beqz a2, .Lbtxi_st_ok
  li t0, 1; la t1, bti_err; sd t0, 0(t1); j .Lbtxi_st_ret
.Lbtxi_st_ok:
  mv s0, a0                                   # tuple cursor
  mv s1, a1                                   # tuple-list end
.Lbtxi_st_loop:
  beq s0, s1, .Lbtxi_st_ret
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next
  bnez a1, .Lbtxi_st_err
  mv s0, a0; sub s2, a0, a2; mv s3, a2            # tuple ptr/len
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_init
  bnez a2, .Lbtxi_st_err
  jal ra, rlp_walk_next                            # item 0 = tx_index field
  bnez a1, .Lbtxi_st_err
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lbtxi_st_err
  mv t6, a0
.Lbtxi_st_have:
  beqz t6, .Lbtxi_st_sysnowrite                    # fhsxz.2.4.2.57.11.6.3.3: tx_index 0 (system) is not a user write
  li t0, 1; la t1, bti_has_write; sd t0, 0(t1)
.Lbtxi_st_sysnowrite:
  la t0, bti_first_tx; ld t1, 0(t0)
  li t2, 0x7fffffff
  bne t1, t2, .Lbtxi_st_cmp
  sd t6, 0(t0); j .Lbtxi_st_adv                      # first tx for this account
.Lbtxi_st_cmp:
  beq t1, t6, .Lbtxi_st_adv
  li t2, 1; la t0, bti_conflict; sd t2, 0(t0)       # >=2 distinct tx => conflict
.Lbtxi_st_adv:
  j .Lbtxi_st_loop
.Lbtxi_st_err:
  li t0, 1; la t1, bti_err; sd t0, 0(t1)
.Lbtxi_st_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
