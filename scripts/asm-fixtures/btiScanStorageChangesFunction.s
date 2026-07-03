bti_scan_storage_changes:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  jal ra, rlp_walk_init
  beqz a2, .Lbtxi_sc_ok
  li t0, 1; la t1, bti_err; sd t0, 0(t1); j .Lbtxi_sc_ret
.Lbtxi_sc_ok:
  mv s0, a0; mv s1, a1
.Lbtxi_sc_loop:
  beq s0, s1, .Lbtxi_sc_ret
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next
  bnez a1, .Lbtxi_sc_err
  mv s0, a0; sub s2, a0, a2; mv s3, a2              # SlotChanges ptr/len
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_init
  bnez a2, .Lbtxi_sc_err
  mv s3, a1                                         # SlotChanges end
  jal ra, rlp_walk_next                              # item 0 = slot
  bnez a1, .Lbtxi_sc_err
  mv a1, s3
  jal ra, rlp_walk_next                              # item 1 = [tuples]
  bnez a1, .Lbtxi_sc_err
  sub a0, a0, a2; mv a1, a2
  jal ra, bti_scan_tuples
  j .Lbtxi_sc_loop
.Lbtxi_sc_err:
  li t0, 1; la t1, bti_err; sd t0, 0(t1)
.Lbtxi_sc_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
