bal_serializer_verify:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a0
  mv a0, a1; la a1, bal_serializer_rebuilt_hash; jal ra, bal_serializer_rebuild_hash
  beqz a0, .Lbsv_rebuilt
  li a0, 2; j .Lbsv_ret
.Lbsv_rebuilt:
  mv a0, s0; la a1, bal_serializer_supplied_hash; jal ra, block_access_list_hash
  la t0, bal_serializer_rebuilt_hash; la t1, bal_serializer_supplied_hash
  ld t2, 0(t0);  ld t3, 0(t1);  bne t2, t3, .Lbsv_differ
  ld t2, 8(t0);  ld t3, 8(t1);  bne t2, t3, .Lbsv_differ
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbsv_differ
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbsv_differ
  li a0, 0; j .Lbsv_ret
.Lbsv_differ:
  li a0, 1
.Lbsv_ret:
  ld ra, 0(sp); ld s0, 8(sp)
  addi sp, sp, 32
  ret
