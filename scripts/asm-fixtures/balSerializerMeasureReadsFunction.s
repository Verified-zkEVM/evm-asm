bal_serializer_measure_reads:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0
  li s1, 0
  la t0, storage_reads_count; ld s2, 0(t0)
  li s3, 0
.Lbsmr_loop:
  bgeu s3, s2, .Lbsmr_done
  li t0, 0xa1908780; slli t1, s3, 6; add t4, t0, t1
  mv a0, s0; mv a1, t4; jal ra, bal_serializer_addr_matches
  beqz a0, .Lbsmr_next
  li t0, 0xa1908780; slli t1, s3, 6; add t4, t0, t1
  addi a0, t4, 32; mv a1, s0; jal ra, bal_serializer_slot_written
  bnez a0, .Lbsmr_next
  li t0, 0xa1908780; slli t1, s3, 6; add t4, t0, t1
  addi a0, t4, 32; jal ra, bal_rlp_scalar_rlp_len
  add s1, s1, a0
.Lbsmr_next:
  addi s3, s3, 1; j .Lbsmr_loop
.Lbsmr_done:
  la t0, bal_serializer_len_table; sd s1, 16(t0)
  mv a0, s1
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
