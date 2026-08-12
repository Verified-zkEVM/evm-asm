bal_serializer_filter_reads:
  addi sp, sp, -32; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0
  la t0, bal_serializer_surviving_read_count; sd zero, 0(t0)
  li s1, 0
  la t0, storage_reads_count; ld s2, 0(t0)
  li t3, 0
.Lbsfr_read:
  bgeu t3, s2, .Lbsfr_done
  li t0, 0xa1908780; slli t1, t3, 6; add t4, t0, t1
  mv a0, s0; mv a1, t4; jal ra, bal_serializer_addr_matches
  beqz a0, .Lbsfr_next
  addi a0, t4, 32; mv a1, s0; jal ra, bal_serializer_slot_written
  bnez a0, .Lbsfr_next
  addi s1, s1, 1
.Lbsfr_next:
  addi t3, t3, 1; j .Lbsfr_read
.Lbsfr_done:
  la t0, bal_serializer_surviving_read_count; sd s1, 0(t0)
  mv a0, s1
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
