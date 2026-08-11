bal_serializer_emit_reads:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  la t0, storage_reads_count; ld s3, 0(t0)
  li s4, 0
.Lbser_loop:
  bgeu s4, s3, .Lbser_done
  li t0, 0xa1908780; slli t1, s4, 6; add t4, t0, t1; sd t4, 48(sp)
  mv a0, s1; mv a1, t4; jal ra, bal_serializer_addr_matches
  beqz a0, .Lbser_next
  ld t4, 48(sp); addi a0, t4, 32; mv a1, s1; jal ra, bal_serializer_slot_written
  bnez a0, .Lbser_next
  ld t4, 48(sp); mv a0, s0; addi a1, t4, 32; mv a2, s2; jal ra, bal_rlp_emit_scalar
  la t0, bv_bal_shadow_emit_storage_reads; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
.Lbser_next:
  addi s4, s4, 1; j .Lbser_loop
.Lbser_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 64
  ret
