bal_serializer_slot_seen_before:
  addi sp, sp, -48; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  li s3, 0
.Lbssb_loop:
  bgeu s3, s2, .Lbssb_no
  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add t3, t2, t1
  mv a0, s0; mv a1, t3; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbssb_next
  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add t3, t2, t1
  addi a0, s1, 32; addi a1, t3, 32; jal ra, bal_serializer_slot_eq
  bnez a0, .Lbssb_yes
.Lbssb_next:
  addi s3, s3, 1; j .Lbssb_loop
.Lbssb_yes:
  li a0, 1; j .Lbssb_ret
.Lbssb_no:
  li a0, 0
.Lbssb_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48; ret
