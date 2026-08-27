tx_extract_data_section:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                   # tx_ptr
  mv s1, a1                   # tx_len
  mv s2, a2                   # data_ptr out
  mv s3, a3                   # data_len out
  sd zero, 0(s2); sd zero, 0(s3)
  # Step 1: tx_type_dispatch.
  mv a0, s0; mv a1, s1
  la a2, teds_type
  la a3, teds_inner_off
  jal ra, tx_type_dispatch
  beqz a0, .Lteds_after_dispatch
  li a0, 1
  j .Lteds_ret
.Lteds_after_dispatch:
  la t0, teds_type;      ld s4, 0(t0)     # type
  la t0, teds_inner_off; ld t5, 0(t0)
  add a0, s0, t5                           # inner_ptr
  sub a1, s1, t5                           # inner_len
  jal ra, rlp_walk_init
  bnez a2, .Lteds_field_fail
  mv s5, a0                                # cursor
  mv s6, a1                                # end
  # Determine field index.
  li t0, 0
  beq s4, t0, .Lteds_legacy_idx
  li t0, 1
  beq s4, t0, .Lteds_t1_idx
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail
  sub t6, a0, a2              # content ptr
  j .Lteds_have_field
.Lteds_legacy_idx:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail
  sub t6, a0, a2              # content ptr
  j .Lteds_have_field
.Lteds_t1_idx:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteds_field_fail
  sub t6, a0, a2              # content ptr
.Lteds_have_field:
  # data_ptr = content ptr; data_len = content length.
  sd t6, 0(s2)
  sd a2, 0(s3)
  li a0, 0
  j .Lteds_ret
.Lteds_field_fail:
  li a0, 2
.Lteds_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
