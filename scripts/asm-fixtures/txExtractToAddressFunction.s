tx_extract_to_address:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                   # tx_bytes ptr
  mv s1, a1                   # tx_len
  mv s2, a2                   # 20B out ptr
  mv s3, a3                   # is_creation out ptr
  # Pre-zero outputs in case of failure.
  sd zero,  0(s2); sd zero,  8(s2); sw zero, 16(s2)
  sd zero,  0(s3)
  # Step 1: tx_type_dispatch(tx, len, &type, &inner_off)
  mv a0, s0; mv a1, s1
  la a2, tea_type
  la a3, tea_inner_off
  jal ra, tx_type_dispatch
  beqz a0, .Ltea_after_dispatch
  li a0, 1
  j .Ltea_ret
.Ltea_after_dispatch:
  la t0, tea_type;      ld s4, 0(t0)    # type
  la t0, tea_inner_off; ld t5, 0(t0)    # inner_off
  add a0, s0, t5                         # inner_ptr
  sub a1, s1, t5                         # inner_len
  jal ra, rlp_walk_init
  bnez a2, .Ltea_field_fail
  mv s5, a0                              # cursor
  mv s6, a1                              # end
  # Determine field index based on type: 0 -> 3, 1 -> 4, 2/3/4 -> 5.
  li t0, 0
  beq s4, t0, .Ltea_legacy_idx
  li t0, 1
  beq s4, t0, .Ltea_t1_idx
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail
  sub t6, a0, a2              # content ptr
  j .Ltea_have_field
.Ltea_legacy_idx:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail
  sub t6, a0, a2              # content ptr
  j .Ltea_have_field
.Ltea_t1_idx:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltea_field_fail
  sub t6, a0, a2              # content ptr
.Ltea_have_field:
  mv t2, a2                    # content length
  beqz t2, .Ltea_creation
  li t1, 20
  bne t2, t1, .Ltea_field_fail
  # Copy 20 bytes from content pointer t6 to s2.
  ld t0,  0(t6); sd t0,  0(s2)
  ld t0,  8(t6); sd t0,  8(s2)
  lwu t0, 16(t6); sw t0, 16(s2)
  sd zero, 0(s3)              # is_creation = 0
  li a0, 0
  j .Ltea_ret
.Ltea_creation:
  li t0, 1
  sd t0, 0(s3)                # is_creation = 1
  li a0, 0
  j .Ltea_ret
.Ltea_field_fail:
  li a0, 2
.Ltea_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
