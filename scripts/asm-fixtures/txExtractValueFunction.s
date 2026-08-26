tx_extract_value:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                   # tx_ptr
  mv s1, a1                   # tx_len
  mv s2, a2                   # 32B out ptr
  # Pre-zero output.
  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)
  # Step 1: tx_type_dispatch.
  mv a0, s0; mv a1, s1
  la a2, tev_type
  la a3, tev_inner_off
  jal ra, tx_type_dispatch
  beqz a0, .Ltev_after_dispatch
  li a0, 1
  j .Ltev_ret
.Ltev_after_dispatch:
  la t0, tev_type;      ld s3, 0(t0)    # type → s3
  la t0, tev_inner_off; ld t5, 0(t0)
  add a0, s0, t5                          # inner_ptr
  sub a1, s1, t5                          # inner_len
  jal ra, rlp_walk_init
  bnez a2, .Ltev_field_fail
  mv s5, a0                               # cursor
  mv s6, a1                               # end
  # Determine field index.
  li t0, 0
  beq s3, t0, .Ltev_legacy_idx
  li t0, 1
  beq s3, t0, .Ltev_t1_idx
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail
  sub t6, a0, a2              # content ptr
  j .Ltev_have_field
.Ltev_legacy_idx:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail
  sub t6, a0, a2              # content ptr
  j .Ltev_have_field
.Ltev_t1_idx:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltev_field_fail
  sub t6, a0, a2              # content ptr
.Ltev_have_field:
  mv a0, t6
  mv a1, a2
  mv a2, s2
  jal ra, rlp_content_to_u256_be_strict
  beqz a0, .Ltev_ok
.Ltev_field_fail:
  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)
  li a0, 2
  j .Ltev_ret
.Ltev_ok:
  li a0, 0
.Ltev_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
