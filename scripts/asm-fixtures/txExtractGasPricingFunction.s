tx_extract_gas_pricing:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  sd s7, 64(sp)
  mv s0, a0                   # tx_ptr
  mv s1, a1                   # tx_len
  mv s2, a2                   # max_priority_fee out (32B)
  mv s3, a3                   # max_fee out (32B)
  # Pre-zero both outputs.
  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)
  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)
  # Step 1: tx_type_dispatch.
  mv a0, s0; mv a1, s1
  la a2, tegp_type
  la a3, tegp_inner_off
  jal ra, tx_type_dispatch
  beqz a0, .Ltegp_after_dispatch
  li a0, 1
  j .Ltegp_ret
.Ltegp_after_dispatch:
  la t0, tegp_type;      ld s4, 0(t0)    # type → s4
  la t0, tegp_inner_off; ld t5, 0(t0)
  add a0, s0, t5                          # inner_ptr
  sub a1, s1, t5                          # inner_len
  jal ra, rlp_walk_init
  bnez a2, .Ltegp_p_fail
  mv s5, a0                               # cursor
  mv s6, a1                               # end
  # Determine first u256 field index.
  # Legacy: gas_price=1. 2930: gas_price=2. 1559/4844/7702: max_priority=2.
  li t0, 0
  beq s4, t0, .Ltegp_p_legacy
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltegp_p_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltegp_p_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltegp_p_fail
  sub t6, a0, a2              # content ptr
  j .Ltegp_p_have
.Ltegp_p_legacy:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltegp_p_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltegp_p_fail
  sub t6, a0, a2              # content ptr
.Ltegp_p_have:
  mv s7, a0                               # cursor after first fee field
  mv a0, t6
  mv a1, a2
  mv a2, s2
  jal ra, rlp_content_to_u256_be_strict
  beqz a0, .Ltegp_after_p
.Ltegp_p_fail:
  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)
  li a0, 2
  j .Ltegp_ret
.Ltegp_after_p:
  # If legacy or 2930, copy max_priority_fee → max_fee.
  li t0, 2
  bgeu s4, t0, .Ltegp_typed_fee
  ld t0,  0(s2); sd t0,  0(s3)
  ld t0,  8(s2); sd t0,  8(s3)
  ld t0, 16(s2); sd t0, 16(s3)
  ld t0, 24(s2); sd t0, 24(s3)
  li a0, 0
  j .Ltegp_ret
.Ltegp_typed_fee:
  # Type 2/3/4: max_fee = next field after max_priority.
  mv s5, s7
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltegp_fee_fail
  sub t6, a0, a2              # content ptr
  mv a0, t6
  mv a1, a2
  mv a2, s3
  jal ra, rlp_content_to_u256_be_strict
  beqz a0, .Ltegp_ok
.Ltegp_fee_fail:
  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)
  li a0, 3
  j .Ltegp_ret
.Ltegp_ok:
  li a0, 0
.Ltegp_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  ld s7, 64(sp)
  addi sp, sp, 80
  ret
