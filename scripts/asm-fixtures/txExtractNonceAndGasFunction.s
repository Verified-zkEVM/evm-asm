tx_extract_nonce_and_gas:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  sd s7, 64(sp)
  mv s0, a0                   # tx_ptr
  mv s1, a1                   # tx_len
  mv s2, a2                   # nonce out
  mv s3, a3                   # gas out
  sd zero, 0(s2); sd zero, 0(s3)
  # Step 1: tx_type_dispatch
  mv a0, s0; mv a1, s1
  la a2, teng_type
  la a3, teng_inner_off
  jal ra, tx_type_dispatch
  beqz a0, .Lteng_after_dispatch
  li a0, 1
  j .Lteng_ret
.Lteng_after_dispatch:
  la t0, teng_type;      ld s4, 0(t0)    # type → s4
  la t0, teng_inner_off; ld t5, 0(t0)
  add a0, s0, t5                          # inner_ptr
  sub a1, s1, t5                          # inner_len
  jal ra, rlp_walk_init
  bnez a2, .Lteng_nonce_fail
  mv s5, a0                               # cursor
  mv s6, a1                               # end
  # Step 2: extract nonce.
  li t0, 0
  beq s4, t0, .Lteng_n_legacy
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_nonce_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_nonce_fail
  sub t6, a0, a2              # content ptr
  j .Lteng_n_have_field
.Lteng_n_legacy:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_nonce_fail
  sub t6, a0, a2              # content ptr
.Lteng_n_have_field:
  mv s7, a0                              # cursor after nonce
  mv a0, t6
  mv a1, a2
  jal ra, rlp_content_to_u64_strict
  beqz a1, .Lteng_step3
.Lteng_nonce_fail:
  sd zero, 0(s2)
  li a0, 2
  j .Lteng_ret
.Lteng_step3:
  sd a0, 0(s2)
  ld t0, 0(s2)
  li t1, -1                              # EIP-2681 rejects u64 max
  bne t0, t1, .Lteng_nonce_under_cap
  sd zero, 0(s2)
  li a0, 4
  j .Lteng_ret
.Lteng_nonce_under_cap:
  mv s5, s7                              # continue from after nonce
  # Step 3: extract gas_limit.
  li t0, 0
  beq s4, t0, .Lteng_g_legacy
  li t0, 1
  beq s4, t0, .Lteng_g_2930
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_gas_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_gas_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_gas_fail
  sub t6, a0, a2              # content ptr
  j .Lteng_g_have_field
.Lteng_g_legacy:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_gas_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_gas_fail
  sub t6, a0, a2              # content ptr
  j .Lteng_g_have_field
.Lteng_g_2930:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_gas_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteng_gas_fail
  sub t6, a0, a2              # content ptr
.Lteng_g_have_field:
  mv a0, t6
  mv a1, a2
  jal ra, rlp_content_to_u64_strict
  beqz a1, .Lteng_store_gas
.Lteng_gas_fail:
  sd zero, 0(s3)
  li a0, 3
  j .Lteng_ret
.Lteng_store_gas:
  sd a0, 0(s3)
  j .Lteng_ok
.Lteng_ok:
  li a0, 0
.Lteng_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  ld s7, 64(sp)
  addi sp, sp, 80
  ret
