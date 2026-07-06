tx_pubkey_signature_material:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0                   # tx ptr
  mv s1, a1                   # tx len
  mv s2, a2                   # chain_id
  mv s3, a3                   # output ptr
  sd zero,   0(s3); sd zero,   8(s3); sd zero,  16(s3); sd zero,  24(s3)
  sd zero,  32(s3); sd zero,  40(s3); sd zero,  48(s3); sd zero,  56(s3)
  sd zero,  64(s3); sd zero,  72(s3); sd zero,  80(s3); sd zero,  88(s3)
  sd zero,  96(s3); sd zero, 104(s3); sd zero, 112(s3); sd zero, 120(s3)
  mv a0, s0; mv a1, s1; la a2, tps_type; la a3, tps_inner_off
  jal ra, tx_type_dispatch
  bnez a0, .Ltps_type_fail
  la t0, tps_type; ld s4, 0(t0); sd s4, 0(s3)
  la t0, tps_inner_off; ld s5, 0(t0); sd s5, 112(s3)
  bltu s1, s5, .Ltps_inner_oob
  add s6, s0, s5              # inner ptr
  sub s7, s1, s5              # inner len
  beqz s4, .Ltps_legacy
  li t0, 1; beq s4, t0, .Ltps_t1
  li t0, 2; beq s4, t0, .Ltps_t2
  li t0, 3; beq s4, t0, .Ltps_t3
  li t0, 4; beq s4, t0, .Ltps_t4
  j .Ltps_type_fail
.Ltps_legacy:
  mv a0, s0; mv a1, s1; la a2, tps_v; addi a3, s3, 16; addi a4, s3, 48
  jal ra, tx_legacy_extract_signature
  bnez a0, .Ltps_sig_fail
  la t0, tps_v; ld t1, 0(t0)
  li t2, 27; beq t1, t2, .Ltps_legacy_v27
  li t2, 28; beq t1, t2, .Ltps_legacy_v28
  slli t2, s2, 1
  li t3, 35; add t3, t3, t2
  beq t1, t3, .Ltps_legacy_eip155_y0
  addi t3, t3, 1
  beq t1, t3, .Ltps_legacy_eip155_y1
  j .Ltps_bad_v
.Ltps_legacy_v27:
  sd zero, 8(s3); sd zero, 120(s3)
  mv a0, s0; mv a1, s1; li a2, 6; li a3, 0; addi a4, s3, 80
  jal ra, tx_signing_hash
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_scalars
.Ltps_legacy_v28:
  li t0, 1; sd t0, 8(s3); sd zero, 120(s3)
  mv a0, s0; mv a1, s1; li a2, 6; li a3, 0; addi a4, s3, 80
  jal ra, tx_signing_hash
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_scalars
.Ltps_legacy_eip155_y0:
  sd zero, 8(s3); li t0, 1; sd t0, 120(s3)
  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s3, 80
  jal ra, tx_signing_hash_legacy_eip155
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_scalars
.Ltps_legacy_eip155_y1:
  li t0, 1; sd t0, 8(s3); sd t0, 120(s3)
  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s3, 80
  jal ra, tx_signing_hash_legacy_eip155
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_scalars
.Ltps_t1:
  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48
  jal ra, tx_eip2930_extract_signature
  bnez a0, .Ltps_sig_fail
  mv a0, s6; mv a1, s7; li a2, 8; li a3, 1; addi a4, s3, 80
  jal ra, tx_signing_hash
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_y
.Ltps_t2:
  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48
  jal ra, tx_eip1559_extract_signature
  bnez a0, .Ltps_sig_fail
  mv a0, s6; mv a1, s7; li a2, 9; li a3, 2; addi a4, s3, 80
  jal ra, tx_signing_hash
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_y
.Ltps_t3:
  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48
  jal ra, tx_eip4844_extract_signature
  bnez a0, .Ltps_sig_fail
  mv a0, s6; mv a1, s7; li a2, 11; li a3, 3; addi a4, s3, 80
  jal ra, tx_signing_hash
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_y
.Ltps_t4:
  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48
  jal ra, tx_eip7702_extract_signature
  bnez a0, .Ltps_sig_fail
  mv a0, s6; mv a1, s7; li a2, 10; li a3, 4; addi a4, s3, 80
  jal ra, tx_signing_hash
  bnez a0, .Ltps_hash_fail
  j .Ltps_validate_y
.Ltps_validate_y:
  ld t0, 8(s3)
  li t1, 1
  bgtu t0, t1, .Ltps_bad_y
.Ltps_validate_scalars:
  addi a0, s3, 16; jal ra, u256_is_zero
  bnez a0, .Ltps_r_zero
  addi a0, s3, 48; jal ra, u256_is_zero
  bnez a0, .Ltps_s_zero
  addi a0, s3, 16; la a1, tps_secp256k1_n; la a2, tps_cmp
  jal ra, u256_lt_be
  la t0, tps_cmp; ld t1, 0(t0)
  beqz t1, .Ltps_r_order
  la a0, tps_secp256k1_half_n; addi a1, s3, 48; la a2, tps_cmp
  jal ra, u256_lt_be
  la t0, tps_cmp; ld t1, 0(t0)
  bnez t1, .Ltps_s_high
  li a0, 0
  j .Ltps_ret
.Ltps_type_fail:
  li a0, 1; j .Ltps_ret
.Ltps_inner_oob:
  li a0, 2; j .Ltps_ret
.Ltps_sig_fail:
  li a0, 10; j .Ltps_ret
.Ltps_hash_fail:
  li a0, 20; j .Ltps_ret
.Ltps_bad_v:
  li a0, 30; j .Ltps_ret
.Ltps_bad_y:
  li a0, 31; j .Ltps_ret
.Ltps_r_zero:
  li a0, 40; j .Ltps_ret
.Ltps_s_zero:
  li a0, 41; j .Ltps_ret
.Ltps_r_order:
  li a0, 42; j .Ltps_ret
.Ltps_s_high:
  li a0, 43
.Ltps_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 80
  ret
