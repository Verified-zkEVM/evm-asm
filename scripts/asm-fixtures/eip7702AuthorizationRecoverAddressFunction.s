eip7702_authorization_recover_address:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # tuple ptr
  mv s1, a1                   # tuple len
  mv s2, a2                   # 20-byte address out
  mv s3, a3                   # scratch base
  # Clear the address output up front so failure cannot expose stale bytes.
  sd zero, 0(s2); sd zero, 8(s2); sw zero, 16(s2)
  # Clear the material block. Only +8/+16/+48/+80 are semantically used by
  # tx_pubkey_ecrecover_stage_material, but zeroing keeps probes readable.
  mv t0, s3; li t1, 16
.La77ra_zero_material:
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .La77ra_zero_material
  # Extract y_parity/r/s into material +8/+16/+48.
  mv a0, s0; mv a1, s1; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48
  jal ra, eip7702_authorization_extract_signature
  beqz a0, .La77ra_sig_ok
  li a0, 10
  j .La77ra_ret
.La77ra_sig_ok:
  # Compute signing hash into material +80.
  mv a0, s0; mv a1, s1; addi a2, s3, 80
  jal ra, eip7702_authorization_signing_hash
  beqz a0, .La77ra_hash_ok
  li a0, 20
  j .La77ra_ret
.La77ra_hash_ok:
  # Validate recid/y_parity and scalar ranges before calling the recovery kernel.
  ld t0, 8(s3); li t1, 1; bgtu t0, t1, .La77ra_bad_y
  addi a0, s3, 16; jal ra, u256_is_zero
  bnez a0, .La77ra_r_zero
  addi a0, s3, 48; jal ra, u256_is_zero
  bnez a0, .La77ra_s_zero
  addi a0, s3, 16; la a1, a77ra_secp256k1_n; la a2, a77ra_cmp
  jal ra, u256_lt_be
  la t0, a77ra_cmp; ld t1, 0(t0); beqz t1, .La77ra_r_order
  la a0, a77ra_secp256k1_half_n; addi a1, s3, 48; la a2, a77ra_cmp
  jal ra, u256_lt_be
  la t0, a77ra_cmp; ld t1, 0(t0); bnez t1, .La77ra_s_high
  # Stage the material and recover the public key.
  mv a0, s3; addi a1, s3, 128
  jal ra, tx_pubkey_ecrecover_stage_material
  beqz a0, .La77ra_stage_ok
  li a0, 50
  j .La77ra_ret
.La77ra_stage_ok:
  addi a0, s3, 128; addi a1, s3, 296
  jal ra, secp256k1_recover_pubkey_staged
  beqz a0, .La77ra_recover_ok
  li a0, 60
  j .La77ra_ret
.La77ra_recover_ok:
  addi a0, s3, 296; mv a1, s2
  jal ra, address_from_pubkey
  li a0, 0
  j .La77ra_ret
.La77ra_bad_y:
  li a0, 31
  j .La77ra_ret
.La77ra_r_zero:
  li a0, 40
  j .La77ra_ret
.La77ra_s_zero:
  li a0, 41
  j .La77ra_ret
.La77ra_r_order:
  li a0, 42
  j .La77ra_ret
.La77ra_s_high:
  li a0, 43
.La77ra_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
