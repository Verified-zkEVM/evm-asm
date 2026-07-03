secp256k1_recover_pubkey_staged:
  addi sp, sp, -24
  sd ra,  0(sp)
  sd s3,  8(sp); sd s4, 16(sp)
  mv s4, a0                   # ABI block ptr (hash @+0, r @+32, s @+64, recid @+96)
  mv s3, a1                   # recovered pubkey out
  # 1. Decompress R = (x, y) from r and the recovery id.
  addi a0, s4, 32             # r ptr (ABI+32)
  ld a1, 96(s4)               # recid word (ABI+96); 0 or 1
  la a2, tpr_R
  jal ra, secp256k1_recover_r
  bnez a0, .Ltprr_recover_fail
  # 2. e = msg_hash mod n. The hash is < 2^256 < 2n, so one conditional
  #    subtraction of n is sufficient.
  mv a0, s4                   # msg hash ptr (ABI+0)
  la a1, tpr_e
  jal ra, secf_reduce_once_n
  # 3. r_inv = r^{-1} mod n.
  addi a0, s4, 32             # r ptr
  la a1, tpr_rinv
  jal ra, secf_inv_mod_n
  bnez a0, .Ltprr_recover_fail   # r == 0 (defensive; callers reject it)
  # 4. neg_e = (n - e) mod n, i.e. (-e) mod n (0 when e == 0).
  la a0, tpr_e
  jal ra, secf_is_zero32
  bnez a0, .Ltprr_neg_e_zero
  la a0, secf_n_be
  la a1, tpr_e
  la a2, tpr_nege
  jal ra, u256_sub_be          # nege = n - e (0 < e < n)
  j .Ltprr_have_nege
.Ltprr_neg_e_zero:
  la a0, tpr_nege
  jal ra, secf_zero32
.Ltprr_have_nege:
  # 5. u1 = (-e) * r_inv mod n ; u2 = s * r_inv mod n.
  la a0, tpr_nege
  la a1, tpr_rinv
  la a2, tpr_u1
  jal ra, secf_mul_mod_n
  addi a0, s4, 64             # s ptr (ABI+64)
  la a1, tpr_rinv
  la a2, tpr_u2
  jal ra, secf_mul_mod_n
  # 6. Q = u1*G + u2*R.
  la a0, tpr_u1
  la a1, secp256k1_generator
  la a2, tpr_p1
  jal ra, secp256k1_scalar_mul
  la a0, tpr_u2
  la a1, tpr_R
  la a2, tpr_p2
  jal ra, secp256k1_scalar_mul
  la a0, tpr_p1
  la a1, tpr_p2
  mv a2, s3                   # recovered pubkey out (x || y)
  jal ra, secp256k1_point_add
  bnez a0, .Ltprr_recover_fail   # identity result => invalid recovery
  j .Ltprr_staged_ok
.Ltprr_recover_fail:
  # zero the 64-byte output so callers never see partial coordinates
  mv t1, s3
  li t2, 8
.Ltprr_zero_out:
  sd zero, 0(t1)
  addi t1, t1, 8; addi t2, t2, -1
  bnez t2, .Ltprr_zero_out
  li a0, 60
  j .Ltprr_staged_ret
.Ltprr_staged_ok:
  li a0, 0
.Ltprr_staged_ret:
  ld ra,  0(sp)
  ld s3,  8(sp); ld s4, 16(sp)
  addi sp, sp, 24
  ret
