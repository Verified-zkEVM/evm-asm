bsr_apply_modeled_system_post_fields:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # AccountChanges ptr
  mv s1, a1                   # AccountChanges len
  mv s2, a2                   # system descriptor index
  mv a0, s0; mv a1, s1; la a2, baap_bal; la a3, baap_bal_len; la a4, baap_nonce; la a5, baap_nonce_len
  jal ra, bal_account_post_fields
  bnez a0, .Lbams_pf_fail
  slli t0, s2, 5; slli t1, s2, 3; add t0, t0, t1; la t1, bsr_changes; add s5, t1, t0
  ld s3, 16(s5)               # current account value ptr
  ld s4, 24(s5)               # current account value len
  la t0, baap_nonce_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbams_pf_balance
  mv a0, s3; mv a1, s4; li a2, 0; la a3, baap_nonce; mv a4, t0; la a5, baap_tmp; la a6, baap_tmp_len
  jal ra, account_set_uint_field
  bnez a0, .Lbams_pf_fail
  la s3, baap_tmp; la t0, baap_tmp_len; ld s4, 0(t0)
.Lbams_pf_balance:
  la t0, baap_bal_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbams_pf_copy
  mv a0, s3; mv a1, s4; li a2, 1; la a3, baap_bal; mv a4, t0; la a5, baap_tmp2; la a6, baap_tmp2_len
  jal ra, account_set_uint_field
  bnez a0, .Lbams_pf_fail
  la s3, baap_tmp2; la t0, baap_tmp2_len; ld s4, 0(t0)
.Lbams_pf_copy:
  ld a0, 16(s5); mv a1, s3; mv a2, s4
  jal ra, mset_memcpy
  sd s4, 24(s5)
  li a0, 0; j .Lbams_pf_ret
.Lbams_pf_fail:
  li a0, 1
.Lbams_pf_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
