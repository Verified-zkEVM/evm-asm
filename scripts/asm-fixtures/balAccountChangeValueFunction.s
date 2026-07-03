bal_account_change_value:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # account ptr
  mv s1, a1                   # account len
  mv s2, a2                   # AccountChanges ptr
  mv s3, a3                   # AccountChanges len
  mv s4, a4                   # out path ptr
  mv s5, a5                   # out account ptr
  mv s6, a6                   # out account len ptr
  la t0, bacv_fail_code; sd zero, 0(t0)
  mv a0, s2; mv a1, s3; mv a2, s4
  jal ra, bal_account_path
  bnez a0, .Lbacv_fail_path
  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s5; mv a5, s6
  jal ra, bal_account_apply_post_fields
  bnez a0, .Lbacv_fail_apply
  j .Lbacv_ret
.Lbacv_fail_path:
  li t0, 401; la t1, bacv_fail_code; sd t0, 0(t1)
  li a0, 1
  j .Lbacv_ret
.Lbacv_fail_apply:
  li t0, 402; la t1, bacv_fail_code; sd t0, 0(t1)
  li a0, 1
.Lbacv_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 80
  ret
