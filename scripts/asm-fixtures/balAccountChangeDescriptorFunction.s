bal_account_change_descriptor:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a4                   # is_insert
  mv s1, a5                   # descriptor out
  mv s2, a6                   # path out
  mv s3, a7                   # value out
  mv s4, a0                   # account ptr
  mv s5, a1                   # account len
  mv s6, a2                   # AccountChanges ptr
  mv s7, a3                   # AccountChanges len
  la t0, baacd_fail_code; sd zero, 0(t0)
  la t0, baap_force_storage_clear; sd zero, 0(t0)
  li t1, 4; bne s0, t1, .Lbaacd_mode_ready
  li s0, 0                    # legacy post-wipe marker: state-trie MODIFY
.Lbaacd_mode_ready:
  mv a0, s4; mv a1, s5; mv a2, s6; mv a3, s7
  mv a4, s2; mv a5, s3; la a6, baacd_value_len
  jal ra, bal_account_change_value
  bnez a0, .Lbaacd_fail_value
  mv a0, s3; la t0, baacd_value_len; ld a1, 0(t0); la a2, baacd_is_empty
  jal ra, account_is_eip161_empty
  bnez a0, .Lbaacd_fail_value
  la t0, baacd_is_empty; ld t0, 0(t0); beqz t0, .Lbaacd_have_mode
  beqz s0, .Lbaacd_delete_empty
  li s0, 3                    # absent account remained empty: no-op
  j .Lbaacd_have_mode
.Lbaacd_delete_empty:
  li s0, 2                    # existing account became empty: delete leaf
.Lbaacd_have_mode:
  sd s2, 0(s1)
  li t0, 64; sd t0, 8(s1)
  sd s3, 16(s1)
  la t0, baacd_value_len; ld t0, 0(t0); sd t0, 24(s1)
  sd s0, 32(s1)
  li a0, 0
  j .Lbaacd_ret
.Lbaacd_fail_value:
  li t0, 301; la t1, baacd_fail_code; sd t0, 0(t1)
.Lbaacd_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 96
  ret
