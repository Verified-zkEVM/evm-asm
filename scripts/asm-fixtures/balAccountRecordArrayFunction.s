bal_account_record_array:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a0                   # root hash ptr
  mv s1, a1                   # witness ptr
  mv s2, a2                   # witness len
  mv s3, a3                   # BAL list ptr
  mv s4, a4                   # BAL list len
  mv s5, a5                   # n
  mv s6, a6                   # records out base
  mv s7, a7                   # account arena cursor
  add t0, s3, s4              # BAL end
  la t1, bara_bal_end; sd t0, 0(t1)
  bgeu s3, t0, .Lbara_fail
  lbu t2, 0(s3); li t3, 0xc0; bltu t2, t3, .Lbara_fail
  li t3, 0xf8; bltu t2, t3, .Lbara_short_outer
  li t3, 0xf7; sub t4, t2, t3; addi t4, t4, 1; add s9, s3, t4; j .Lbara_have_cursor
.Lbara_short_outer:
  addi s9, s3, 1
.Lbara_have_cursor:
  li s8, 0                    # i
.Lbara_loop:
  beq s8, s5, .Lbara_ok
  la t0, bara_bal_end; ld t0, 0(t0); bgeu s9, t0, .Lbara_fail
  mv a0, s9; jal ra, rlp_item_size; mv t6, a0
  add t0, s9, t6; la t1, bara_bal_end; ld t1, 0(t1); bgtu t0, t1, .Lbara_fail
  la t1, bara_next_item; sd t0, 0(t1)
  la t1, bara_item_len; sd t6, 0(t1)
  mv a0, s9; mv a1, t6
  jal ra, bal_account_has_state_change
  li t0, 1; beq a0, t0, .Lbara_changed
  bnez a0, .Lbara_fail
  la s9, bara_empty_account; li t1, 70; li t2, 3; j .Lbara_record
.Lbara_changed:
.Lbara_walk_changed:
  mv a0, s9; la t0, bara_item_len; ld a1, 0(t0)
  la a2, bara_path
  jal ra, bal_account_path
  bnez a0, .Lbara_fail
  mv a0, s0; mv a1, s1; mv a2, s2; la a3, bara_path; li a4, 64
  la a5, bara_acct; la a6, bara_acct_len
  jal ra, mpt_walk
  beqz a0, .Lbara_found
  li t0, 1; bne a0, t0, .Lbara_fail
  la s9, bara_empty_account
  li t1, 70
  li t2, 1                    # is_insert
  j .Lbara_record
.Lbara_found:
  la s9, bara_acct
  la t0, bara_acct_len; ld t1, 0(t0)
  li t0, 256; bgtu t1, t0, .Lbara_fail
  li t2, 0                    # modify existing
  j .Lbara_record
.Lbara_record:
  mv a0, s7; mv a1, s9; mv a2, t1
  jal ra, mset_memcpy
  slli t0, s8, 4; slli t3, s8, 3; add t0, t0, t3; add t0, s6, t0
  sd s7, 0(t0); sd t1, 8(t0); sd t2, 16(t0)
  add s7, s7, t1; addi s7, s7, 7; andi s7, s7, -8
  la t0, bara_next_item; ld s9, 0(t0)
  addi s8, s8, 1
  j .Lbara_loop
.Lbara_ok:
  li a0, 0
  j .Lbara_ret
.Lbara_fail:
  li a0, 1
.Lbara_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 112
  ret
