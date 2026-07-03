mpt_state_root_ins:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a1                   # witness
  mv s1, a2                   # witness_len
  mv s2, a3                   # changes
  mv s3, a4                   # n_changes
  mv s4, a5                   # out_root
  # current root := root_hash (a0) -> mset_dr_root
  la t0, mset_dr_root
  ld t1,  0(a0); sd t1,  0(t0)
  ld t1,  8(a0); sd t1,  8(t0)
  ld t1, 16(a0); sd t1, 16(t0)
  ld t1, 24(a0); sd t1, 24(t0)
  # init the node DB (shared by mpt_set_acc + mpt_insert_acc)
  la t0, mset_db_count; sd zero, 0(t0)
  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)
  jal ra, mpt_resolve_cache_reset
  la t0, sri_fail_index; sd zero, 0(t0)
  la t0, sri_fail_mode; sd zero, 0(t0)
  la t0, sri_fail_status; sd zero, 0(t0)
  li s5, 0                    # i
.Lsri_loop:
  beq s5, s3, .Lsri_done
  slli t0, s5, 5; slli t1, s5, 3; add t0, t0, t1   # 40 * i
  add t0, s2, t0              # &change[i]
  ld a3, 0(t0)                # path_ptr
  ld a4, 8(t0)                # path_len
  ld a5, 16(t0)               # value_ptr
  ld a6, 24(t0)               # value_len
  ld t2, 32(t0)               # mode: 0=set, 1=insert, 2=delete, 3=noop
  la t3, sri_cur_mode; sd t2, 0(t3)
  la a0, mset_dr_root
  mv a1, s0
  mv a2, s1
  la a7, mset_dr_root
  li t3, 3; beq t2, t3, .Lsri_noop
  li t3, 2; beq t2, t3, .Lsri_delete
  beqz t2, .Lsri_modify
  jal ra, mpt_insert_acc
  j .Lsri_after
.Lsri_delete:
  jal ra, mpt_delete_acc
  j .Lsri_after
.Lsri_modify:
  jal ra, mpt_set_acc
  j .Lsri_after
.Lsri_noop:
  li a0, 0
.Lsri_after:
  bnez a0, .Lsri_fail
  addi s5, s5, 1
  j .Lsri_loop
.Lsri_done:
  la t0, mset_dr_root
  ld t1,  0(t0); sd t1,  0(s4)
  ld t1,  8(t0); sd t1,  8(s4)
  ld t1, 16(t0); sd t1, 16(s4)
  ld t1, 24(t0); sd t1, 24(s4)
  li a0, 0
.Lsri_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
.Lsri_fail:
  la t0, sri_fail_index; sd s5, 0(t0)
  la t0, sri_cur_mode; ld t1, 0(t0); la t0, sri_fail_mode; sd t1, 0(t0)
  la t0, sri_fail_status; sd a0, 0(t0)
  j .Lsri_ret
