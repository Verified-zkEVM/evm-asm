mpt_state_root:
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
  # init node DB
  la t0, mset_db_count; sd zero, 0(t0)
  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)
  jal ra, mpt_resolve_cache_reset
  li s5, 0                    # i
.Lsr_loop:
  beq s5, s3, .Lsr_done
  slli t0, s5, 5; add t0, s2, t0   # &change[i]
  ld a3, 0(t0)                # path_ptr
  ld a4, 8(t0)                # path_len
  ld a5, 16(t0)               # value_ptr
  ld a6, 24(t0)               # value_len
  la a0, mset_dr_root
  mv a1, s0
  mv a2, s1
  la a7, mset_dr_root
  jal ra, mpt_set_acc
  bnez a0, .Lsr_fail
  addi s5, s5, 1
  j .Lsr_loop
.Lsr_done:
  la t0, mset_dr_root
  ld t1,  0(t0); sd t1,  0(s4)
  ld t1,  8(t0); sd t1,  8(s4)
  ld t1, 16(t0); sd t1, 16(s4)
  ld t1, 24(t0); sd t1, 24(s4)
  li a0, 0
.Lsr_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
.Lsr_fail:
  j .Lsr_ret
