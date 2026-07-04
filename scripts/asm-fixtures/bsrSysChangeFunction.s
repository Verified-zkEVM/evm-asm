bsr_sys_change:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  # keccak(addr, 20) -> bsr_kbuf
  mv a0, s0; li a1, 20; la a2, bsr_kbuf; jal ra, zkvm_keccak256
  # path = bsr_paths + 64*index; bytes_to_nibbles(bsr_kbuf, 32, path)
  slli t0, s4, 6; la t1, bsr_paths; add t2, t1, t0
  la t3, bsr_pathp; sd t2, 0(t3)              # stash path ptr
  la a0, bsr_kbuf; li a1, 32; mv a2, t2; jal ra, bytes_to_nibbles
  # mpt_walk(root, witness, wlen, path, 64, bsr_acct, bsr_acct_len)
  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)
  la t0, bsr_pathp; ld a3, 0(t0); li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len
  jal ra, mpt_walk
  bnez a0, .Lbsc_fail
  # account_apply_storage_slot_acc(acct, len, slot, val, vlen, newacct, bsr_tmplen)
  # The accumulator helper replays non-empty system-contract storage roots.
  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)
  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)
  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); mv a2, s1; mv a3, s2; mv a4, s3
  slli t0, s4, 7; la t1, bsr_newaccts; add a5, t1, t0; la a6, bsr_tmplen
  jal ra, account_apply_storage_slot_acc
  bnez a0, .Lbsc_fail
  # record change[index] = (path, 64, newacct, tmplen, is_insert=0) -- 40 B
  slli t0, s4, 5; slli t4, s4, 3; add t0, t0, t4; la t1, bsr_changes; add t1, t1, t0
  la t2, bsr_pathp; ld t2, 0(t2); sd t2, 0(t1); li t3, 64; sd t3, 8(t1)
  slli t0, s4, 7; la t2, bsr_newaccts; add t2, t2, t0; sd t2, 16(t1)
  la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1)
  sd zero, 32(t1)             # is_insert = 0 (system contract MODIFY)
  li a0, 0; j .Lbsc_ret
.Lbsc_fail:
  li a0, 1
.Lbsc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
