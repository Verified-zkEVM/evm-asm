block_access_list_hash:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # SSZ_BASE
  mv s1, a1                   # out hash
  addi s2, s0, 16             # NPR = SSZ_BASE + 16
  # exec_payload = NPR + 44
  addi t3, s2, 44             # exec_payload (kept in t3 across the u32 reads;
                              # bah_u32le clobbers only t0/t1)
  # bal_off = u32 @ exec_payload+528
  addi a0, t3, 528; jal ra, bah_u32le
  addi t3, s2, 44             # re-derive exec_payload (a0-call safe but cheap)
  add t4, t3, a0              # bal_start = exec_payload + bal_off
  la t0, bah_bal_start; sd t4, 0(t0)
  # vh_off = u32 @ NPR+4 ; bal_end = NPR + vh_off
  addi a0, s2, 4; jal ra, bah_u32le
  add t5, s2, a0              # bal_end = NPR + vh_off
  la t0, bah_bal_start; ld t4, 0(t0)
  sub a1, t5, t4              # bal_len = bal_end - bal_start
  mv a0, t4                   # bal_start
  mv a2, s1                   # out hash
  jal ra, zkvm_keccak256
  li a0, 0
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
