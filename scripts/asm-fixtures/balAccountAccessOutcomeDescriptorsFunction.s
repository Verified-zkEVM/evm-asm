bal_account_access_outcome_descriptors:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)
  mv s0, a0                   # outcome table
  mv s1, a1                   # outcome count
  mv s2, a2                   # changed account table
  mv s3, a3                   # changed account count
  mv s4, a4                   # descriptor out base
  mv s5, a5                   # path cursor
  mv s6, a6                   # out_count ptr
  sd zero, 0(s6)
  li s7, 0                    # outcome index
  li s8, 0                    # emitted descriptor count
.Lbaaod_loop:
  beq s7, s1, .Lbaaod_ok
  slli t0, s7, 6
  add s9, s0, t0              # current outcome ptr
  ld t1, 32(s9)               # status
  li t2, 2
  bgtu t1, t2, .Lbaaod_fail
  # Skip if this address already has a state-changing BAL descriptor.
  li s10, 0
.Lbaaod_changed_scan:
  beq s10, s3, .Lbaaod_dup_scan_start
  slli t0, s10, 5
  add t0, s2, t0
  mv t1, s9
  li t2, 0
.Lbaaod_changed_cmp:
  li t3, 20
  beq t2, t3, .Lbaaod_next
  add t4, t0, t2
  add t5, t1, t2
  lbu t4, 0(t4)
  lbu t5, 0(t5)
  bne t4, t5, .Lbaaod_changed_next
  addi t2, t2, 1
  j .Lbaaod_changed_cmp
.Lbaaod_changed_next:
  addi s10, s10, 1
  j .Lbaaod_changed_scan
  # Skip duplicate outcome addresses; the first read observation is enough.
.Lbaaod_dup_scan_start:
  li s10, 0
.Lbaaod_dup_scan:
  beq s10, s7, .Lbaaod_emit
  slli t0, s10, 6
  add t0, s0, t0
  mv t1, s9
  li t2, 0
.Lbaaod_dup_cmp:
  li t3, 20
  beq t2, t3, .Lbaaod_next
  add t4, t0, t2
  add t5, t1, t2
  lbu t4, 0(t4)
  lbu t5, 0(t5)
  bne t4, t5, .Lbaaod_dup_next
  addi t2, t2, 1
  j .Lbaaod_dup_cmp
.Lbaaod_dup_next:
  addi s10, s10, 1
  j .Lbaaod_dup_scan
.Lbaaod_emit:
  mv a0, s9
  li a1, 20
  la a2, baaod_hash
  jal ra, zkvm_keccak256
  la a0, baaod_hash
  li a1, 32
  mv a2, s5
  jal ra, bytes_to_nibbles
  slli t0, s8, 5
  slli t1, s8, 3
  add t0, t0, t1
  add t0, s4, t0              # descriptor[out]
  sd s5, 0(t0)
  li t1, 64
  sd t1, 8(t0)
  la t1, baaod_empty_account
  sd t1, 16(t0)
  li t1, 70
  sd t1, 24(t0)
  li t1, 3
  sd t1, 32(t0)
  addi s5, s5, 64
  addi s8, s8, 1
  sd s8, 0(s6)
.Lbaaod_next:
  addi s7, s7, 1
  j .Lbaaod_loop
.Lbaaod_ok:
  li a0, 0
  j .Lbaaod_ret
.Lbaaod_fail:
  li a0, 1
.Lbaaod_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)
  addi sp, sp, 112
  ret
