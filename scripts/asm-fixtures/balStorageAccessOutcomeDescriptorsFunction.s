bal_storage_access_outcome_descriptors:
  addi sp, sp, -128
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # outcome table
  mv s1, a1                   # outcome count
  mv s2, a2                   # committed window table
  mv s3, a3                   # committed window count
  mv s4, a4                   # account token
  mv s5, a5                   # descriptor out base
  mv s6, a6                   # path cursor
  mv s7, a7                   # out_count ptr
  sd zero, 0(s7)
  li s8, 0                    # window index
  li s9, 0                    # emitted descriptor count
.Lbsaod_window_loop:
  beq s8, s3, .Lbsaod_ok
  slli t0, s8, 5
  add s10, s2, t0             # current window
  ld t1, 0(s10)               # window status
  beqz t1, .Lbsaod_next_window
  li t2, 1
  bne t1, t2, .Lbsaod_fail
  ld t3, 8(s10)               # start index
  ld t4, 16(s10)              # count
  add t5, t3, t4              # exclusive end
  bltu t5, t3, .Lbsaod_fail
  bgtu t5, s1, .Lbsaod_fail
  sd t5, 104(sp)              # caller-saved across hash helpers
  mv s11, t3                  # outcome index
.Lbsaod_outcome_loop:
  ld t5, 104(sp)
  beq s11, t5, .Lbsaod_next_window
  slli t0, s11, 6
  slli t1, s11, 5
  add t0, t0, t1
  add s10, s0, t0             # current outcome
  ld t1, 64(s10)              # status
  li t2, 1
  bgtu t1, t2, .Lbsaod_next_outcome
  # Keep only rows for the requested account token.
  mv t0, s10
  mv t1, s4
  li t2, 0
.Lbsaod_account_cmp:
  li t3, 32
  beq t2, t3, .Lbsaod_emit
  add t4, t0, t2
  add t6, t1, t2
  lbu t4, 0(t4)
  lbu t6, 0(t6)
  bne t4, t6, .Lbsaod_next_outcome
  addi t2, t2, 1
  j .Lbsaod_account_cmp
.Lbsaod_emit:
  addi a0, s10, 32
  li a1, 32
  la a2, bsaod_hash
  jal ra, zkvm_keccak256
  la a0, bsaod_hash
  li a1, 32
  mv a2, s6
  jal ra, bytes_to_nibbles
  # Skip duplicate committed observations by comparing against emitted paths.
  li t0, 0
.Lbsaod_emitted_dup_scan:
  beq t0, s9, .Lbsaod_write_descriptor
  sub t1, s9, t0
  slli t1, t1, 6
  sub t2, s6, t1             # path for emitted row t0
  li t3, 0
.Lbsaod_emitted_dup_cmp:
  li t4, 64
  beq t3, t4, .Lbsaod_next_outcome
  add t5, t2, t3
  add t6, s6, t3
  lbu t5, 0(t5)
  lbu t6, 0(t6)
  bne t5, t6, .Lbsaod_emitted_dup_next
  addi t3, t3, 1
  j .Lbsaod_emitted_dup_cmp
.Lbsaod_emitted_dup_next:
  addi t0, t0, 1
  j .Lbsaod_emitted_dup_scan
.Lbsaod_write_descriptor:
  slli t0, s9, 5
  slli t1, s9, 3
  add t0, t0, t1
  add t0, s5, t0              # descriptor[out]
  sd s6, 0(t0)
  li t1, 64
  sd t1, 8(t0)
  la t1, bsaod_empty_value
  sd t1, 16(t0)
  sd zero, 24(t0)
  li t1, 3
  sd t1, 32(t0)
  addi s6, s6, 64
  addi s9, s9, 1
  sd s9, 0(s7)
.Lbsaod_next_outcome:
  addi s11, s11, 1
  j .Lbsaod_outcome_loop
.Lbsaod_next_window:
  addi s8, s8, 1
  j .Lbsaod_window_loop
.Lbsaod_ok:
  li a0, 0
  j .Lbsaod_ret
.Lbsaod_fail:
  li a0, 1
.Lbsaod_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 128
  ret
