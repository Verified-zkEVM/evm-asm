execution_requests_hash:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)
  mv s0, a0                   # SszExecutionRequests section
  mv s1, a1                   # section length
  mv s2, a2                   # output hash
  li t0, 20; bltu s1, t0, .Lerh_fail
  mv a0, s0; jal ra, bgv_u32le; mv s3, a0
  addi a0, s0, 4; jal ra, bgv_u32le; mv s4, a0
  addi a0, s0, 8; jal ra, bgv_u32le; mv s5, a0
  addi a0, s0, 12; jal ra, bgv_u32le; mv s6, a0
  addi a0, s0, 16; jal ra, bgv_u32le; mv s7, a0
  li t0, 20; bne s3, t0, .Lerh_fail
  bltu s4, s3, .Lerh_fail
  bltu s5, s4, .Lerh_fail
  bltu s6, s5, .Lerh_fail
  bltu s7, s6, .Lerh_fail
  bltu s1, s7, .Lerh_fail
  sub t0, s4, s3; li t1, 192; remu t2, t0, t1; bnez t2, .Lerh_fail
  divu t2, t0, t1; li t3, 8192; bgtu t2, t3, .Lerh_fail
  sub t0, s5, s4; li t1, 76;  remu t2, t0, t1; bnez t2, .Lerh_fail
  divu t2, t0, t1; li t3, 16;   bgtu t2, t3, .Lerh_fail
  sub t0, s6, s5; li t1, 116; remu t2, t0, t1; bnez t2, .Lerh_fail
  divu t2, t0, t1; li t3, 2;    bgtu t2, t3, .Lerh_fail
  sub t0, s7, s6; li t1, 184; remu t2, t0, t1; bnez t2, .Lerh_fail
  divu t2, t0, t1; li t3, 64;   bgtu t2, t3, .Lerh_fail
  sub t0, s1, s7; li t1, 68; remu t2, t0, t1; bnez t2, .Lerh_fail
  divu t2, t0, t1; li t3, 16;   bgtu t2, t3, .Lerh_fail
  la s8, erh_digests          # next digest output
  li s9, 0                    # digest count
  # deposits: type 0x00, body [s3,s4)
  sub s10, s4, s3; beqz s10, .Lerh_withdrawals
  add a3, s0, s3; li a4, 0; jal ra, erh_hash_one
  addi s8, s8, 32; addi s9, s9, 1
.Lerh_withdrawals:
  sub s10, s5, s4; beqz s10, .Lerh_consolidations
  add a3, s0, s4; li a4, 1; jal ra, erh_hash_one
  addi s8, s8, 32; addi s9, s9, 1
.Lerh_consolidations:
  sub s10, s6, s5; beqz s10, .Lerh_builder_deposits
  add a3, s0, s5; li a4, 2; jal ra, erh_hash_one
  addi s8, s8, 32; addi s9, s9, 1
.Lerh_builder_deposits:
  sub s10, s7, s6; beqz s10, .Lerh_builder_exits
  add a3, s0, s6; li a4, 3; jal ra, erh_hash_one
  addi s8, s8, 32; addi s9, s9, 1
.Lerh_builder_exits:
  sub s10, s1, s7; beqz s10, .Lerh_final
  add a3, s0, s7; li a4, 4; jal ra, erh_hash_one
  addi s8, s8, 32; addi s9, s9, 1
.Lerh_final:
  la a0, erh_digests; slli a1, s9, 5; mv a2, s2; jal ra, zkvm_sha256
  li a0, 0; j .Lerh_ret
.Lerh_fail:
  li a0, 1
.Lerh_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)
  addi sp, sp, 96
  ret
