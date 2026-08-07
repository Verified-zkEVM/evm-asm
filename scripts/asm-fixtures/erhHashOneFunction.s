erh_hash_one:
  addi sp, sp, -16
  sd ra, 0(sp)
  la t0, erh_blob; sb a4, 0(t0)
  addi t1, t0, 1; mv t2, a3; mv t3, s10
.Lerh_copy:
  beqz t3, .Lerh_hash
  lbu t4, 0(t2); sb t4, 0(t1)
  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lerh_copy
.Lerh_hash:
  la a0, erh_blob; addi a1, s10, 1; mv a2, s8; jal ra, zkvm_sha256
  ld ra, 0(sp); addi sp, sp, 16; ret
