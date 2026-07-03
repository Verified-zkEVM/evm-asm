secp256k1_point_copy64:
  li t0, 64
.Lsecc_copy64_loop:
  beqz t0, .Lsecc_copy64_ret
  lbu t1, 0(a0)
  sb t1, 0(a1)
  addi a0, a0, 1
  addi a1, a1, 1
  addi t0, t0, -1
  j .Lsecc_copy64_loop
.Lsecc_copy64_ret:
  ret
