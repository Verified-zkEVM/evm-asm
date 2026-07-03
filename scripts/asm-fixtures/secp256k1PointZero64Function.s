secp256k1_point_zero64:
  li t0, 64
.Lsecc_zero64_loop:
  beqz t0, .Lsecc_zero64_ret
  sb zero, 0(a0)
  addi a0, a0, 1
  addi t0, t0, -1
  j .Lsecc_zero64_loop
.Lsecc_zero64_ret:
  ret
