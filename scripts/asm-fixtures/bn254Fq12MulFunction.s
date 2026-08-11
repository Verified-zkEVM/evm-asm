bnq_mul:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0
  mv s1, a1
  mv s2, a2
  la t0, bnq_acc
  li t1, 92
.Lbnq_mul_zero:
  sd zero, 0(t0)
  addi t0, t0, 8
  addi t1, t1, -1
  bnez t1, .Lbnq_mul_zero
  li s3, 0                       # i
.Lbnq_mul_i:
  li s4, 0                       # j
.Lbnq_mul_j:
  slli t1, s3, 5
  add t1, s1, t1                 # &a[i]
  slli t2, s4, 5
  add t2, s2, t2                 # &b[j]
  add t3, s3, s4
  slli t3, t3, 5
  la t4, bnq_acc
  add t3, t4, t3                 # &acc[i+j]
  la t0, bnp_arith_params
  sd t1, 0(t0)
  sd t2, 8(t0)
  sd t3, 16(t0)
  la t1, bnf_le_p
  sd t1, 24(t0)
  sd t3, 32(t0)
  .4byte 0x8022a073              # acc[i+j] = a[i]*b[j] + acc[i+j]
  addi s4, s4, 1
  li t0, 12
  bne s4, t0, .Lbnq_mul_j
  addi s3, s3, 1
  li t0, 12
  bne s3, t0, .Lbnq_mul_i
  li s3, 22                      # k
.Lbnq_mul_red:
  la t4, bnq_acc
  slli t1, s3, 5
  add t1, t4, t1                 # &acc[k]
  addi t2, s3, -6
  slli t2, t2, 5
  add t2, t4, t2                 # &acc[k-6]
  la t0, bnp_arith_params
  sd t1, 0(t0)
  la t3, bnq_le_18
  sd t3, 8(t0)
  sd t2, 16(t0)
  la t3, bnf_le_p
  sd t3, 24(t0)
  sd t2, 32(t0)
  .4byte 0x8022a073              # acc[k-6] += 18*acc[k]
  addi t2, s3, -12
  slli t2, t2, 5
  add t2, t4, t2                 # &acc[k-12]
  la t0, bnp_arith_params
  sd t1, 0(t0)
  la t3, bnq_le_pm82
  sd t3, 8(t0)
  sd t2, 16(t0)
  la t3, bnf_le_p
  sd t3, 24(t0)
  sd t2, 32(t0)
  .4byte 0x8022a073              # acc[k-12] += (p-82)*acc[k]
  addi s3, s3, -1
  li t0, 11
  bne s3, t0, .Lbnq_mul_red
  la t0, bnq_acc
  mv t1, s0
  li t2, 48
.Lbnq_mul_copy:
  ld t3, 0(t0)
  sd t3, 0(t1)
  addi t0, t0, 8
  addi t1, t1, 8
  addi t2, t2, -1
  bnez t2, .Lbnq_mul_copy
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
