u256_mul_u64_be:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                  # a ptr
  mv s1, a1                  # b
  mv s2, a2                  # out ptr
  # Zero 40-byte accumulator.
  la s3, u256m_acc
  mv t0, s3
  li t1, 5
.Lmul_zinit:
  beqz t1, .Lmul_zdone
  sd zero, 0(t0)
  addi t0, t0, 8
  addi t1, t1, -1
  j .Lmul_zinit
.Lmul_zdone:
  # Outer loop: p in 0..32 (byte position from LSB).
  li s4, 0
.Lmul_outer:
  li t0, 32
  beq s4, t0, .Lmul_post
  # byte_a = a[31 - p]
  li t0, 31
  sub t0, t0, s4
  add t0, s0, t0
  lbu t0, 0(t0)
  beqz t0, .Lmul_step        # skip zero bytes (optimization)
  # partial = byte_a * b: low 64 in t1, high ≤ 0xff in t2.
  mul   t1, t0, s1
  mulhu t2, t0, s1
  # Add to acc[p..p+9] with carry.
  add t3, s3, s4             # &acc[p]
  li t4, 8                   # 8 low bytes
  li t5, 0                   # carry
.Lmul_addlo:
  lbu t6, 0(t3)
  andi a3, t1, 0xff
  add  t6, t6, a3
  add  t6, t6, t5
  andi a3, t6, 0xff
  sb   a3, 0(t3)
  srli t5, t6, 8
  srli t1, t1, 8
  addi t3, t3, 1
  addi t4, t4, -1
  bnez t4, .Lmul_addlo
  # Add p_hi (t2; ≤ 1 byte) + carry at acc[p+8].
  lbu t6, 0(t3)
  add t6, t6, t2
  add t6, t6, t5
  andi a3, t6, 0xff
  sb   a3, 0(t3)
  srli t5, t6, 8
  addi t3, t3, 1
  # Propagate remaining carry through higher bytes.
.Lmul_carry:
  beqz t5, .Lmul_step
  lbu t6, 0(t3)
  add t6, t6, t5
  andi a3, t6, 0xff
  sb   a3, 0(t3)
  srli t5, t6, 8
  addi t3, t3, 1
  j .Lmul_carry
.Lmul_step:
  addi s4, s4, 1
  j .Lmul_outer
.Lmul_post:
  # Copy acc[0..32] (LSB first) into out (BE, MSB first).
  mv t0, s3                  # acc cursor (LSB)
  addi t1, s2, 32            # out end (exclusive)
  li t2, 32
.Lmul_copy:
  beqz t2, .Lmul_overflow_check
  addi t1, t1, -1
  lbu t3, 0(t0)
  sb t3, 0(t1)
  addi t0, t0, 1
  addi t2, t2, -1
  j .Lmul_copy
.Lmul_overflow_check:
  # t0 now points to acc[32]; any nonzero in acc[32..40] → overflow.
  li t1, 8
  li a0, 0
.Lmul_of_loop:
  beqz t1, .Lmul_done
  lbu t3, 0(t0)
  beqz t3, .Lmul_of_next
  li a0, 1
  j .Lmul_done
.Lmul_of_next:
  addi t0, t0, 1
  addi t1, t1, -1
  j .Lmul_of_loop
.Lmul_done:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
