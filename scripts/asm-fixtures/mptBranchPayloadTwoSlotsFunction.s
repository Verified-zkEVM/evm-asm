mpt_branch_payload_two_slots:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # idx_a
  mv s1, a1                   # bytes_a ptr
  mv s2, a2                   # len_a
  mv s3, a3                   # idx_b
  mv s4, a4                   # bytes_b ptr
  mv s5, a5                   # len_b
  # ---- Validate ----
  li t0, 17
  bgeu s0, t0, .Lmbpts_fail
  bgeu s3, t0, .Lmbpts_fail
  beq  s0, s3, .Lmbpts_fail
  # ---- Walk slot indices 0..16, emitting bytes ----
  mv t1, a6                   # output cursor
  li t2, 0                    # i
.Lmbpts_loop:
  li t0, 17
  bge t2, t0, .Lmbpts_done
  beq t2, s0, .Lmbpts_emit_a
  beq t2, s3, .Lmbpts_emit_b
  # Empty slot: write 0x80.
  li t3, 0x80
  sb t3, 0(t1)
  addi t1, t1, 1
  j .Lmbpts_next
.Lmbpts_emit_a:
  # Copy len_a bytes from bytes_a to output.
  mv t3, s1
  mv t4, s2
.Lmbpts_cp_a:
  beqz t4, .Lmbpts_next
  lbu t5, 0(t3)
  sb t5, 0(t1)
  addi t3, t3, 1
  addi t1, t1, 1
  addi t4, t4, -1
  j .Lmbpts_cp_a
.Lmbpts_emit_b:
  mv t3, s4
  mv t4, s5
.Lmbpts_cp_b:
  beqz t4, .Lmbpts_next
  lbu t5, 0(t3)
  sb t5, 0(t1)
  addi t3, t3, 1
  addi t1, t1, 1
  addi t4, t4, -1
  j .Lmbpts_cp_b
.Lmbpts_next:
  addi t2, t2, 1
  j .Lmbpts_loop
.Lmbpts_done:
  # out_length = cursor - output_start.
  sub t1, t1, a6
  sd t1, 0(a7)
  li a0, 0
  j .Lmbpts_ret
.Lmbpts_fail:
  sd zero, 0(a7)
  li a0, 1
.Lmbpts_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
