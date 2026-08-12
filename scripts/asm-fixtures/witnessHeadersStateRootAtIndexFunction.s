witness_headers_state_root_at_index:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section_len
  mv s2, a2                  # index
  mv s3, a3                  # out buf (32 B)
  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)
  beqz s1, .Lwhsr_oob
  lwu t0, 0(s0)
  srli s4, t0, 2             # s4 = N
  bgeu s2, s4, .Lwhsr_oob
  # Compute element i bounds.
  slli t0, s2, 2
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  add s5, s0, t2             # el_i_start
  addi t3, s2, 1
  beq t3, s4, .Lwhsr_use_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4
  j .Lwhsr_have_end
.Lwhsr_use_end:
  add t4, s0, s1
.Lwhsr_have_end:
  sub s6, t4, s5             # el_i_len
  mv a0, s5
  mv a1, s6
  mv a2, s3                  # output buffer
  jal ra, header_extract_state_root
  # header_extract_state_root: 0=ok, 1=parse fail, 2=size fail.
  beqz a0, .Lwhsr_ret
  # Remap K201 1->2 and 2->3 to leave 1 for OOB.
  addi a0, a0, 1
  j .Lwhsr_ret
.Lwhsr_oob:
  li a0, 1
.Lwhsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
