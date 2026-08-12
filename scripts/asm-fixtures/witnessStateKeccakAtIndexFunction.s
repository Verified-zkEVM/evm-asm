witness_state_keccak_at_index:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section_len
  mv s2, a2                  # index
  mv s3, a3                  # out buf ptr (32 B)
  # Zero out_buf so OOB callers get a deterministic zero.
  sd zero,  0(s3); sd zero,  8(s3)
  sd zero, 16(s3); sd zero, 24(s3)
  beqz s1, .Lwski_oob        # empty section ⇒ any index is OOB
  lwu t0, 0(s0)              # first inner offset = 4 * N
  srli s4, t0, 2             # s4 = N
  bgeu s2, s4, .Lwski_oob    # index >= N ⇒ OOB
  # Compute element i bounds.
  slli t0, s2, 2             # 4*i
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  add a0, s0, t2             # el_i_start
  addi t3, s2, 1
  beq t3, s4, .Lwski_use_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4             # el_i_end
  j .Lwski_have_end
.Lwski_use_end:
  add t4, s0, s1             # el_i_end = section_end
.Lwski_have_end:
  sub a1, t4, a0             # el_i_len
  mv a2, s3                  # out buf
  jal ra, zkvm_keccak256
  li a0, 0
  j .Lwski_ret
.Lwski_oob:
  li a0, 1
.Lwski_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 48
  ret
