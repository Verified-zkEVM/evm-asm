headers_keccak_chain:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                  # s0 = section ptr
  mv s1, a1                  # s1 = section_len
  mv s2, a2                  # s2 = output ptr
  beqz s1, .Lhkc_n0          # empty section ⇒ N = 0
  lwu t0, 0(s0)              # offset_0 = 4 * N
  srli s3, t0, 2             # s3 = N
  li s4, 0                   # s4 = i
.Lhkc_loop:
  beq s4, s3, .Lhkc_done
  slli t0, s4, 2             # 4*i
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  add a0, s0, t2             # el_i_start
  addi t3, s4, 1
  beq t3, s3, .Lhkc_use_end
  slli t3, t3, 2             # 4*(i+1)
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4             # el_i_end
  j .Lhkc_have_end
.Lhkc_use_end:
  add t4, s0, s1             # el_i_end = section_end
.Lhkc_have_end:
  sub a1, t4, a0             # el_i_len
  mv a2, s2                  # output (overwritten each iter)
  jal ra, zkvm_keccak256
  addi s4, s4, 1
  j .Lhkc_loop
.Lhkc_n0:
  sd zero,  0(s2)
  sd zero,  8(s2)
  sd zero, 16(s2)
  sd zero, 24(s2)
  li s3, 0                   # N = 0
.Lhkc_done:
  mv a0, s3                  # return N
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
