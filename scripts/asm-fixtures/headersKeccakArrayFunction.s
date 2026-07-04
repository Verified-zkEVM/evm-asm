headers_keccak_array:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                  # s0 = section ptr
  mv s1, a1                  # s1 = section_len
  mv s2, a2                  # s2 = table base
  beqz s1, .Lhka_n0
  lwu t0, 0(s0)
  srli s3, t0, 2             # s3 = N
  li s4, 0                   # s4 = i
.Lhka_loop:
  beq s4, s3, .Lhka_done
  slli t0, s4, 2             # 4*i
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  add a0, s0, t2             # el_i_start
  addi t3, s4, 1
  beq t3, s3, .Lhka_use_end
  slli t3, t3, 2             # 4*(i+1)
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4             # el_i_end
  j .Lhka_have_end
.Lhka_use_end:
  add t4, s0, s1             # el_i_end = section_end
.Lhka_have_end:
  sub a1, t4, a0             # el_i_len
  slli t0, s4, 5             # 32*i
  add a2, s2, t0             # a2 = &table[i]
  jal ra, zkvm_keccak256
  addi s4, s4, 1
  j .Lhka_loop
.Lhka_n0:
  li s3, 0
.Lhka_done:
  mv a0, s3                  # return N
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
