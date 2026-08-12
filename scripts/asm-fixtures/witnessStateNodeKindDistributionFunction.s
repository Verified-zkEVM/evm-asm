witness_state_node_kind_distribution:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section_len
  mv s2, a2                  # out buffer ptr
  # Zero the 32-byte output buffer.
  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)
  beqz s1, .Lwsnd_done       # empty section -> all counts 0
  # First inner offset (=4*N) gives N.
  lwu t0, 0(s0)
  srli s3, t0, 2             # s3 = N
  li s4, 0                   # s4 = i = current index
.Lwsnd_loop:
  beq s4, s3, .Lwsnd_done
  # Compute element i bounds.
  slli t0, s4, 2             # 4*i
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  add s5, s0, t2             # el_i_start  (preserve across K22 call)
  addi t3, s4, 1
  beq t3, s3, .Lwsnd_use_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4             # el_i_end
  j .Lwsnd_have_end
.Lwsnd_use_end:
  add t4, s0, s1             # el_i_end = section_end
.Lwsnd_have_end:
  sub s6, t4, s5             # el_i_len   (preserve across K22 call)
  mv a0, s5
  mv a1, s6
  jal ra, mpt_node_kind
  # a0 is 0/1/2/3 -- increment count[a0].
  slli t0, a0, 3             # a0 * 8
  add t1, s2, t0
  ld t2, 0(t1)
  addi t2, t2, 1
  sd t2, 0(t1)
  addi s4, s4, 1
  j .Lwsnd_loop
.Lwsnd_done:
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
