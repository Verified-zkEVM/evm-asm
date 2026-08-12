witness_state_validate_node_kinds:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section_len
  mv s2, a2                  # n_processed out
  mv s3, a3                  # first_bad_index out
  sd zero, 0(s2)
  li t0, -1
  sd t0, 0(s3)
  beqz s1, .Lwsvn_ok           # empty section ⇒ vacuous-valid
  lwu t0, 0(s0)
  srli s4, t0, 2               # s4 = N
  li s5, 0                     # s5 = i
.Lwsvn_loop:
  beq s5, s4, .Lwsvn_ok
  # Element i bounds.
  slli t0, s5, 2
  add t1, s0, t0
  lwu t2, 0(t1)                # inner_off_i
  add a0, s0, t2               # el_i_start
  addi t3, s5, 1
  beq t3, s4, .Lwsvn_use_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4               # el_i_end
  j .Lwsvn_have_end
.Lwsvn_use_end:
  add t4, s0, s1
.Lwsvn_have_end:
  sub a1, t4, a0               # el_i_len
  jal ra, mpt_node_kind
  li t0, 3
  beq a0, t0, .Lwsvn_parse_fail
  addi s5, s5, 1
  j .Lwsvn_loop
.Lwsvn_parse_fail:
  sd s5, 0(s2)                 # n_processed = i
  sd s5, 0(s3)                 # first_bad_index = i
  li a0, 1
  j .Lwsvn_ret
.Lwsvn_ok:
  sd s4, 0(s2)                 # n_processed = N (full)
  li t0, -1
  sd t0, 0(s3)                 # first_bad_index = -1
  li a0, 0
.Lwsvn_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
