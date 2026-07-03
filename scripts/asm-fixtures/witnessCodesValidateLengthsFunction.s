witness_codes_validate_lengths:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section_len
  mv s2, a2                  # max_byte_length
  mv s3, a3                  # n_processed out
  mv s4, a4                  # first_bad_index out
  sd zero, 0(s3)
  li t0, -1
  sd t0, 0(s4)
  beqz s1, .Lwcvl_ok           # empty section ⇒ vacuous-valid
  lwu t0, 0(s0)
  srli s5, t0, 2               # s5 = N
  li s6, 0                     # s6 = i
.Lwcvl_loop:
  beq s6, s5, .Lwcvl_ok
  # Element i bounds.
  slli t0, s6, 2
  add t1, s0, t0
  lwu t2, 0(t1)                # inner_off_i
  addi t3, s6, 1
  beq t3, s5, .Lwcvl_use_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)                # inner_off_{i+1}
  sub t5, t4, t2               # el_i_len
  j .Lwcvl_check
.Lwcvl_use_end:
  sub t5, s1, t2               # el_i_len = section_len - inner_off_i
.Lwcvl_check:
  bgtu t5, s2, .Lwcvl_too_long
  addi s6, s6, 1
  j .Lwcvl_loop
.Lwcvl_too_long:
  sd s6, 0(s3)                 # n_processed = i
  sd s6, 0(s4)                 # first_bad_index = i
  li a0, 1
  j .Lwcvl_ret
.Lwcvl_ok:
  sd s5, 0(s3)                 # n_processed = N
  li t0, -1
  sd t0, 0(s4)
  li a0, 0
.Lwcvl_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
