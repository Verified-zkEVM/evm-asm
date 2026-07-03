codes_blockhash_required_headers:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                  # witness.codes section ptr
  mv s1, a1                  # witness.codes section len
  mv s2, a2                  # max-required-headers out ptr
  li s5, 0                   # running max offset
  sd zero, 0(s2)
  beqz s1, .Lcbrh_ok
  lwu t0, 0(s0)
  srli s3, t0, 2             # N = first_offset / 4
  li s4, 0                   # code index
.Lcbrh_item_loop:
  beq s4, s3, .Lcbrh_ok
  slli t0, s4, 2
  add t1, s0, t0
  lwu t2, 0(t1)              # item start offset
  add s6, s0, t2             # item start ptr
  addi t3, s4, 1
  beq t3, s3, .Lcbrh_use_section_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)              # next item offset
  j .Lcbrh_have_end_off
.Lcbrh_use_section_end:
  mv t4, s1                  # last item ends at section_len
.Lcbrh_have_end_off:
  bltu t4, t2, .Lcbrh_fail
  sub s7, t4, t2             # remaining item bytes
  li t5, 5
  bltu s7, t5, .Lcbrh_next_item
.Lcbrh_scan_loop:
  li t5, 5
  bltu s7, t5, .Lcbrh_next_item
  lbu t0, 0(s6)
  li t1, 0x60
  beq t0, t1, .Lcbrh_try_push_number_sub
  li t1, 0x43
  beq t0, t1, .Lcbrh_try_number_push_sub
  j .Lcbrh_advance
.Lcbrh_try_push_number_sub:
  lbu t2, 2(s6); li t3, 0x43; bne t2, t3, .Lcbrh_advance
  lbu t2, 3(s6); li t3, 0x03; bne t2, t3, .Lcbrh_advance
  lbu t2, 4(s6); li t3, 0x40; bne t2, t3, .Lcbrh_advance
  lbu t4, 1(s6)              # offset
  bleu t4, s5, .Lcbrh_advance
  mv s5, t4
  j .Lcbrh_advance
.Lcbrh_try_number_push_sub:
  lbu t2, 1(s6); li t3, 0x60; bne t2, t3, .Lcbrh_advance
  lbu t2, 3(s6); li t3, 0x03; bne t2, t3, .Lcbrh_advance
  lbu t2, 4(s6); li t3, 0x40; bne t2, t3, .Lcbrh_advance
  lbu t4, 2(s6)              # offset
  bleu t4, s5, .Lcbrh_advance
  mv s5, t4
.Lcbrh_advance:
  addi s6, s6, 1
  addi s7, s7, -1
  j .Lcbrh_scan_loop
.Lcbrh_next_item:
  addi s4, s4, 1
  j .Lcbrh_item_loop
.Lcbrh_ok:
  sd s5, 0(s2)
  li a0, 0
  j .Lcbrh_ret
.Lcbrh_fail:
  li a0, 1
.Lcbrh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
