rlp_list_truncate_to_n_fields:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # input_rlp ptr
  mv s1, a1                   # input_rlp len
  mv s2, a2                   # n_fields
  mv s3, a3                   # output buffer ptr
  mv s4, a4                   # out_length ptr
  beqz s2, .Lrltn_empty       # n == 0 → emit `0xc0`
  # ---- Parse the outer list prefix to get payload_start ----
  # NOTE: we cannot use `rlp_list_nth_item(input, 0)` for this:
  # K20 returns the *content* offset for byte-string items, which
  # drops the field's RLP prefix byte. The truncation needs the
  # *item* offset = start of the outer payload = byte after the
  # outer list prefix.
  beqz s1, .Lrltn_parse_fail
  lbu t0, 0(s0)
  li t1, 0xc0
  bltu t0, t1, .Lrltn_parse_fail   # not an RLP list
  li t1, 0xf8
  bltu t0, t1, .Lrltn_short_list
  # Long list: payload_start = 1 + (t0 - 0xf7)
  addi s5, t0, -0xf7
  addi s5, s5, 1
  j .Lrltn_have_start
.Lrltn_short_list:
  li s5, 1                          # payload_start = 1
.Lrltn_have_start:
  # ---- Locate field (n-1) to get end-of-payload ----
  addi t0, s2, -1
  mv a0, s0; mv a1, s1; mv a2, t0
  la a3, rltn_offset_hi; la a4, rltn_length_hi
  jal ra, rlp_list_nth_item
  bnez a0, .Lrltn_too_few
  la t0, rltn_offset_hi; ld t1, 0(t0)
  la t0, rltn_length_hi; ld t2, 0(t0)
  add t1, t1, t2                              # end-of-payload (after item n-1)
  sub s6, t1, s5                              # new_payload_len
  # ---- Write new outer list prefix ----
  mv a0, s6; mv a1, s3
  la a2, rltn_prefix_len
  jal ra, rlp_encode_list_prefix
  la t0, rltn_prefix_len; ld t1, 0(t0)        # prefix_len
  # ---- Copy payload bytes ----
  add t2, s3, t1                              # dst = output + prefix
  add t3, s0, s5                              # src = input + payload_start
  mv t4, s6                                   # remaining bytes
.Lrltn_cploop:
  beqz t4, .Lrltn_cpdone
  lbu t5, 0(t3)
  sb t5, 0(t2)
  addi t2, t2, 1
  addi t3, t3, 1
  addi t4, t4, -1
  j .Lrltn_cploop
.Lrltn_cpdone:
  add t1, t1, s6                              # out_len = prefix + payload
  sd t1, 0(s4)
  li a0, 0
  j .Lrltn_ret
.Lrltn_empty:
  li t0, 0xc0
  sb t0, 0(s3)
  li t0, 1
  sd t0, 0(s4)
  li a0, 0
  j .Lrltn_ret
.Lrltn_parse_fail:
  li a0, 1
  j .Lrltn_ret
.Lrltn_too_few:
  li a0, 2
.Lrltn_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
