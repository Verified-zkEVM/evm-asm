receipt_encode:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # status
  mv s1, a1                   # cumulative_gas
  mv s2, a2                   # bloom ptr
  mv s3, a3                   # logs_rlp ptr
  mv s4, a4                   # logs_rlp len
  mv s5, a5                   # output ptr
  mv s6, a6                   # out_length ptr
  # The running cursor (payload offset within re_payload_buf) is
  # stashed to `re_cursor` across `jal` calls since t-registers are
  # caller-saved and the encode helpers clobber them.
  la t0, re_cursor; sd zero, 0(t0)
  # ---- Step 1: encode status into re_payload_buf[0..] ----
  mv a0, s0
  la a1, re_payload_buf
  la a2, re_field_len
  jal ra, rlp_encode_u64
  la t0, re_field_len; ld t1, 0(t0)         # status_len
  la t0, re_cursor; sd t1, 0(t0)            # cursor = status_len
  # ---- Step 2: encode cumulative_gas at re_payload_buf[cursor] ----
  la t0, re_cursor; ld t2, 0(t0)
  mv a0, s1
  la a1, re_payload_buf; add a1, a1, t2
  la a2, re_field_len
  jal ra, rlp_encode_u64
  la t0, re_field_len; ld t1, 0(t0)         # gas_len
  la t0, re_cursor; ld t2, 0(t0)
  add t2, t2, t1
  la t0, re_cursor; sd t2, 0(t0)
  # ---- Step 3: encode bloom (256 B) ----
  mv a0, s2; li a1, 256
  la a2, re_payload_buf; add a2, a2, t2
  la a3, re_field_len
  jal ra, rlp_encode_bytes
  la t0, re_field_len; ld t1, 0(t0)         # bloom_enc_len
  la t0, re_cursor; ld t2, 0(t0)
  add t2, t2, t1
  # ---- Step 4: copy logs_rlp verbatim ----
  la t3, re_payload_buf; add t3, t3, t2     # dst
  mv t4, s3                                 # src
  mv t5, s4                                 # remaining bytes
.Lre_logs_cp:
  beqz t5, .Lre_logs_done
  lbu t6, 0(t4)
  sb t6, 0(t3)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t5, t5, -1
  j .Lre_logs_cp
.Lre_logs_done:
  add t2, t2, s4                            # total payload len
  # Stash total_payload before the next jal clobbers caller-saved t2.
  la t0, re_total_payload; sd t2, 0(t0)
  # ---- Step 5: write outer list prefix at output[0..] ----
  mv a0, t2; mv a1, s5
  la a2, re_field_len
  jal ra, rlp_encode_list_prefix
  la t0, re_field_len; ld t1, 0(t0)        # outer_prefix_len
  # ---- Step 6: copy re_payload_buf[..total_payload] to output[prefix_len..] ----
  # Total payload was last stashed in t2; restore via .data
  # Actually we lost t2 across jal. Re-derive: total_payload =
  # bytes_written - bytes_p, but cleaner to re-compute it from
  # re_payload_buf metadata. Save total_payload before jal next time.
  # Use the stashed value: we'll save t2 to .data BEFORE the
  # rlp_encode_list_prefix call.
  # (Fixed by re-reading the saved payload total below.)
  la t0, re_total_payload; ld t2, 0(t0)
  add t3, s5, t1                            # dst = output + prefix_len
  la t4, re_payload_buf                     # src
  mv t5, t2                                 # remaining
.Lre_body_cp:
  beqz t5, .Lre_body_done
  lbu t6, 0(t4)
  sb t6, 0(t3)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t5, t5, -1
  j .Lre_body_cp
.Lre_body_done:
  # total_written = outer_prefix_len + total_payload
  add t1, t1, t2
  sd t1, 0(s6)
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
