mpt_extension_node_encode:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # path_nibbles ptr
  mv s1, a1                   # nibble count
  mv s2, a2                   # child_ref ptr
  mv s3, a3                   # child_ref len
  mv s4, a4                   # output ptr
  mv s5, a5                   # out_length ptr
  li t0, 0xa0000000
  bltu s4, t0, .Lmxne_fail
  bltu s5, t0, .Lmxne_fail
  li t0, 0xc0000000
  bgeu s4, t0, .Lmxne_fail
  li t0, 0xbffffff8
  bgtu s5, t0, .Lmxne_fail
  # ---- Step 1: HP-encode nibbles (is_leaf=0) ----
  mv a0, s0; mv a1, s1; li a2, 0
  la a3, mxne_hp_buf
  jal ra, hp_encode_nibbles
  la t0, mxne_hp_len; sd a0, 0(t0)
  # ---- Step 2: RLP-encode hp_path into payload[0..] ----
  la a0, mxne_hp_buf
  la t0, mxne_hp_len; ld a1, 0(t0)
  la a2, mxne_payload_buf
  la a3, mxne_field_len
  jal ra, rlp_encode_bytes
  la t0, mxne_field_len; ld t1, 0(t0)         # hp_rlp_len
  la t0, mxne_cursor; sd t1, 0(t0)
  # ---- Step 3: copy child_ref verbatim into payload[cursor..] ----
  la t0, mxne_cursor; ld t1, 0(t0)
  la t2, mxne_payload_buf; add t2, t2, t1     # dst
  mv t3, s2                                    # src
  mv t4, s3                                    # remaining
.Lmxne_cref_cp:
  beqz t4, .Lmxne_cref_done
  lbu t5, 0(t3)
  sb t5, 0(t2)
  addi t2, t2, 1
  addi t3, t3, 1
  addi t4, t4, -1
  j .Lmxne_cref_cp
.Lmxne_cref_done:
  la t0, mxne_cursor; ld t1, 0(t0)
  add t2, t1, s3                                # total payload len
  la t0, mxne_total_payload; sd t2, 0(t0)
  # ---- Step 4: outer list prefix to output[0..] ----
  mv a0, t2; mv a1, s4
  la a2, mxne_field_len
  jal ra, rlp_encode_list_prefix
  la t0, mxne_field_len; ld t1, 0(t0)          # outer_prefix_len
  la t0, mxne_total_payload; ld t2, 0(t0)
  add t6, s4, t1
  bltu t6, s4, .Lmxne_fail
  add t6, t6, t2
  bltu t6, s4, .Lmxne_fail
  li t0, 0xc0000000
  bgtu t6, t0, .Lmxne_fail
  # ---- Step 5: copy payload after prefix ----
  add t3, s4, t1                                # dst
  la t4, mxne_payload_buf                       # src
  mv t5, t2                                     # remaining
.Lmxne_body_cp:
  beqz t5, .Lmxne_body_done
  lbu t6, 0(t4)
  sb t6, 0(t3)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t5, t5, -1
  j .Lmxne_body_cp
.Lmxne_body_done:
  add t1, t1, t2                                # total written = prefix + payload
  sd t1, 0(s5)
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
.Lmxne_fail:
  li a0, 1
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
