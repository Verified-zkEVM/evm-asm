mpt_leaf_node_encode_from_nibbles:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # path_nibbles ptr
  mv s1, a1                   # nibble count
  mv s2, a2                   # value ptr
  mv s3, a3                   # value len
  mv s4, a4                   # output ptr
  mv s5, a5                   # out_length ptr
  li t0, 0xa0000000  # RAM_MEM_START bound
  bltu s4, t0, .Lmlnen_fail
  bltu s5, t0, .Lmlnen_fail
  li t0, 0xc0000000
  bgeu s4, t0, .Lmlnen_fail
  li t0, 0xbffffff8  # RAM_MEM_END-8 bound
  bgtu s5, t0, .Lmlnen_fail
  li t0, 16000
  bgtu s3, t0, .Lmlnen_fail
  # ---- Step 1: HP-encode (leaf=true) ----
  mv a0, s0; mv a1, s1; li a2, 1
  la a3, mlnen_hp_buf
  jal ra, hp_encode_nibbles
  la t0, mlnen_hp_len; sd a0, 0(t0)
  # ---- Step 2: RLP-encode hp_path into payload_buf ----
  la a0, mlnen_hp_buf
  la t0, mlnen_hp_len; ld a1, 0(t0)
  la a2, mlnen_payload_buf
  la a3, mlnen_field_len
  jal ra, rlp_encode_bytes
  la t0, mlnen_field_len; ld t1, 0(t0)
  la t0, mlnen_cursor; sd t1, 0(t0)
  # ---- Step 3: RLP-encode value at payload[cursor..] ----
  la t0, mlnen_cursor; ld t1, 0(t0)
  mv a0, s2; mv a1, s3
  la a2, mlnen_payload_buf; add a2, a2, t1
  la a3, mlnen_field_len
  jal ra, rlp_encode_bytes
  la t0, mlnen_field_len; ld t1, 0(t0)
  la t0, mlnen_cursor; ld t2, 0(t0)
  add t2, t2, t1
  la t0, mlnen_total_payload; sd t2, 0(t0)
  # ---- Step 4: outer list prefix to output[0..] ----
  mv a0, t2; mv a1, s4
  la a2, mlnen_field_len
  jal ra, rlp_encode_list_prefix
  la t0, mlnen_field_len; ld t1, 0(t0)
  la t0, mlnen_total_payload; ld t2, 0(t0)
  add t6, s4, t1
  bltu t6, s4, .Lmlnen_fail
  add t6, t6, t2
  bltu t6, s4, .Lmlnen_fail
  li t0, 0xc0000000
  bgtu t6, t0, .Lmlnen_fail
  # ---- Step 5: copy payload after prefix ----
  add t3, s4, t1
  la t4, mlnen_payload_buf
  mv t5, t2
.Lmlnen_cp:
  beqz t5, .Lmlnen_cp_done
  lbu t6, 0(t4)
  sb t6, 0(t3)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t5, t5, -1
  j .Lmlnen_cp
.Lmlnen_cp_done:
  add t1, t1, t2
  sd t1, 0(s5)
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
.Lmlnen_fail:
  li a0, 1
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
