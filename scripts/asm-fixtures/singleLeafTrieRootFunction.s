single_leaf_trie_root:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # key ptr
  mv s1, a1                   # key len
  mv s2, a2                   # value ptr
  mv s3, a3                   # value len
  mv s4, a4                   # output root ptr
  # ---- Step 1: expand key bytes to nibbles ----
  mv a0, s0; mv a1, s1
  la a2, sltr_nibbles
  jal ra, bytes_to_nibbles
  # a0 = 2 * key_len nibbles emitted -- store for HP step
  la t0, sltr_nibble_count; sd a0, 0(t0)
  # ---- Step 2: HP-encode the nibbles (leaf=true) ----
  la a0, sltr_nibbles
  la t0, sltr_nibble_count; ld a1, 0(t0)
  li a2, 1                                    # is_leaf = 1
  la a3, sltr_hp_buf
  jal ra, hp_encode_nibbles
  la t0, sltr_hp_len; sd a0, 0(t0)
  # ---- Step 3: RLP-encode hp_path into the payload buffer ----
  la a0, sltr_hp_buf
  la t0, sltr_hp_len; ld a1, 0(t0)
  la a2, sltr_payload_buf
  la a3, sltr_field_len
  jal ra, rlp_encode_bytes
  la t0, sltr_field_len; ld t1, 0(t0)         # hp_rlp_len
  la t0, sltr_cursor; sd t1, 0(t0)            # cursor = hp_rlp_len
  # ---- Step 4: RLP-encode value at payload[cursor..] ----
  la t0, sltr_cursor; ld t1, 0(t0)
  mv a0, s2; mv a1, s3
  la a2, sltr_payload_buf; add a2, a2, t1
  la a3, sltr_field_len
  jal ra, rlp_encode_bytes
  la t0, sltr_field_len; ld t1, 0(t0)         # value_rlp_len
  la t0, sltr_cursor; ld t2, 0(t0)
  add t2, t2, t1                              # total inner payload len
  la t0, sltr_total_payload; sd t2, 0(t0)
  # ---- Step 5: write outer list prefix at node_buf[0..] ----
  mv a0, t2
  la a1, sltr_node_buf
  la a2, sltr_field_len
  jal ra, rlp_encode_list_prefix
  la t0, sltr_field_len; ld t1, 0(t0)         # outer_prefix_len
  la t0, sltr_total_payload; ld t2, 0(t0)
  # ---- Step 6: copy payload after prefix in node_buf ----
  la t3, sltr_node_buf; add t3, t3, t1        # dst
  la t4, sltr_payload_buf                     # src
  mv t5, t2                                   # remaining
.Lsltr_cp:
  beqz t5, .Lsltr_cp_done
  lbu t6, 0(t4)
  sb t6, 0(t3)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t5, t5, -1
  j .Lsltr_cp
.Lsltr_cp_done:
  add t1, t1, t2                              # full leaf-node RLP length
  # ---- Step 7: keccak256(node_buf, full_len) → root ----
  la a0, sltr_node_buf
  mv a1, t1
  mv a2, s4
  jal ra, zkvm_keccak256
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
