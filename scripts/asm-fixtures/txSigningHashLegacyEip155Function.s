tx_signing_hash_legacy_eip155:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # tx_rlp ptr
  mv s1, a1                   # tx_rlp len
  mv s2, a2                   # chain_id
  mv s3, a3                   # output hash ptr
  # ---- Parse outer list prefix to get payload_start ----
  # NOTE: K20 returns content offsets, not item-start offsets.
  # We need the byte right after the outer list prefix.
  beqz s1, .Lt155_fail
  lbu t0, 0(s0)
  li t1, 0xc0
  bltu t0, t1, .Lt155_fail
  li t1, 0xf8
  bltu t0, t1, .Lt155_short_list
  addi s4, t0, -0xf7
  addi s4, s4, 1                              # payload_start
  j .Lt155_have_start
.Lt155_short_list:
  li s4, 1
.Lt155_have_start:
  # ---- Locate field 5 to get end-of-body ----
  mv a0, s0; mv a1, s1; li a2, 5
  la a3, t155_offset_hi; la a4, t155_length_hi
  jal ra, rlp_list_nth_item
  bnez a0, .Lt155_fail
  la t0, t155_offset_hi; ld t1, 0(t0)
  la t0, t155_length_hi; ld t2, 0(t0)
  add t1, t1, t2                              # end-of-body
  sub s5, t1, s4                              # body_len
  # ---- Encode chain_id as canonical RLP into t155_chain_be ----
  # Write chain_id as 8 BE bytes to t155_chain_be
  la t0, t155_chain_be
  li t1, 7
.Lt155_chain_be_loop:
  bltz t1, .Lt155_chain_be_done
  slli t2, t1, 3
  srl t3, s2, t2
  andi t3, t3, 0xff
  sb t3, 0(t0)
  addi t0, t0, 1
  addi t1, t1, -1
  j .Lt155_chain_be_loop
.Lt155_chain_be_done:
  la a0, t155_chain_be; li a1, 8
  la a2, t155_chain_enc
  jal ra, rlp_encode_uint_be
  mv t3, a0                                   # chain_id_enc_len
  # tail_len = chain_id_enc_len + 2  (two 0x80 bytes for 0, 0)
  addi t3, t3, 2
  # new_payload_len = body_len + tail_len. Held in a callee-saved register
  # (s6) because rlp_encode_list_prefix's long-list path (payload >= 56)
  # clobbers t4; new_payload_len is reused below for the chain_id length and
  # the final keccak length, so a t-reg would corrupt both for large txs.
  add s6, s5, t3                              # new_payload_len
  # ---- Write new outer list prefix into t155_buf[0..] ----
  # .63.1.6.2.8 (e1s5z): NO 128 KiB capacity cap. The 6-field body is streamed
  # IN PLACE from the input region via zkvm_keccak256_segments, so a legacy
  # EIP-155 tx with arbitrarily large calldata (up to the block-gas bound,
  # ~20 MB at 200M gas) hashes without a staging-buffer overflow. The old gate
  # fail-closed at 128 KiB -> false-reject (bead .11.3); streaming is sound for
  # any size with O(1) extra memory and no input mutation.
  mv a0, s6; la a1, t155_buf
  la a2, t155_prefix_len
  jal ra, rlp_encode_list_prefix
  # ---- Build suffix [chain_id_enc || 0x80 || 0x80] at t155_buf+64 ----
  sub t2, s6, s5; addi t2, t2, -2             # chain_id_enc_len = new_payload - body - 2
  la t0, t155_buf; addi t0, t0, 64            # suffix dst (small; prefix lives at +0)
  la t1, t155_chain_enc
  mv t3, t2
.Lt155_suffix_cp:
  beqz t3, .Lt155_suffix_tail
  lbu t6, 0(t1); sb t6, 0(t0); addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; j .Lt155_suffix_cp
.Lt155_suffix_tail:
  li t6, 0x80; sb t6, 0(t0); sb t6, 1(t0)     # (0, 0) tail
  addi t2, t2, 2                              # suffix_len = chain_id_enc_len + 2
  # ---- Build 3-segment descriptor at t155_buf+128: prefix || body(in place) || suffix ----
  la t4, t155_prefix_len; ld t4, 0(t4)        # prefix_len
  la t5, t155_buf; addi t5, t5, 128           # &segs[0]
  la t6, t155_buf; sd t6, 0(t5); sd t4, 8(t5)            # seg0 = (prefix, prefix_len)
  add t6, s0, s4; sd t6, 16(t5); sd s5, 24(t5)           # seg1 = (input+payload_start, body_len) IN PLACE
  la t6, t155_buf; addi t6, t6, 64; sd t6, 32(t5); sd t2, 40(t5)   # seg2 = (suffix, suffix_len)
  mv a0, t5; li a1, 3; mv a2, s3
  jal ra, zkvm_keccak256_segments
  li a0, 0
  j .Lt155_ret
.Lt155_fail:
  li a0, 1
.Lt155_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
