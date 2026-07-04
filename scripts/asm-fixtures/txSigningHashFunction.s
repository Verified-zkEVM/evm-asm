tx_signing_hash:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # inner_rlp ptr
  mv s1, a1                   # inner_rlp len
  mv s2, a2                   # n_fields
  mv s3, a3                   # type_prefix (low byte; 0 = none)
  mv s4, a4                   # output hash ptr (32 B)
  # .63.1.6.2.8 (e1s5z follow-up): stream keccak([type?] || rlp([first n fields]))
  # over the inner RLP IN PLACE via zkvm_keccak256_segments -- NO 128 KiB tsh_buf
  # cap, so typed/modern txs with large calldata hash without a staging overflow.
  # tsh_buf now only holds the small type byte (+0), new list header (+16),
  # nth_item scratch (+64/+72), header length (+80) and the 3-seg descriptor
  # (+128). Same digest as the one-shot. Boundary parse mirrors
  # rlp_list_truncate_to_n_fields (payload_start + end-of-field(n-1)) but copies
  # nothing.
  la t0, tsh_buf; sb s3, 0(t0)              # type byte at tsh_buf[0] (unread when legacy)
  # ---- Parse outer list prefix -> payload_start (s5) ----
  beqz s1, .Ltsh_fail
  lbu t0, 0(s0)
  li t1, 0xc0; bltu t0, t1, .Ltsh_fail      # not an RLP list
  li t1, 0xf8; bltu t0, t1, .Ltsh_short_list
  addi s5, t0, -0xf7; addi s5, s5, 1        # long list: payload_start = 1 + (prefix - 0xf7)
  j .Ltsh_have_start
.Ltsh_short_list:
  li s5, 1
.Ltsh_have_start:
  # ---- new_payload_len (s6) = end_of_field(n-1) - payload_start ----
  li s6, 0
  beqz s2, .Ltsh_have_payload                # n == 0 -> empty list (payload 0)
  addi t0, s2, -1
  mv a0, s0; mv a1, s1; mv a2, t0
  la a3, tsh_buf; addi a3, a3, 64            # &content_offset (relative to inner_rlp)
  la a4, tsh_buf; addi a4, a4, 72            # &content_length
  jal ra, rlp_list_nth_item
  bnez a0, .Ltsh_fail                        # parse failure / fewer than n fields
  la t0, tsh_buf; ld t1, 64(t0); ld t2, 72(t0)
  add t1, t1, t2                             # end-of-payload (after field n-1)
  sub s6, t1, s5                             # new_payload_len
.Ltsh_have_payload:
  # ---- Build new outer list header at tsh_buf[16] ----
  mv a0, s6; la a1, tsh_buf; addi a1, a1, 16
  la a2, tsh_buf; addi a2, a2, 80            # &header_len
  jal ra, rlp_encode_list_prefix
  la t0, tsh_buf; ld t4, 80(t0)             # header_len (NH)
  # ---- Build 3-segment descriptor at tsh_buf[128]: [type?] || header || body(in place) ----
  la t5, tsh_buf; addi t5, t5, 128
  li t0, 0; beqz s3, .Ltsh_seg0
  li t0, 1
.Ltsh_seg0:
  la t6, tsh_buf; sd t6, 0(t5); sd t0, 8(t5)            # seg0 = (type byte, 0 or 1)
  la t6, tsh_buf; addi t6, t6, 16; sd t6, 16(t5); sd t4, 24(t5)   # seg1 = (header, NH)
  add t6, s0, s5; sd t6, 32(t5); sd s6, 40(t5)         # seg2 = (input+payload_start, new_payload_len)
  mv a0, t5; li a1, 3; mv a2, s4
  jal ra, zkvm_keccak256_segments
  li a0, 0
  j .Ltsh_ret
.Ltsh_fail:
  li a0, 1
.Ltsh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
