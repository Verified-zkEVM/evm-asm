block_logs_bloom_from_receipts_list:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0                   # receipts list ptr
  mv s1, a1                   # receipts list len
  mv s2, a2                   # output bloom ptr
  # ---- Count receipts ----
  mv a0, s0; mv a1, s1
  la a2, blbr_count
  jal ra, rlp_list_count_items
  bnez a0, .Lblbr_parse_fail
  la t0, blbr_count; ld s3, 0(t0)              # raw RLP item count
  li s4, 0                                     # raw item index
.Lblbr_loop:
  bgeu s4, s3, .Lblbr_done
  # Extract the next receipt. Typed receipts are encoded as type_byte || rlp(inner),
  # which appears as two raw RLP items inside this internal list.
  mv a0, s0; mv a1, s1; mv a2, s4
  la a3, blbr_offset; la a4, blbr_length
  jal ra, rlp_item_span
  bnez a0, .Lblbr_parse_fail
  la t0, blbr_offset; ld t1, 0(t0)
  la t0, blbr_length; ld t2, 0(t0)
  add a0, s0, t1                                # default legacy receipt ptr
  mv a1, t2                                    # default legacy receipt len
  li t3, 1; bne t2, t3, .Lblbr_have_receipt
  lbu t3, 0(a0); beqz t3, .Lblbr_have_receipt
  li t4, 4; bgtu t3, t4, .Lblbr_have_receipt
  addi t3, s4, 1; bgeu t3, s3, .Lblbr_parse_fail
  mv a0, s0; mv a1, s1; mv a2, t3
  la a3, blbr_next_offset; la a4, blbr_next_length
  jal ra, rlp_item_span
  bnez a0, .Lblbr_parse_fail
  la t0, blbr_next_offset; ld t1, 0(t0)
  la t0, blbr_next_length; ld t2, 0(t0)
  add a0, s0, t1                                # typed inner receipt ptr
  mv a1, t2                                    # typed inner receipt len
  addi s4, s4, 2
  j .Lblbr_extract
.Lblbr_have_receipt:
  addi s4, s4, 1
.Lblbr_extract:
  la a2, blbr_scratch_bloom
  jal ra, receipt_extract_logs_bloom
  bnez a0, .Lblbr_child_err                    # 1 or 2 -> propagate
  # OR scratch_bloom into output bloom.
  mv a0, s2
  la a1, blbr_scratch_bloom
  jal ra, bloom_or_into
  j .Lblbr_loop
.Lblbr_done:
  li a0, 0
  j .Lblbr_ret
.Lblbr_parse_fail:
  li a0, 1
  j .Lblbr_ret
.Lblbr_child_err:
  # a0 carries the child's status (1 = parse fail, 2 = size fail).
.Lblbr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 48
  ret
