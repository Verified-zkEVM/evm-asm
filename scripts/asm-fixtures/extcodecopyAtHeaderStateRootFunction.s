extcodecopy_at_header_state_root:
  addi sp, sp, -96
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # code_offset
  mv s4, a4                  # length
  mv s5, a5                  # output buffer ptr
  mv s6, a6                  # witness.state ptr
  mv s7, a7                  # witness.state len
  # Reject length > 65536 (EIP-7907 MAX_CODE_SIZE / deployed-code-size cap).
  li t0, 65536
  bgtu s4, t0, .Lecc_too_long
  # Pre-zero output[0..length] byte-by-byte (length <= 65536).
  mv t0, s5
  mv t1, s4
.Lecc_zero_loop:
  beqz t1, .Lecc_zero_done
  sb zero, 0(t0)
  addi t0, t0, 1
  addi t1, t1, -1
  j .Lecc_zero_loop
.Lecc_zero_done:
  # Step 1: header.state_root -> ecc_state_root.
  mv a0, s0
  mv a1, s1
  la a2, ecc_state_root
  jal ra, header_extract_state_root
  beqz a0, .Lecc_step2
  li a0, 4
  j .Lecc_ret
.Lecc_step2:
  # Step 2: account_at_address -> ecc_acct_struct.
  mv a0, s2
  li a1, 20
  la a2, ecc_state_root
  mv a3, s6
  mv a4, s7
  la s8, ecc_acct_struct
  mv a5, s8
  jal ra, account_at_address
  beqz a0, .Lecc_step3
  li t0, 1
  beq a0, t0, .Lecc_success_zero  # 1 -> output is zeros
  j .Lecc_ret                     # 2/3 propagate
.Lecc_success_zero:
  li a0, 0
  j .Lecc_ret
.Lecc_step3:
  # Check code_hash == EMPTY_CODE_HASH.
  la t0, ecc_empty_code_hash
  ld t1,  0(t0); ld t2, 72(s8); bne t1, t2, .Lecc_step4
  ld t1,  8(t0); ld t2, 80(s8); bne t1, t2, .Lecc_step4
  ld t1, 16(t0); ld t2, 88(s8); bne t1, t2, .Lecc_step4
  ld t1, 24(t0); ld t2, 96(s8); bne t1, t2, .Lecc_step4
  # Empty code; output stays zero, return 0.
  li a0, 0
  j .Lecc_ret
.Lecc_step4:
  # Step 4: lookup code in witness.codes.
  la t0, eccp_codes_ptr; ld a0, 0(t0)
  la t0, eccp_codes_len; ld a1, 0(t0)
  addi a2, s8, 72            # &acct.code_hash
  la a3, ecc_match_offset
  la a4, ecc_match_len
  mv a5, s2                  # GH #10619: address ptr for the CodeRead tuple
  jal ra, code_read_fetch
  beqz a0, .Lecc_step5
  li a0, 5                   # integrity violation
  j .Lecc_ret
.Lecc_step5:
  # s9 = code_ptr = codes_ptr + match_offset
  la t0, eccp_codes_ptr; ld t1, 0(t0)
  la t0, ecc_match_offset; ld t2, 0(t0)
  add s9, t1, t2
  # code_len in t3
  la t0, ecc_match_len; ld t3, 0(t0)
  # Byte-by-byte zero-padded copy.
  # for i in 0..length: output[i] = code[code_offset+i] if code_offset+i < code_len else 0
  li t0, 0                   # i
.Lecc_copy_loop:
  beq t0, s4, .Lecc_copy_done
  add t1, s3, t0             # src_idx = code_offset + i
  bgeu t1, t3, .Lecc_pad     # past code end -> already zero
  add t2, s9, t1             # code_ptr + src_idx
  lbu t4, 0(t2)
  add t5, s5, t0
  sb t4, 0(t5)
.Lecc_pad:
  addi t0, t0, 1
  j .Lecc_copy_loop
.Lecc_copy_done:
  li a0, 0
  j .Lecc_ret
.Lecc_too_long:
  li a0, 6
.Lecc_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
