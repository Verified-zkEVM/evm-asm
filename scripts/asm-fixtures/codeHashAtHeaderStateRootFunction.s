code_hash_at_header_state_root:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # witness.state ptr
  mv s4, a4                  # witness.state len
  mv s5, a5                  # 32-byte output ptr
  # Pre-fill output with EMPTY_CODE_HASH (spec default for absent).
  la t0, chahsr_empty_code_hash
  ld t1,  0(t0); sd t1,  0(s5)
  ld t1,  8(t0); sd t1,  8(s5)
  ld t1, 16(t0); sd t1, 16(s5)
  ld t1, 24(t0); sd t1, 24(s5)
  # Step 1: header.state_root -> chahsr_state_root.
  mv a0, s0
  mv a1, s1
  la a2, chahsr_state_root
  jal ra, header_extract_state_root
  beqz a0, .Lchahsr_step2
  # Header parse fail: zero output for unambiguous error reporting.
  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)
  li a0, 4
  j .Lchahsr_ret
.Lchahsr_step2:
  mv a0, s2
  li a1, 20
  la a2, chahsr_state_root
  mv a3, s3
  mv a4, s4
  la s6, chahsr_acct_struct
  mv a5, s6
  jal ra, account_at_address
  beqz a0, .Lchahsr_copy
  li t0, 1
  beq a0, t0, .Lchahsr_absent  # 1 -> output stays EMPTY_CODE_HASH
  # 2/3 propagate; zero output for unambiguous error.
  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)
  j .Lchahsr_ret
.Lchahsr_absent:
  li a0, 0
  j .Lchahsr_ret
.Lchahsr_copy:
  # Copy code_hash (struct + 72 .. + 104) to output.
  ld t1, 72(s6); sd t1,  0(s5)
  ld t1, 80(s6); sd t1,  8(s5)
  ld t1, 88(s6); sd t1, 16(s5)
  ld t1, 96(s6); sd t1, 24(s5)
  li a0, 0
.Lchahsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
