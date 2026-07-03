account_is_empty_at_header_state_root:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # witness.state ptr
  mv s4, a4                  # witness.state len
  # Pre-zero predicate.
  la t0, aie_predicate
  sd zero, 0(t0)
  # Step 1: header.state_root -> aie_state_root.
  mv a0, s0
  mv a1, s1
  la a2, aie_state_root
  jal ra, header_extract_state_root
  beqz a0, .Laiehsr_step2
  li a0, 4
  j .Laiehsr_ret
.Laiehsr_step2:
  # Step 2: account_at_address.
  mv a0, s2
  li a1, 20
  la a2, aie_state_root
  mv a3, s3
  mv a4, s4
  la s5, aie_acct_struct
  mv a5, s5
  jal ra, account_at_address
  beqz a0, .Laiehsr_check
  li t0, 1
  beq a0, t0, .Laiehsr_absent
  j .Laiehsr_ret
.Laiehsr_absent:
  # absent -> predicate 0 (already zero).
  li a0, 0
  j .Laiehsr_ret
.Laiehsr_check:
  # nonce == 0 ?
  ld t1, 0(s5)
  bnez t1, .Laiehsr_non_empty
  # balance == 0 ?
  ld t1,  8(s5); bnez t1, .Laiehsr_non_empty
  ld t1, 16(s5); bnez t1, .Laiehsr_non_empty
  ld t1, 24(s5); bnez t1, .Laiehsr_non_empty
  ld t1, 32(s5); bnez t1, .Laiehsr_non_empty
  # code_hash == EMPTY_CODE_HASH ?
  la t0, aie_empty_code_hash
  ld t1,  0(t0); ld t2, 72(s5); bne t1, t2, .Laiehsr_non_empty
  ld t1,  8(t0); ld t2, 80(s5); bne t1, t2, .Laiehsr_non_empty
  ld t1, 16(t0); ld t2, 88(s5); bne t1, t2, .Laiehsr_non_empty
  ld t1, 24(t0); ld t2, 96(s5); bne t1, t2, .Laiehsr_non_empty
  # All three empty-conditions hold; predicate := 1.
  la t0, aie_predicate
  li t1, 1
  sd t1, 0(t0)
  li a0, 0
  j .Laiehsr_ret
.Laiehsr_non_empty:
  # Predicate stays 0.
  li a0, 0
.Laiehsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
