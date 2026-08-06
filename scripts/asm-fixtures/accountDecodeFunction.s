account_decode:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                  # account ptr
  mv s1, a1                  # account_len
  mv s2, a2                  # nonce out
  mv s3, a3                  # balance out
  mv s4, a4                  # storage_root out
  mv s5, a5                  # code_hash out
  # Field 0: nonce (u64 BE → LE store)
  mv a0, s0
  mv a1, s1
  li a2, 0
  la a3, ad_offset
  la a4, ad_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lad_fail
  la t0, ad_length; ld t1, 0(t0)
  li t2, 8
  bgtu t1, t2, .Lad_fail      # nonce > 8 bytes
  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3
  li t2, 0                   # accumulator
.Lad_nonce_loop:
  beqz t1, .Lad_nonce_done
  slli t2, t2, 8
  lbu t4, 0(t3)
  or t2, t2, t4
  addi t3, t3, 1
  addi t1, t1, -1
  j .Lad_nonce_loop
.Lad_nonce_done:
  sd t2, 0(s2)               # nonce_out (LE u64)
  # Field 1: balance (u256 BE → BE 32-byte buffer)
  mv a0, s0
  mv a1, s1
  li a2, 1
  la a3, ad_offset
  la a4, ad_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lad_fail
  la t0, ad_length; ld t1, 0(t0)
  li t2, 32
  bgtu t1, t2, .Lad_fail      # balance > 32 bytes
  # Zero balance_out
  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)
  # Right-align: write to s3 + (32 - length)
  sub t2, t2, t1             # 32 - length
  add t4, s3, t2             # dst
  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3
.Lad_bal_loop:
  beqz t1, .Lad_bal_done
  lbu t5, 0(t3)
  sb  t5, 0(t4)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t1, t1, -1
  j .Lad_bal_loop
.Lad_bal_done:
  # Field 2: storage_root (must be exactly 32 bytes)
  mv a0, s0
  mv a1, s1
  li a2, 2
  la a3, ad_offset
  la a4, ad_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lad_fail
  la t0, ad_length; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Lad_root_zero      # GH #11483: len != 32 -> zero-length dispatch
  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3
  lbu t4, 0(t3); sb t4, 0(s4)
  addi t3, t3, 1; addi s4, s4, 1; addi t1, t1, -1
  bnez t1, .-20
  nop
  nop
.Lad_field3:
  # Field 3: code_hash (must be exactly 32 bytes)
  mv a0, s0
  mv a1, s1
  li a2, 3
  la a3, ad_offset
  la a4, ad_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lad_fail
  la t0, ad_length; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Lad_code_zero      # GH #11483: len != 32 -> zero-length dispatch
  la t0, ad_offset; ld t3, 0(t0); add t3, s0, t3
  lbu t4, 0(t3); sb t4, 0(s5)
  addi t3, t3, 1; addi s5, s5, 1; addi t1, t1, -1
  bnez t1, .-20
  nop
  nop
.Lad_ok:
  li a0, 0
  j .Lad_ret
.Lad_fail:
  li a0, 1
.Lad_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret

  # GH #11483: fold a zero-length storage_root / code_hash to EMPTY_TRIE_ROOT /
  # EMPTY_CODE_HASH, mirroring execution-specs amsterdam witness_state.py:114-119.
  # Reached only from the exact-32 checks above; any other length still fails.
.Lad_root_zero:
  beq t1, x0, .Lad_root_fold
  j .Lad_fail
.Lad_root_fold:
  la t0, iw_empty_trie_root
  ld t2, 0(t0); sd t2, 0(s4)
  ld t2, 8(t0); sd t2, 8(s4)
  ld t2, 16(t0); sd t2, 16(s4)
  ld t2, 24(t0); sd t2, 24(s4)
  j .Lad_field3
.Lad_code_zero:
  beq t1, x0, .Lad_code_fold
  j .Lad_fail
.Lad_code_fold:
  la t0, aie_empty_code_hash
  ld t2, 0(t0); sd t2, 0(s5)
  ld t2, 8(t0); sd t2, 8(s5)
  ld t2, 16(t0); sd t2, 16(s5)
  ld t2, 24(t0); sd t2, 24(s5)
  j .Lad_ok
