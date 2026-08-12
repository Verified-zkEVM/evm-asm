eip7702_authority_asof:
  addi sp, sp, -64; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp); mv s0, a0; li s2, 0
  addi a1, sp, 56; addi a2, sp, 48; mv a0, s0; jal ra, account_writes_auth_current
  li t0, 1; bne a0, t0, .L77as_normal_nonce
  ld s1, 56(sp)
  mv a0, s0; addi a1, sp, 56; jal ra, account_writes_latest_nonce_tx
  beqz a0, .L77as_hit_nonce_done; ld s1, 56(sp)
.L77as_hit_nonce_done:
  mv a0, s0; addi a1, sp, 56; addi a2, sp, 48; jal ra, account_writes_auth_block
  beqz a0, .L77as_deleg_hdr
  li t0, 2; beq a0, t0, .L77as_deleg_empty
  beqz a2, .L77as_deleg_empty; li t0, 23; bne a2, t0, .L77as_deleg_empty; lbu t0, 0(a1); li t1, 239; bne t0, t1, .L77as_deleg_empty; lbu t0, 1(a1); li t1, 1; bne t0, t1, .L77as_deleg_empty; lbu t0, 2(a1); bnez t0, .L77as_deleg_empty; mv a1, s1; li a2, 1; li a0, 1; j .L77as_ret
.L77as_deleg_empty:
  mv a1, s1; li a2, 0; li a0, 1; j .L77as_ret
.L77as_deleg_hdr:
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s0; la t0, bv_witness_state_ptr; ld a3, 0(t0); la t0, bv_witness_state_len; ld a4, 0(t0); la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0); jal ra, code_at_header_state_root
  beqz a0, .L77as_deleg_code; li t0, 1; beq a0, t0, .L77as_deleg_empty; li t0, 5; beq a0, t0, .L77as_deleg_empty; mv a1, s1; li a2, 0; li a0, 1; j .L77as_ret
.L77as_deleg_code:
  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .L77as_deleg_empty; li t1, 23; bne t0, t1, .L77as_deleg_empty; la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1; lbu t1, 0(t0); li t2, 239; bne t1, t2, .L77as_deleg_empty; lbu t1, 1(t0); li t2, 1; bne t1, t2, .L77as_deleg_empty; lbu t1, 2(t0); bnez t1, .L77as_deleg_empty; mv a1, s1; li a2, 1; li a0, 1; j .L77as_ret
.L77as_normal_nonce:
  li t0, 2; beq a0, t0, .L77as_absent
  mv a0, s0; addi a1, sp, 56; li a2, 20; jal ra, account_writes_latest_nonce_tx
  beqz a0, .L77as_try_block; ld s1, 56(sp); li s2, 1; j .L77as_header
.L77as_try_block:
  mv a0, s0; addi a1, sp, 56; li a2, 21; jal ra, account_writes_latest_nonce_block
  beqz a0, .L77as_header; ld s1, 56(sp); li s2, 1
.L77as_header:
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s0; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, teer_pre_acct; jal ra, account_at_header_state_root
  beqz a0, .L77as_found; li t0, 1; beq a0, t0, .L77as_absent; li a0, 2; li a1, 0; li a2, 0; j .L77as_ret
.L77as_found:
  bnez s2, .L77as_nonce_ready; la t0, teer_pre_acct; ld a1, 0(t0)
.L77as_nonce_ready:
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s0; la t0, bv_witness_state_ptr; ld a3, 0(t0); la t0, bv_witness_state_len; ld a4, 0(t0); la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0); jal ra, code_at_header_state_root
  beqz a0, .L77as_code; li t0, 1; beq a0, t0, .L77as_live_empty; li t0, 5; beq a0, t0, .L77as_live_empty; li a0, 2; li a1, 0; li a2, 0; j .L77as_ret
.L77as_code:
  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .L77as_live_empty; li t1, 23; bne t0, t1, .L77as_invalid_code; la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1; lbu t1, 0(t0); li t2, 239; bne t1, t2, .L77as_invalid_code; lbu t1, 1(t0); li t2, 1; bne t1, t2, .L77as_invalid_code; lbu t1, 2(t0); bnez t1, .L77as_invalid_code; li a2, 1; j .L77as_live
.L77as_invalid_code:
  li a0, 3; li a1, 0; li a2, 0; j .L77as_ret
.L77as_live_empty:
  li a2, 0
.L77as_live:
  bnez s2, .L77as_live_map; la t0, teer_pre_acct; ld s1, 0(t0)
.L77as_live_map:
  mv a1, s1; li a0, 1; j .L77as_ret
.L77as_absent:
  li a0, 0; li a1, 0; li a2, 0
.L77as_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld a3, 32(sp); ld a4, 40(sp); ld a5, 48(sp); addi sp, sp, 64; ret
