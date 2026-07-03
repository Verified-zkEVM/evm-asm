step2_verdict:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # params
  # 1. this header RLP = block_header_ssz_to_rlp(payload, header commitments).
  ld a0, 0(s0); ld a1, 32(s0); ld a2, 40(s0); ld a3, 48(s0); ld a4, 56(s0)
  ld a7, 96(s0)
  la a5, sv_this_rlp; la a6, sv_this_rlp_len
  jal ra, block_header_ssz_to_rlp
  # 2. validate_header_rlp_pair(this_rlp, parent_rlp).
  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)
  ld a2, 8(s0); ld a3, 16(s0)
  jal ra, validate_header_rlp_pair
  mv s1, a0                   # header validity status
  # 3. recompute post-state root from withdrawals over the pre-state.
  ld a0, 24(s0); ld a1, 80(s0); ld a2, 88(s0)
  ld a3, 64(s0); ld a4, 72(s0); la a5, sv_recomputed
  jal ra, withdrawals_state_root
  mv s2, a0                   # recompute status
  # 4. memcmp(recomputed, this.state_root = payload+52) over 32 bytes.
  la t0, sv_recomputed
  ld t1, 0(s0); addi t1, t1, 52   # claimed state_root ptr
  li t2, 32
.Lsv_cmp:
  beqz t2, .Lsv_cmp_ok
  lbu t3, 0(t0); lbu t4, 0(t1)
  bne t3, t4, .Lsv_zero
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1
  j .Lsv_cmp
.Lsv_cmp_ok:
  # 5. verdict = (header valid) AND (recompute ok) AND (root match).
  bnez s1, .Lsv_zero
  bnez s2, .Lsv_zero
  li a0, 1
  j .Lsv_ret
.Lsv_zero:
  li a0, 0
.Lsv_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
