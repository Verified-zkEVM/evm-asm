stateless_verdict_from_ssz:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  li s0, 0x40000000
  addi s0, s0, 18             # s0 = SSZ_BASE (INPUT + 16 + 2)
  # 1. payload + withdrawals.
  mv a0, s0
  la a1, svf_payload; la a2, svf_wds_ptr; la a3, svf_wds_count
  jal ra, extract_payload_and_withdrawals
  bnez a0, .Lsvf_zero         # malformed SSZ payload/withdrawals offsets
  # 2. pre-state witness section.
  mv a0, s0
  la a1, svf_witness; la a2, svf_witness_len
  jal ra, extract_witness_state_section
  # 3. parent header + state_root (this.parent_hash = payload + 0).
  mv a0, s0
  la t0, svf_payload; ld a1, 0(t0)
  la a2, svf_parent_rlp; la a3, svf_parent_rlp_len; la a4, svf_parent_sr
  jal ra, extract_parent_header_and_state_root
  bnez a0, .Lsvf_zero         # parent not found / parse fail
  # 4. SSZ withdrawals (44 B each) -> RLP descriptors (ptr,len) 16 B each.
  la t0, svf_wds_count; ld s1, 0(t0)    # s1 = count
  la t0, svf_wds_ptr;   ld s2, 0(t0)    # s2 = ssz withdrawals base
  la s3, svf_descriptors                # s3 = descriptor cursor
  la s4, svf_rlp_arena                  # s4 = rlp arena cursor
  li s5, 0
.Lsvf_wloop:
  bge s5, s1, .Lsvf_wdone
  mv a0, s2; mv a1, s4; la a2, svf_wd_len
  jal ra, ssz_withdrawal_to_rlp
  sd s4, 0(s3)
  la t0, svf_wd_len; ld t1, 0(t0); sd t1, 8(s3)
  addi s2, s2, 44
  addi s4, s4, 72
  addi s3, s3, 16
  addi s5, s5, 1
  j .Lsvf_wloop
.Lsvf_wdone:
  # 5. fill the 13-field step2_verdict params struct (sv_params).
  la t1, sv_params
  la t0, svf_payload;        ld t0, 0(t0); sd t0, 0(t1)   # payload
  la t0, svf_parent_rlp;     ld t0, 0(t0); sd t0, 8(t1)   # parent_rlp ptr
  la t0, svf_parent_rlp_len; ld t0, 0(t0); sd t0, 16(t1)  # parent_rlp_len
  la t0, svf_parent_sr;      sd t0, 24(t1)                # parent_state_root ptr
  la t0, svf_zero32;         sd t0, 32(t1)                # tx_root (placeholder)
  la t0, svf_zero32;         sd t0, 40(t1)                # wd_root (placeholder)
  addi t0, s0, 24;           sd t0, 48(t1)                # parent_beacon_block_root (NPR+8)
  la t0, svf_zero32;         sd t0, 56(t1)                # requests_hash (placeholder)
  la t0, svf_zero32;         sd t0, 96(t1)                # block_access_list_hash (placeholder)
  la t0, svf_descriptors;    sd t0, 64(t1)                # wds_descriptors
  la t0, svf_wds_count;      ld t0, 0(t0); sd t0, 72(t1)  # n_wds
  la t0, svf_witness;        ld t0, 0(t0); sd t0, 80(t1)  # witness
  la t0, svf_witness_len;    ld t0, 0(t0); sd t0, 88(t1)  # witness_len
  # 6. verdict = step2_verdict(params).
  la a0, sv_params
  jal ra, step2_verdict
  j .Lsvf_ret
.Lsvf_zero:
  li a0, 0
.Lsvf_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
