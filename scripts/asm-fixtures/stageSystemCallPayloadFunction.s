stage_system_call_payload:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                    # target addr
  mv s1, a1                    # code ptr
  mv s2, a2                    # code len
  mv s3, a3                    # exec payload
  mv s4, a4                    # out payload
  la t0, scc_ctx
  mv t1, t0; li t2, 24
.Lscc_zero:
  sd zero, 0(t1); addi t1, t1, 8; addi t2, t2, -1; bnez t2, .Lscc_zero
  li t1, 30000000
  sd t1, 40(t0)
  la t1, ssc_calldata_ptr; ld t1, 0(t1); sd t1, 56(t0)
  la t1, ssc_calldata_len; ld t1, 0(t1); sd t1, 64(t0)
  addi t1, t0, 72; mv t2, s0; li t3, 20
.Lscc_recip:
  beqz t3, .Lscc_recip_d
  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, 1; addi t1, t1, 1; addi t3, t3, -1; j .Lscc_recip
.Lscc_recip_d:
  addi t1, s2, 7; andi t1, t1, -8
  la t0, ssc_calldata_len; ld t2, 0(t0); addi t2, t2, 7; andi t2, t2, -8; add t1, t1, t2
  la t0, m29_stage_count; ld t2, 0(t0); slli t2, t2, 5; add t1, t1, t2
  la t0, svf_parent_rlp_len; ld t2, 0(t0); add t1, t1, t2
  la t0, svf_witness_len; ld t2, 0(t0); add t1, t1, t2
  la t0, svf_codes_len; ld t2, 0(t0); add t1, t1, t2
  addi t1, t1, 584; li t2, 6940672; bgtu t1, t2, .Lscc_toobig
  la a0, scc_ctx
  mv a1, s4
  mv a2, s3
  mv a3, s1
  mv a4, s2
  li a5, 0; li a6, 0
  jal ra, stage_runtime_payload_code
  bnez a0, .Lscc_ret
  mv a0, s4
  la t0, svf_parent_rlp; ld a1, 0(t0); la t0, svf_parent_rlp_len; ld a2, 0(t0)
  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)
  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)
  jal ra, stage_runtime_payload_witness_context
  la t5, srpc_env_base; ld t1, 0(t5)
  add t2, s4, t1
  la t3, scc_system_addr; addi t4, t2, 64; li t5, 0
.Lscc_caller:
  li t6, 20; beq t5, t6, .Lscc_caller_d
  add a5, t3, t5; lbu a6, 0(a5); li a5, 19; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lscc_caller
.Lscc_caller_d:
  addi t4, t2, 128; li t5, 0
.Lscc_origin:
  li t6, 20; beq t5, t6, .Lscc_origin_d
  add a5, t3, t5; lbu a6, 0(a5); li a5, 19; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lscc_origin
.Lscc_origin_d:
  li a0, 0
  j .Lscc_ret
.Lscc_toobig:
  li a0, 1
.Lscc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
