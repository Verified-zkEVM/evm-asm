stage_runtime_payload_witness_context:
  la t0, srpc_env_base; ld t1, 0(t0); add t0, a0, t1
  sd a2, 472(t0); sd a4, 480(t0); sd a6, 488(t0)
  addi t2, t0, 496
  mv t0, a1; mv t1, a2
.Lsrpwc_header:
  beqz t1, .Lsrpwc_state_start
  lbu t3, 0(t0); sb t3, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lsrpwc_header
.Lsrpwc_state_start:
  mv t0, a3; mv t1, a4
.Lsrpwc_state:
  beqz t1, .Lsrpwc_codes_start
  lbu t3, 0(t0); sb t3, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lsrpwc_state
.Lsrpwc_codes_start:
  mv t0, a5; mv t1, a6
.Lsrpwc_codes:
  beqz t1, .Lsrpwc_done
  lbu t3, 0(t0); sb t3, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lsrpwc_codes
.Lsrpwc_done:
  ret
