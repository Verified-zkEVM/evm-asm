slot_tuple_sequences_match:
  bne a1, a3, .Lstsm_bad        # length mismatch -> reject
  li t0, 0                      # i
.Lstsm_loop:
  beq t0, a1, .Lstsm_ok
  slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2   # i*40
  add t3, a0, t1                # BAL record i
  add t4, a2, t1                # exec record i
  ld t5, 0(t3);  ld t6, 0(t4);  bne t5, t6, .Lstsm_bad   # block_access_index
  ld t5, 8(t3);  ld t6, 8(t4);  bne t5, t6, .Lstsm_bad   # value[0:8]
  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lstsm_bad   # value[8:16]
  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lstsm_bad   # value[16:24]
  ld t5, 32(t3); ld t6, 32(t4); bne t5, t6, .Lstsm_bad   # value[24:32]
  addi t0, t0, 1; j .Lstsm_loop
.Lstsm_ok:
  li a0, 0; ret
.Lstsm_bad:
  li a0, 1; ret
