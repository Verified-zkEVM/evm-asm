code_read_fetch:
  addi sp, sp, -64
  sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp)
  sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp)
  la t0, ecc_empty_code_hash
  li t1, 0
.Lcrf_empty_cmp:
  li t2, 32; beq t1, t2, .Lcrf_skip
  add t2, t0, t1; lbu t2, 0(t2)
  add t3, a2, t1; lbu t3, 0(t3)
  bne t2, t3, .Lcrf_record
  addi t1, t1, 1; j .Lcrf_empty_cmp
.Lcrf_record:
  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0)
  ld a2, 24(sp)               # code-hash ptr (saved a2)
  jal ra, find_code_effect_by_hash
  mv t1, a0
  ld a5, 48(sp)
  ld a2, 24(sp)
  bnez t1, .Lcrf_skip
  mv a0, a5
  mv a1, a2
  jal ra, code_read_record
.Lcrf_skip:
  ld ra, 0(sp); ld a0, 8(sp); ld a1, 16(sp); ld a2, 24(sp)
  ld a3, 32(sp); ld a4, 40(sp); ld a5, 48(sp)
  addi sp, sp, 64
  j witness_codes_lookup_by_hash
