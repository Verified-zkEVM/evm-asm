public_keys_valid:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a0                   # SSZ_BASE
  mv s1, a1                   # exec_payload
  # tx_count from the SSZ transactions list.
  addi a0, s1, 504; jal ra, bgv_u32le
  mv s2, a0                   # transactions_offset
  addi a0, s1, 508; jal ra, bgv_u32le
  mv s3, a0                   # withdrawals_offset
  li s4, 0                    # tx_count
  bleu s3, s2, .Lpkv_have_tx_count
  sub t0, s3, s2
  li t1, 4; bltu t0, t1, .Lpkv_fail
  add t2, s1, s2
  mv a0, t2; jal ra, bgv_u32le
  andi t1, a0, 3; bnez t1, .Lpkv_fail
  srli s4, a0, 2
  slli t1, s4, 2; bgtu t1, t0, .Lpkv_fail
.Lpkv_have_tx_count:
  # public_keys start = SSZ_BASE + outer.offsets[3]. End = zisk input
  # payload start + host length; host length includes schema id + SSZ bytes.
  addi a0, s0, 12; jal ra, bgv_u32le
  add s5, s0, a0              # public_keys ptr
  li a0, 0x40000008; jal ra, bgv_u64le
  li t0, 0x40000010; add s6, t0, a0     # end of host payload
  bltu s6, s5, .Lpkv_fail
  sub s7, s6, s5              # public_keys byte length
  li t0, 65
  remu t1, s7, t0; bnez t1, .Lpkv_fail
  divu s8, s7, t0             # public key count
  bne s8, s4, .Lpkv_fail
  la t0, bv_public_keys_ptr; sd s5, 0(t0)
  la t0, bv_public_keys_len; sd s7, 0(t0)
  li s9, 0
.Lpkv_loop:
  beq s9, s4, .Lpkv_ok
  li t0, 65; mul t1, s9, t0; add t2, s5, t1
  lbu t3, 0(t2); li t4, 4; bne t3, t4, .Lpkv_fail
  li t3, 1; li t4, 0
.Lpkv_coord_loop:
  li t5, 65; beq t3, t5, .Lpkv_coord_done
  add t6, t2, t3; lbu t6, 0(t6); or t4, t4, t6
  addi t3, t3, 1; j .Lpkv_coord_loop
.Lpkv_coord_done:
  beqz t4, .Lpkv_fail
  addi s9, s9, 1; j .Lpkv_loop
.Lpkv_ok:
  li a0, 0; j .Lpkv_ret
.Lpkv_fail:
  li a0, 1
.Lpkv_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
