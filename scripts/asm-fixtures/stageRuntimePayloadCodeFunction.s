stage_runtime_payload_code:
  addi sp, sp, -72
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a1                    # output payload ptr
  mv s1, a0                    # context record
  mv s2, a2                    # exec payload
  mv s3, a3                    # code ptr
  mv s4, a4                    # code length
  mv s6, a5                    # storage preload ptr (count x 64B (key,value))
  mv s7, a6                    # storage preload count
  ld t0, 0(s1)                 # context status
  beqz t0, .Lsrpc_supported
  li a0, 1
  j .Lsrpc_ret
.Lsrpc_supported:
  addi t0, s4, 7; andi t0, t0, -8     # t0 = cb (padded code length)
  ld a7, 64(s1)                       # a7 = calldata length (ctx data len)
  addi t6, a7, 7; andi t6, t6, -8     # t6 = cd_pad (padded calldata length)
  slli a6, s7, 6                      # a6 = storage bytes = count*64
  add t1, t0, t6                      # t1 = co = cb + cd_pad
  add t1, t1, a6; addi t1, t1, 80     # t1 = env_base = 80 + co + count*64
  la t5, m28_blob_stage_count; ld t5, 0(t5); slli t5, t5, 5; add t1, t1, t5
  la t5, m29_stage_count; ld t5, 0(t5); slli t5, t5, 5; add t1, t1, t5
  la t5, srpc_env_base; sd t1, 0(t5)
  addi t2, t1, 504                    # t2 = total payload bytes
  addi t2, t2, 7; andi t2, t2, -8
  mv t3, s0
.Lsrpc_zero:
  beqz t2, .Lsrpc_zero_done
  sd zero, 0(t3); addi t3, t3, 8; addi t2, t2, -8; j .Lsrpc_zero
.Lsrpc_zero_done:
  sd s4, 0(s0)
  addi t3, s0, 8; mv t4, s3; mv t5, s4
.Lsrpc_copy:
  beqz t5, .Lsrpc_copy_done
  lbu t6, 0(t4); sb t6, 0(t3); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lsrpc_copy
.Lsrpc_copy_done:
  add t3, s0, t0               # t3 = s0 + cb
  ld a7, 64(s1); sd a7, 8(t3)  # calldata-len @ +8+cb
  addi t3, t3, 16              # t3 = dst = s0 + cb + 16 (calldata bytes)
  ld t4, 56(s1); mv t5, a7     # src = ctx data ptr, bytes = calldata len
.Lsrpc_cdcopy:
  beqz t5, .Lsrpc_cdcopy_done
  lbu t6, 0(t4); sb t6, 0(t3); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lsrpc_cdcopy
.Lsrpc_cdcopy_done:
  add t3, s0, t0               # s0 + cb
  ld a7, 64(s1); addi t6, a7, 7; andi t6, t6, -8   # cd_pad
  add t3, t3, t6               # t3 = s0 + co
  sd s7, 16(t3)                # slot_count @ +16+co
  addi t3, t3, 24              # t3 = dst = s0 + co + 24 (storage pairs)
  mv t4, s6; slli t5, s7, 6    # src, bytes = count*64
.Lsrpc_scopy:
  beqz t5, .Lsrpc_scopy_done
  lbu t6, 0(t4); sb t6, 0(t3); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lsrpc_scopy
.Lsrpc_scopy_done:
  mv s5, t3
  addi a0, s2, 520; jal ra, bgv_u64le
  mv a1, s5; jal ra, amsterdam_blob_gas_price_u256
  mv t3, s5
  la t4, m28_blob_stage_count; ld t0, 0(t4); sd t0, 32(t3)
  addi t4, t3, 40; la t5, m28_blob_stage_table; slli t6, t0, 5
.Lsrpc_blob:
  beqz t6, .Lsrpc_blob_done
  lbu a5, 0(t5); sb a5, 0(t4); addi t5, t5, 1; addi t4, t4, 1; addi t6, t6, -1; j .Lsrpc_blob
.Lsrpc_blob_done:
  slli t0, t0, 5
  la t4, m29_stage_cur;   ld t5, 0(t4); add t4, t3, t0; sd t5, 40(t4)
  la t4, m29_stage_count; ld t6, 0(t4); add t4, t3, t0; sd t6, 48(t4)
  add t4, t3, t0; addi t4, t4, 56; la t5, m29_stage_table; slli t6, t6, 5
.Lsrpc_m29:
  beqz t6, .Lsrpc_m29_done
  lbu a5, 0(t5); sb a5, 0(t4); addi t5, t5, 1; addi t4, t4, 1; addi t6, t6, -1; j .Lsrpc_m29
.Lsrpc_m29_done:
  la t1, srpc_env_base; ld t1, 0(t1)     # reload env_base after helper calls
  add s5, s0, t1               # s5 = &env_words (env_base)
  addi t3, s2, 32; addi t4, s5, 192; li t5, 0
.Lsrpc_cb:
  li t6, 20; beq t5, t6, .Lsrpc_cb_done
  add a5, t3, t5; lbu a6, 0(a5); li a5, 19; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_cb
.Lsrpc_cb_done:
  ld t3, 404(s2); sd t3, 256(s5)
  ld t3, 428(s2); sd t3, 224(s5)
  addi t3, s2, 372; addi t4, s5, 288; li t5, 0
.Lsrpc_prevrandao_loop:
  li t6, 32; beq t5, t6, .Lsrpc_prevrandao_done
  add a5, t3, t5; lbu a6, 0(a5)
  li a5, 31; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5)
  addi t5, t5, 1; j .Lsrpc_prevrandao_loop
.Lsrpc_prevrandao_done:
  ld t3, 412(s2); sd t3, 320(s5)
  addi t3, s2, 440
  ld t4, 0(t3); sd t4, 352(s5); ld t4, 8(t3); sd t4, 360(s5)
  ld t4, 16(t3); sd t4, 368(s5); ld t4, 24(t3); sd t4, 376(s5)
  la t3, bv_chain_id; ld t4, 0(t3); sd t4, 384(s5)
  addi t3, s1, 72; mv t4, s5; li t5, 0
.Lsrpc_ad:
  li t6, 20; beq t5, t6, .Lsrpc_ad_done
  li a5, 19; sub a5, a5, t5; add a5, t3, a5; lbu a6, 0(a5); add a5, t4, t5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_ad
.Lsrpc_ad_done:
  addi t3, s1, 96; addi t4, s5, 96; li t5, 0
.Lsrpc_cv:
  li t6, 32; beq t5, t6, .Lsrpc_cv_done
  add a5, t3, t5; lbu a6, 0(a5); li a5, 31; sub a5, a5, t5; add a5, t4, a5; sb a6, 0(a5); addi t5, t5, 1; j .Lsrpc_cv
.Lsrpc_cv_done:
  li t3, 0; li t4, 0
.Lsrpc_slot:
  li t5, 8; beq t4, t5, .Lsrpc_slot_done
  add t5, s2, t4; addi t5, t5, 532; lbu t6, 0(t5); slli a5, t4, 3; sll t6, t6, a5; or t3, t3, t6
  addi t4, t4, 1; j .Lsrpc_slot
.Lsrpc_slot_done:
  sd t3, 416(s5)                       # SLOTNUM limb0 = slot_number (u64 LE)
  ld t3, 40(s1); sd t3, 448(s5)        # gas limit (ctx tx gas)
  li t3, 1; sd t3, 456(s5)             # validate_tx_gas = 1
  ld t3, 48(s1); sd t3, 464(s5)        # is_creation
  li a0, 0
.Lsrpc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)
  ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 72
  ret
