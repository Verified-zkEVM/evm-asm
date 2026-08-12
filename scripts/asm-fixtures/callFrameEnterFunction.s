call_frame_enter:
  addi sp, sp, -16
  sd ra, 0(sp); sd s0, 8(sp)
  la t0, evm_sparse_memory_next_epoch
  ld t1, 0(t0)
  addi t2, t1, 1
  sd t2, 0(t0)
  la t0, evm_sparse_memory_epoch_by_depth
  slli t2, a0, 3
  add t0, t0, t2
  sd t1, 0(t0)
  jal ra, frame_base                 # a0 = call_frame_arena + d*0x19000
  mv s0, a0                          # s0 = child slot base
  la t0, evm_call_depth; ld t1, 0(t0)
  li t2, 1; beq t1, t2, .Lcfe_pool_first
  la t0, frame_parent_bases; slli t1, t1, 4; add t0, t0, t1
  ld t1, 0(t0); ld t2, 8(t0); ld t2, 488(t2); add a0, t1, t2
  j .Lcfe_pool_have
.Lcfe_pool_first:
  la a0, evm_memory_pool
.Lcfe_pool_have:
  li t0, 0x8200
  add a1, s0, t0                     # x12 = base + frameStackTopOff
  li t0, 0x18400
  add a2, s0, t0                     # x20 = base + frameEnvOff
  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16
  ret
