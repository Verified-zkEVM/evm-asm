chain_config_valid:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # SSZ_BASE
  mv s1, a1                   # exec_payload
  addi a0, s0, 8; jal ra, bgv_u32le
  add s2, s0, a0              # chain_config ptr
  mv a0, s2; jal ra, bgv_u64le
  la t0, bv_chain_id; sd a0, 0(t0)
  addi a0, s0, 12; jal ra, bgv_u32le
  add s3, s0, a0              # public_keys ptr = chain_config end
  bltu s3, s2, .Lccv_fail
  sub t0, s3, s2; li t1, 12; bltu t0, t1, .Lccv_fail
  addi a0, s2, 8; jal ra, bgv_u32le
  li t0, 12; bne a0, t0, .Lccv_fail
  add s4, s2, a0              # active_fork (fork_config) ptr
  bltu s3, s4, .Lccv_fail
  sub s10, s3, s4             # fork_config len (4-byte offset table + activation)
  li t0, 12; bltu s10, t0, .Lccv_fail
  mv a0, s4; jal ra, bgv_u32le
  li t0, 4; bne a0, t0, .Lccv_fail   # offset_activation == 4
  addi s5, s4, 4              # activation ptr
  addi s6, s10, -4            # activation len
  li t0, 8; beq s6, t0, .Lccv_fail
  li t0, 16; beq s6, t0, .Lccv_activation_len16
  li t0, 24; beq s6, t0, .Lccv_activation_len24
  j .Lccv_fail
.Lccv_activation_len16:
  addi a0, s5, 0; jal ra, bgv_u32le
  li t0, 8; bne a0, t0, .Lccv_fail
  addi a0, s5, 4; jal ra, bgv_u32le
  li t0, 8; beq a0, t0, .Lccv_check_ts_at8
  li t0, 16; beq a0, t0, .Lccv_check_bn_at8
  j .Lccv_fail
.Lccv_activation_len24:
  addi a0, s5, 0; jal ra, bgv_u32le
  li t0, 8; bne a0, t0, .Lccv_fail
  addi a0, s5, 4; jal ra, bgv_u32le
  li t0, 16; bne a0, t0, .Lccv_fail
  addi a0, s5, 8; jal ra, bgv_u64le
  mv s9, a0
  addi a0, s1, 404; jal ra, bgv_u64le
  bltu a0, s9, .Lccv_fail
  addi a0, s5, 16; jal ra, bgv_u64le
  mv s9, a0
  addi a0, s1, 428; jal ra, bgv_u64le
  bltu a0, s9, .Lccv_fail
  j .Lccv_activation_ok
.Lccv_check_bn_at8:
  addi a0, s5, 8; jal ra, bgv_u64le
  mv s9, a0
  addi a0, s1, 404; jal ra, bgv_u64le
  bltu a0, s9, .Lccv_fail
  j .Lccv_activation_ok
.Lccv_check_ts_at8:
  addi a0, s5, 8; jal ra, bgv_u64le
  mv s9, a0
  addi a0, s1, 428; jal ra, bgv_u64le
  bltu a0, s9, .Lccv_fail
.Lccv_activation_ok:
  li a0, 0; j .Lccv_ret
.Lccv_fail:
  li a0, 1
.Lccv_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
