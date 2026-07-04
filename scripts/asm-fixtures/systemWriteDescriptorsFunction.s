system_write_descriptors:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # SSZ_BASE
  addi s1, s0, 60             # exec_payload
  # ---- EIP-2935: slot = (number-1) % 8191, value = parent_hash ----
  addi a0, s1, 404; jal ra, swd_read_u64le
  addi a0, a0, -1             # number - 1
  li t0, 8191; remu a0, a0, t0
  la a1, swd_2935_slot; jal ra, swd_write_be32_u64
  mv a0, s1; li a1, 32; la a2, swd_2935_val; la a3, swd_2935_vlen
  jal ra, swd_minimal_copy
  # ---- EIP-4788: slot = timestamp % 8191, value = timestamp ----
  addi a0, s1, 428; jal ra, swd_read_u64le
  mv s2, a0                   # timestamp
  li t0, 8191; remu a0, a0, t0
  la a1, swd_4788_slot; jal ra, swd_write_be32_u64
  mv a0, s2; la a1, swd_ts_be8; jal ra, swd_write_be8
  la a0, swd_ts_be8; li a1, 8; la a2, swd_4788_val; la a3, swd_4788_vlen
  jal ra, swd_minimal_copy
  # ---- EIP-4788: slot = timestamp + 8191, value = parent_beacon_block_root ----
  mv a0, s2; li t0, 8191; remu a0, a0, t0; add a0, a0, t0
  la a1, swd_4788_root_slot; jal ra, swd_write_be32_u64
  addi a0, s0, 24; li a1, 32; la a2, swd_4788_root_val; la a3, swd_4788_root_vlen
  jal ra, swd_minimal_copy
  li a0, 0
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
