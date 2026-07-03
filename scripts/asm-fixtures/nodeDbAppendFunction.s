node_db_append:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # node ptr
  mv s1, a1                   # node len
  # keccak(node) -> mset_db_hash
  mv a0, s0; mv a1, s1; la a2, mset_db_hash
  jal ra, zkvm_keccak256
  la t0, mset_db_top; ld s2, 0(t0)   # dst record ptr
  la t1, mset_db_hash
  ld t2,  0(t1); sd t2,  0(s2)
  ld t2,  8(t1); sd t2,  8(s2)
  ld t2, 16(t1); sd t2, 16(s2)
  ld t2, 24(t1); sd t2, 24(s2)
  sd s1, 32(s2)               # len
  addi a0, s2, 40             # dst bytes
  mv a1, s0; mv a2, s1
  jal ra, mset_memcpy
  # advance top by 40 + roundup8(len)
  addi t0, s1, 7; andi t0, t0, -8; addi t0, t0, 40
  add s2, s2, t0
  la t1, mset_db_top; sd s2, 0(t1)
  la t1, mset_db_count; ld t2, 0(t1); addi t2, t2, 1; sd t2, 0(t1)
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
