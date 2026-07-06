mpt_node_resolve:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  mv a0, s2; mv a1, s3; mv a2, s4
  jal ra, node_db_lookup
  beqz a0, .Lres_ret
  # Direct-mapped cache for witness-section resolutions. DB lookup wins;
  # the cache only avoids repeated scans of the immutable witness list.
  lbu t0, 0(s2)
  lbu t1, 1(s2); slli t1, t1, 8; or t0, t0, t1; li t2, 4095; and t0, t0, t2
  la t1, mset_res_cache_valid
  slli t2, t0, 3; add t1, t1, t2
  ld t2, 0(t1); beqz t2, .Lres_cache_miss
  slli t2, t0, 5; slli t3, t0, 4; add t2, t2, t3   # 48 * index
  la t3, mset_res_cache_data; add t2, t3, t2
  ld t3,  0(t2); ld t4,  0(s2); bne t3, t4, .Lres_cache_miss
  ld t3,  8(t2); ld t4,  8(s2); bne t3, t4, .Lres_cache_miss
  ld t3, 16(t2); ld t4, 16(s2); bne t3, t4, .Lres_cache_miss
  ld t3, 24(t2); ld t4, 24(s2); bne t3, t4, .Lres_cache_miss
  ld t3, 32(t2); sd t3, 0(s3)
  ld t3, 40(t2); sd t3, 0(s4)
  li a0, 0
  j .Lres_ret
.Lres_cache_miss:
  mv a0, s0; mv a1, s1; mv a2, s2
  la a3, mset_res_off; la a4, mset_res_len
  jal ra, witness_lookup_by_hash
  bnez a0, .Lres_ret
  la t0, mset_res_off; ld t1, 0(t0); add t1, s0, t1   # abs = witness + off
  sd t1, 0(s3)
  la t0, mset_res_len; ld t1, 0(t0); sd t1, 0(s4)
  lbu t0, 0(s2)
  lbu t1, 1(s2); slli t1, t1, 8; or t0, t0, t1; li t2, 4095; and t0, t0, t2
  slli t2, t0, 5; slli t3, t0, 4; add t2, t2, t3   # 48 * index
  la t3, mset_res_cache_data; add t2, t3, t2
  ld t3,  0(s2); sd t3,  0(t2)
  ld t3,  8(s2); sd t3,  8(t2)
  ld t3, 16(s2); sd t3, 16(t2)
  ld t3, 24(s2); sd t3, 24(t2)
  ld t3, 0(s3); sd t3, 32(t2)
  ld t3, 0(s4); sd t3, 40(t2)
  la t1, mset_res_cache_valid; slli t3, t0, 3; add t1, t1, t3; li t3, 1; sd t3, 0(t1)
  li a0, 0
.Lres_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
