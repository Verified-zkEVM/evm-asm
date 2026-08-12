blob_gas_used_from_versioned_hashes:
  addi sp, sp, -24
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a2                   # gas_per_blob
  mv s1, a3                   # out ptr
  la a2, bgvh_count_scratch
  jal ra, rlp_list_count_items
  bnez a0, .Lbgvh_fail
  la t0, bgvh_count_scratch; ld t1, 0(t0)
  mul t2, t1, s0
  sd t2, 0(s1)
  li a0, 0
  j .Lbgvh_ret
.Lbgvh_fail:
  sd zero, 0(s1)
  li a0, 1
.Lbgvh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 24
  ret
