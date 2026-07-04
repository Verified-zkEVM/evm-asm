ssz_hash_tree_root_list_bytelist:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # s0 = section ptr
  mv s1, a1                  # s1 = section_len
  mv s2, a2                  # s2 = byte_log2
  mv s3, a3                  # s3 = count_log2
  mv s4, a4                  # s4 = out ptr
  beqz s1, .Lszls_N0          # empty section ⇒ N = 0
  lbu t0, 0(s0)              # offset_0 = 4*N (LBU-packed: section ptr may be unaligned)
  lbu t5, 1(s0); slli t5, t5, 8;  or t0, t0, t5
  lbu t5, 2(s0); slli t5, t5, 16; or t0, t0, t5
  lbu t5, 3(s0); slli t5, t5, 24; or t0, t0, t5
  andi t5, t0, 3
  bnez t5, .Lszls_fail       # offset_0 must equal 4*N
  srli s5, t0, 2             # s5 = N (element count)
  beqz s5, .Lszls_fail       # non-empty section cannot encode an empty list
  li t5, 4096
  bltu t5, s5, .Lszls_fail   # child root scratch is 4096 roots
  bltu s1, t0, .Lszls_fail   # offset table must fit in section
  li s6, 0                   # s6 = i (loop counter)
.Lszls_loop:
  beq s6, s5, .Lszls_done_loop
  slli t0, s6, 2             # 4*i
  add t1, s0, t0
  lbu t2, 0(t1)              # inner_off_i (LBU-packed)
  lbu t5, 1(t1); slli t5, t5, 8;  or t2, t2, t5
  lbu t5, 2(t1); slli t5, t5, 16; or t2, t2, t5
  lbu t5, 3(t1); slli t5, t5, 24; or t2, t2, t5
  slli t3, s5, 2
  bltu t2, t3, .Lszls_fail   # element data starts after offset table
  bltu s1, t2, .Lszls_fail   # element start must be in section
  add a0, s0, t2             # el_i_start
  addi t3, s6, 1
  beq t3, s5, .Lszls_use_end
  slli t3, t3, 2             # 4*(i+1)
  add t3, s0, t3
  lbu t4, 0(t3)              # inner_off_{i+1} (LBU-packed)
  lbu t5, 1(t3); slli t5, t5, 8;  or t4, t4, t5
  lbu t5, 2(t3); slli t5, t5, 16; or t4, t4, t5
  lbu t5, 3(t3); slli t5, t5, 24; or t4, t4, t5
  bltu t4, t2, .Lszls_fail   # offsets must be monotone
  bltu s1, t4, .Lszls_fail   # next element start must be in section
  add t4, s0, t4             # el_i_end
  j .Lszls_have_end
.Lszls_use_end:
  add t4, s0, s1             # el_i_end = section_end
.Lszls_have_end:
  sub a1, t4, a0             # el_i_len
  li t1, 32
  sll t1, t1, s2             # declared ByteList byte capacity
  bltu t1, a1, .Lszls_fail   # reject element longer than ByteList[B]
  li t0, 0x200000
  bltu t0, a1, .Lszls_fail   # ssz_hash_tree_root_bytes scratch supports <=2MiB
  mv a2, s2                  # byte_log2
  la a3, ssz_ltb_child_roots
  slli t0, s6, 5             # 32*i
  add a3, a3, t0             # &child_roots[i]
  jal ra, ssz_hash_tree_root_bytes
  bnez a0, .Lszls_fail
  addi s6, s6, 1
  j .Lszls_loop
.Lszls_done_loop:
  la a0, ssz_ltb_child_roots
  mv a1, s5                  # N
  mv a2, s3                  # count_log2
  la a3, ssz_ltb_partial
  jal ra, ssz_merkleize
  la t0, ssz_ltb_partial
  la t1, ssz_ltb_mix
  ld t2,  0(t0); sd t2,  0(t1)
  ld t2,  8(t0); sd t2,  8(t1)
  ld t2, 16(t0); sd t2, 16(t1)
  ld t2, 24(t0); sd t2, 24(t1)
  sd s5, 32(t1)              # length = N (u64 LE)
  sd zero, 40(t1)
  sd zero, 48(t1)
  sd zero, 56(t1)
  la a0, ssz_ltb_mix
  li a1, 64
  mv a2, s4
  jal ra, zkvm_sha256
  j .Lszls_ret
.Lszls_N0:
  la t0, ssz_zero_hashes
  slli t1, s3, 5
  add t0, t0, t1             # &Z_{count_log2}
  la t1, ssz_ltb_mix
  ld t2,  0(t0); sd t2,  0(t1)
  ld t2,  8(t0); sd t2,  8(t1)
  ld t2, 16(t0); sd t2, 16(t1)
  ld t2, 24(t0); sd t2, 24(t1)
  sd zero, 32(t1); sd zero, 40(t1)
  sd zero, 48(t1); sd zero, 56(t1)
  la a0, ssz_ltb_mix
  li a1, 64
  mv a2, s4
  jal ra, zkvm_sha256
.Lszls_ret:
  li a0, 0
  j .Lszls_restore
.Lszls_fail:
  sd zero,  0(s4)
  sd zero,  8(s4)
  sd zero, 16(s4)
  sd zero, 24(s4)
  li a0, 1
.Lszls_restore:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
