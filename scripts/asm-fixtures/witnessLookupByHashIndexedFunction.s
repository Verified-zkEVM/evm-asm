witness_lookup_by_hash_indexed:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a2                  # target hash
  mv s1, a3                  # out offset
  mv s2, a4                  # out length
  li s3, 0                   # lo
  la t0, widx_count; ld s4, 0(t0) # hi
.Lwidx_lookup_loop:
  bgeu s3, s4, .Lwidx_lookup_miss
  add s5, s3, s4
  srli s5, s5, 1             # mid
  mv a0, s5; jal ra, widx_record_ptr; mv s6, a0
  mv a0, s6; mv a1, s0; jal ra, widx_cmp32
  li t0, 1; beq a0, t0, .Lwidx_lookup_hit
  li t0, 0; beq a0, t0, .Lwidx_lookup_less
  mv s4, s5
  j .Lwidx_lookup_loop
.Lwidx_lookup_less:
  addi s3, s5, 1
  j .Lwidx_lookup_loop
.Lwidx_lookup_hit:
  ld t0, 32(s6); sd t0, 0(s1)
  ld t0, 40(s6); sd t0, 0(s2)
  li a0, 0
  j .Lwidx_lookup_ret
.Lwidx_lookup_miss:
  li a0, 1
.Lwidx_lookup_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
