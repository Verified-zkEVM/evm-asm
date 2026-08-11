witness_lookup_by_hash:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section_len
  mv s2, a2                  # target_hash ptr
  mv s3, a3                  # out_offset ptr
  mv s4, a4                  # out_length ptr
  la t0, wlh_lookup_calls; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  la t0, widx_enabled
  ld t0, 0(t0)
  beqz t0, .Lwlh_linear
  la t0, widx_section_ptr
  ld t0, 0(t0)
  bne s0, t0, .Lwlh_linear
  la t0, widx_section_len
  ld t0, 0(t0)
  bne s1, t0, .Lwlh_linear
  mv a0, s0
  mv a1, s1
  mv a2, s2
  mv a3, s3
  mv a4, s4
  la t0, wlh_indexed_calls; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  jal ra, witness_lookup_by_hash_indexed
  bnez a0, .Lwlh_indexed_miss_count
  la t0, wlh_indexed_hits; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  j .Lwlh_ret
.Lwlh_indexed_miss_count:
  la t0, wlh_indexed_misses; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  j .Lwlh_ret
.Lwlh_linear:
  la t0, wlh_linear_calls; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  la t0, wlh_linear_last_section_len; sd s1, 0(t0)
  la t0, wlh_linear_max_section_len; ld t1, 0(t0); bgeu t1, s1, .Lwlh_linear_max_done
  sd s1, 0(t0)
.Lwlh_linear_max_done:
  beqz s1, .Lwlh_miss        # empty section ⇒ miss
  li t0, 4
  bltu s1, t0, .Lwlh_miss    # too short for an offsets table
  lwu t0, 0(s0)              # first inner offset = 4 * N
  andi t1, t0, 3
  bnez t1, .Lwlh_miss        # misaligned offsets table ⇒ malformed
  bgtu t0, s1, .Lwlh_miss    # first offset past the section
  srli s5, t0, 2             # s5 = N
  li s6, 0                   # s6 = i
.Lwlh_loop:
  beq s6, s5, .Lwlh_miss
  # Compute element i bounds (every offset validated against the
  # section bounds — a malformed table must surface as a miss, not a
  # runaway keccak length; see the widx_build twin checks).
  slli t0, s6, 2             # 4*i
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  bgtu t2, s1, .Lwlh_miss    # offset past the section
  add a0, s0, t2             # el_i_start
  addi t3, s6, 1
  beq t3, s5, .Lwlh_use_end
  slli t3, t3, 2             # 4*(i+1)
  add t3, s0, t3
  lwu t4, 0(t3)
  bgtu t4, s1, .Lwlh_miss    # next offset past the section
  add t4, s0, t4             # el_i_end
  j .Lwlh_have_end
.Lwlh_use_end:
  add t4, s0, s1             # el_i_end = section_end
.Lwlh_have_end:
  bltu t4, a0, .Lwlh_miss    # descending offsets ⇒ malformed
  sub a1, t4, a0             # el_i_len
  la a2, wlh_scratch_hash
  la t0, wlh_linear_iterations; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  jal ra, zkvm_keccak256
  # Compare scratch_hash vs target_hash.
  la t0, wlh_scratch_hash
  mv t1, s2
  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwlh_no_match
  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwlh_no_match
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwlh_no_match
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwlh_no_match
  # Match. Recompute (offset, length) from i (clobbered above).
  slli t0, s6, 2
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  sd t2, 0(s3)               # *out_offset = inner_off_i
  addi t3, s6, 1
  beq t3, s5, .Lwlh_last_len
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  sub t4, t4, t2             # length = inner_off_{i+1} - inner_off_i
  j .Lwlh_store_len
.Lwlh_last_len:
  sub t4, s1, t2             # length = section_len - inner_off_i
.Lwlh_store_len:
  sd t4, 0(s4)
  la t0, wlh_linear_hits; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  li a0, 0                   # hit
  j .Lwlh_ret
.Lwlh_no_match:
  addi s6, s6, 1
  j .Lwlh_loop
.Lwlh_miss:
  la t0, wlh_linear_misses; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  li a0, 1                   # miss
.Lwlh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
