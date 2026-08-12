witness_codes_index_build:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  la t0, wcidx_enabled; sd zero, 0(t0)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section len
  la t0, wcidx_build_status; sd zero, 0(t0)
  la t0, wcidx_build_section_len; sd s1, 0(t0)
  la t0, wcidx_build_count; sd zero, 0(t0)
  la t0, wclh_lookup_calls; sd zero, 0(t0)
  la t0, wclh_indexed_calls; sd zero, 0(t0)
  la t0, wclh_indexed_hits; sd zero, 0(t0)
  la t0, wclh_indexed_misses; sd zero, 0(t0)
  la t0, wclh_linear_calls; sd zero, 0(t0)
  la t0, wclh_linear_hits; sd zero, 0(t0)
  la t0, wclh_linear_misses; sd zero, 0(t0)
  la t0, wclh_linear_iterations; sd zero, 0(t0)
  la t0, wclh_linear_last_section_len; sd zero, 0(t0)
  la t0, wclh_linear_max_section_len; sd zero, 0(t0)
  beqz s1, .Lwcidx_build_empty
  li t0, 4; bltu s1, t0, .Lwcidx_build_fail
  lwu t0, 0(s0)              # first offset = 4*N
  andi t1, t0, 3; bnez t1, .Lwcidx_build_fail
  bgtu t0, s1, .Lwcidx_build_fail
  srli s2, t0, 2             # count
  la t1, wcidx_build_count; sd s2, 0(t1)
  li t1, 131072
  bgtu s2, t1, .Lwcidx_build_fail
  mv s3, t0                  # first data offset, lower bound
  li s4, 0                   # i
.Lwcidx_build_loop:
  beq s4, s2, .Lwcidx_build_sort
  slli t0, s4, 2
  add t1, s0, t0
  lwu s5, 0(t1)              # offset_i
  bltu s5, s3, .Lwcidx_build_fail
  bgtu s5, s1, .Lwcidx_build_fail
  addi t2, s4, 1
  beq t2, s2, .Lwcidx_build_last
  slli t3, t2, 2
  add t3, s0, t3
  lwu s6, 0(t3)              # offset_{i+1}
  bgtu s6, s1, .Lwcidx_build_fail
  j .Lwcidx_build_have_end
.Lwcidx_build_last:
  mv s6, s1
.Lwcidx_build_have_end:
  bltu s6, s5, .Lwcidx_build_fail
  sub s7, s6, s5             # element len
  mv a0, s4; jal ra, wcidx_record_ptr; mv s8, a0
  add a0, s0, s5
  mv a1, s7
  mv a2, s8
  jal ra, zkvm_keccak256
  sd s5, 32(s8)
  sd s7, 40(s8)
  addi s4, s4, 1
  j .Lwcidx_build_loop
.Lwcidx_build_empty:
  li s2, 0
.Lwcidx_build_sort:
  li t0, 2; bltu s2, t0, .Lwcidx_build_enable
  srli s4, s2, 1
.Lwcidx_heapify:
  beqz s4, .Lwcidx_extract_init
  addi s4, s4, -1
  mv a0, s4; mv a1, s2; jal ra, wcidx_sift_down
  j .Lwcidx_heapify
.Lwcidx_extract_init:
  mv s4, s2
.Lwcidx_extract:
  li t0, 1; bleu s4, t0, .Lwcidx_build_enable
  addi s4, s4, -1
  li a0, 0; jal ra, wcidx_record_ptr; mv s8, a0
  mv a0, s4; jal ra, wcidx_record_ptr; mv s9, a0
  mv a0, s8; mv a1, s9; jal ra, wcidx_swap_records
  li a0, 0; mv a1, s4; jal ra, wcidx_sift_down
  j .Lwcidx_extract
.Lwcidx_build_enable:
  la t0, wcidx_section_ptr; sd s0, 0(t0)
  la t0, wcidx_section_len; sd s1, 0(t0)
  la t0, wcidx_count; sd s2, 0(t0)
  li t1, 1; la t0, wcidx_enabled; sd t1, 0(t0)
  li a0, 0
  j .Lwcidx_build_ret
.Lwcidx_build_fail:
  li t1, 1; la t0, wcidx_build_status; sd t1, 0(t0)
  li a0, 1
.Lwcidx_build_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
