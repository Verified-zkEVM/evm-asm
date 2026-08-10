/-
  EvmAsm.Codegen.Programs.MptWitnessIndex

  Raw-asm helper cluster for the stateless witness NodeDb index used by
  `witness_lookup_by_hash`. Kept separate from Mpt.lean to stay under the
  codegen file-size guard.
-/

namespace EvmAsm.Codegen

/-- Bytes stored per sorted witness-index record: 32-byte hash plus offset/len. -/
def mptWitnessIndexRecordBytes : Nat := 48

/-- Maximum `witness.state` records indexed by the stateless guest.

    The accepted `block_state_root` witness byte guard is 512 KiB. An SSZ
    `List[Bytes]` offset table uses four bytes per element, so the largest
    record count representable under that byte guard is 524288 / 4 = 131072.
    The backing arena is therefore about 6 MiB, well within the assumed ZisK RAM
    layout where input and RAM are separate regions. -/
def mptWitnessIndexCapacity : Nat := 524288 / 4

/-- Backing bytes reserved for `widx_records`. -/
def mptWitnessIndexArenaBytes : Nat :=
  mptWitnessIndexCapacity * mptWitnessIndexRecordBytes

/-- Sorted full-hash witness index helpers plus their private data labels.
    `witness_index_build(section_ptr, section_len)` computes one keccak per SSZ
    list entry, stores `(hash, offset, len)` records, and heapsorts them by the
    full 32-byte hash. `witness_lookup_by_hash_indexed` then does binary search.
    Capacity is `mptWitnessIndexCapacity`; larger sections fail conservatively
    at build. -/
def witnessIndexFunctions : String :=
  "\n" ++
  "widx_record_ptr:\n" ++
  "  slli t0, a0, 5             # i * 32\n" ++
  "  slli t1, a0, 4             # i * 16\n" ++
  "  add t0, t0, t1             # i * 48\n" ++
  "  la a0, widx_records\n" ++
  "  add a0, a0, t0\n" ++
  "  ret\n" ++
  "\n" ++
  "widx_cmp32:\n" ++
  "  li t0, 32\n" ++
  ".Lwidx_cmp_loop:\n" ++
  "  beqz t0, .Lwidx_cmp_eq\n" ++
  "  lbu t1, 0(a0)\n" ++
  "  lbu t2, 0(a1)\n" ++
  "  bltu t1, t2, .Lwidx_cmp_lt\n" ++
  "  bltu t2, t1, .Lwidx_cmp_gt\n" ++
  "  addi a0, a0, 1\n" ++
  "  addi a1, a1, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lwidx_cmp_loop\n" ++
  ".Lwidx_cmp_lt:\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lwidx_cmp_eq:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lwidx_cmp_gt:\n" ++
  "  li a0, 2\n" ++
  "  ret\n" ++
  "\n" ++
  "widx_swap_records:\n" ++
  "  beq a0, a1, .Lwidx_swap_ret\n" ++
  "  li t6, 6\n" ++
  ".Lwidx_swap_loop:\n" ++
  "  beqz t6, .Lwidx_swap_ret\n" ++
  "  ld t0, 0(a0)\n" ++
  "  ld t1, 0(a1)\n" ++
  "  sd t1, 0(a0)\n" ++
  "  sd t0, 0(a1)\n" ++
  "  addi a0, a0, 8\n" ++
  "  addi a1, a1, 8\n" ++
  "  addi t6, t6, -1\n" ++
  "  j .Lwidx_swap_loop\n" ++
  ".Lwidx_swap_ret:\n" ++
  "  ret\n" ++
  "\n" ++
  "widx_sift_down:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # root\n" ++
  "  mv s1, a1                  # heap count\n" ++
  ".Lwidx_sift_loop:\n" ++
  "  slli s2, s0, 1\n" ++
  "  addi s2, s2, 1             # left child\n" ++
  "  bgeu s2, s1, .Lwidx_sift_ret\n" ++
  "  mv s3, s0                  # best index\n" ++
  "  mv a0, s3; jal ra, widx_record_ptr; mv s4, a0\n" ++
  "  mv a0, s2; jal ra, widx_record_ptr; mv s5, a0\n" ++
  "  mv a0, s4; mv a1, s5; jal ra, widx_cmp32\n" ++
  "  li t0, 0; bne a0, t0, .Lwidx_left_done\n" ++
  "  mv s3, s2\n" ++
  ".Lwidx_left_done:\n" ++
  "  addi s6, s2, 1             # right child\n" ++
  "  bgeu s6, s1, .Lwidx_choose_done\n" ++
  "  mv a0, s3; jal ra, widx_record_ptr; mv s4, a0\n" ++
  "  mv a0, s6; jal ra, widx_record_ptr; mv s5, a0\n" ++
  "  mv a0, s4; mv a1, s5; jal ra, widx_cmp32\n" ++
  "  li t0, 0; bne a0, t0, .Lwidx_choose_done\n" ++
  "  mv s3, s6\n" ++
  ".Lwidx_choose_done:\n" ++
  "  beq s3, s0, .Lwidx_sift_ret\n" ++
  "  mv a0, s0; jal ra, widx_record_ptr; mv s4, a0\n" ++
  "  mv a0, s3; jal ra, widx_record_ptr; mv s5, a0\n" ++
  "  mv a0, s4; mv a1, s5; jal ra, widx_swap_records\n" ++
  "  mv s0, s3\n" ++
  "  j .Lwidx_sift_loop\n" ++
  ".Lwidx_sift_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  "\n" ++
  "witness_index_build:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  la t0, widx_enabled; sd zero, 0(t0)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section len\n" ++
  "  la t0, widx_build_status; sd zero, 0(t0)\n" ++
  "  la t0, widx_build_section_len; sd s1, 0(t0)\n" ++
  "  la t0, widx_build_count; sd zero, 0(t0)\n" ++
  "  la t0, wlh_lookup_calls; sd zero, 0(t0)\n" ++
  "  la t0, wlh_indexed_calls; sd zero, 0(t0)\n" ++
  "  la t0, wlh_indexed_hits; sd zero, 0(t0)\n" ++
  "  la t0, wlh_indexed_misses; sd zero, 0(t0)\n" ++
  "  la t0, wlh_linear_calls; sd zero, 0(t0)\n" ++
  "  la t0, wlh_linear_hits; sd zero, 0(t0)\n" ++
  "  la t0, wlh_linear_misses; sd zero, 0(t0)\n" ++
  "  la t0, wlh_linear_iterations; sd zero, 0(t0)\n" ++
  "  la t0, wlh_linear_last_section_len; sd zero, 0(t0)\n" ++
  "  la t0, wlh_linear_max_section_len; sd zero, 0(t0)\n" ++
  "  beqz s1, .Lwidx_build_empty\n" ++
  "  li t0, 4; bltu s1, t0, .Lwidx_build_fail\n" ++
  "  lwu t0, 0(s0)              # first offset = 4*N\n" ++
  "  andi t1, t0, 3; bnez t1, .Lwidx_build_fail\n" ++
  "  bgtu t0, s1, .Lwidx_build_fail\n" ++
  "  srli s2, t0, 2             # count\n" ++
  "  la t1, widx_build_count; sd s2, 0(t1)\n" ++
  "  li t1, " ++ toString mptWitnessIndexCapacity ++ "\n" ++
  "  bgtu s2, t1, .Lwidx_build_fail\n" ++
  "  mv s3, t0                  # first data offset, lower bound\n" ++
  "  li s4, 0                   # i\n" ++
  ".Lwidx_build_loop:\n" ++
  "  beq s4, s2, .Lwidx_build_sort\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu s5, 0(t1)              # offset_i\n" ++
  "  bltu s5, s3, .Lwidx_build_fail\n" ++
  "  bgtu s5, s1, .Lwidx_build_fail\n" ++
  "  addi t2, s4, 1\n" ++
  "  beq t2, s2, .Lwidx_build_last\n" ++
  "  slli t3, t2, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu s6, 0(t3)              # offset_{i+1}\n" ++
  "  bgtu s6, s1, .Lwidx_build_fail\n" ++  -- next offset past the section: malformed table
  "  j .Lwidx_build_have_end\n" ++
  ".Lwidx_build_last:\n" ++
  "  mv s6, s1\n" ++
  ".Lwidx_build_have_end:\n" ++
  "  bltu s6, s5, .Lwidx_build_fail\n" ++
  "  sub s7, s6, s5             # element len\n" ++
  "  mv a0, s4; jal ra, widx_record_ptr; mv s8, a0\n" ++
  "  add a0, s0, s5\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s8\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  sd s5, 32(s8)\n" ++
  "  sd s7, 40(s8)\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lwidx_build_loop\n" ++
  ".Lwidx_build_empty:\n" ++
  "  li s2, 0\n" ++
  ".Lwidx_build_sort:\n" ++
  "  li t0, 2; bltu s2, t0, .Lwidx_build_enable\n" ++
  "  srli s4, s2, 1\n" ++
  ".Lwidx_heapify:\n" ++
  "  beqz s4, .Lwidx_extract_init\n" ++
  "  addi s4, s4, -1\n" ++
  "  mv a0, s4; mv a1, s2; jal ra, widx_sift_down\n" ++
  "  j .Lwidx_heapify\n" ++
  ".Lwidx_extract_init:\n" ++
  "  mv s4, s2\n" ++
  ".Lwidx_extract:\n" ++
  "  li t0, 1; bleu s4, t0, .Lwidx_build_enable\n" ++
  "  addi s4, s4, -1\n" ++
  "  li a0, 0; jal ra, widx_record_ptr; mv s8, a0\n" ++
  "  mv a0, s4; jal ra, widx_record_ptr; mv s9, a0\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, widx_swap_records\n" ++
  "  li a0, 0; mv a1, s4; jal ra, widx_sift_down\n" ++
  "  j .Lwidx_extract\n" ++
  ".Lwidx_build_enable:\n" ++
  "  la t0, widx_section_ptr; sd s0, 0(t0)\n" ++
  "  la t0, widx_section_len; sd s1, 0(t0)\n" ++
  "  la t0, widx_count; sd s2, 0(t0)\n" ++
  "  li t1, 1; la t0, widx_enabled; sd t1, 0(t0)\n" ++
  "  li a0, 0\n" ++
  "  j .Lwidx_build_ret\n" ++
  ".Lwidx_build_fail:\n" ++
  "  li t1, 1; la t0, widx_build_status; sd t1, 0(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lwidx_build_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  "\n" ++
  "witness_lookup_by_hash_indexed:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a2                  # target hash\n" ++
  "  mv s1, a3                  # out offset\n" ++
  "  mv s2, a4                  # out length\n" ++
  "  li s3, 0                   # lo\n" ++
  "  la t0, widx_count; ld s4, 0(t0) # hi\n" ++
  ".Lwidx_lookup_loop:\n" ++
  "  bgeu s3, s4, .Lwidx_lookup_miss\n" ++
  "  add s5, s3, s4\n" ++
  "  srli s5, s5, 1             # mid\n" ++
  "  mv a0, s5; jal ra, widx_record_ptr; mv s6, a0\n" ++
  "  mv a0, s6; mv a1, s0; jal ra, widx_cmp32\n" ++
  "  li t0, 1; beq a0, t0, .Lwidx_lookup_hit\n" ++
  "  li t0, 0; beq a0, t0, .Lwidx_lookup_less\n" ++
  "  mv s4, s5\n" ++
  "  j .Lwidx_lookup_loop\n" ++
  ".Lwidx_lookup_less:\n" ++
  "  addi s3, s5, 1\n" ++
  "  j .Lwidx_lookup_loop\n" ++
  ".Lwidx_lookup_hit:\n" ++
  "  ld t0, 32(s6); sd t0, 0(s1)\n" ++
  "  ld t0, 40(s6); sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lwidx_lookup_ret\n" ++
  ".Lwidx_lookup_miss:\n" ++
  "  li a0, 1\n" ++
  ".Lwidx_lookup_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  ".pushsection .data\n" ++
  ".balign 8\n" ++
  "widx_enabled:\n  .zero 8\n" ++
  "widx_section_ptr:\n  .zero 8\n" ++
  "widx_section_len:\n  .zero 8\n" ++
  "widx_count:\n  .zero 8\n" ++
  "widx_build_status:\n  .zero 8\n" ++
  "widx_build_section_len:\n  .zero 8\n" ++
  "widx_build_count:\n  .zero 8\n" ++
  "wlh_lookup_calls:\n  .zero 8\n" ++
  "wlh_indexed_calls:\n  .zero 8\n" ++
  "wlh_indexed_hits:\n  .zero 8\n" ++
  "wlh_indexed_misses:\n  .zero 8\n" ++
  "wlh_linear_calls:\n  .zero 8\n" ++
  "wlh_linear_hits:\n  .zero 8\n" ++
  "wlh_linear_misses:\n  .zero 8\n" ++
  "wlh_linear_iterations:\n  .zero 8\n" ++
  "wlh_linear_last_section_len:\n  .zero 8\n" ++
  "wlh_linear_max_section_len:\n  .zero 8\n" ++
  ".popsection\n" ++
  -- The index arena is runtime-built scratch, not initialized data.  Keep the
  -- metadata above in `.data`, but place the six-MiB record arena in NOBITS so
  -- it does not occupy the linked image's PROGBITS payload.
  ".section .bss, \"aw\", @nobits\n" ++
  ".balign 8\n" ++
  "widx_records:\n  .zero " ++ toString mptWitnessIndexArenaBytes ++ "\n" ++
  ".section .text"

end EvmAsm.Codegen
