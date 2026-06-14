/-
  EvmAsm.Codegen.Programs.BlockVerdictSenderCounts

  Deterministic sender-count table helper for the multi-tx B1 final-nonce check.
  The current verdict tail scans prior/all senders per transaction; this helper
  provides the non-quadratic substrate: sort sender addresses, then count equal
  runs once.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## b1_sender_count_table

    Build a distinct sender-count table from the multi-tx skip-list sender lanes.

    Calling convention:
      a0 = skip-list ptr, where sender_i starts at a0 + i*64
      a1 = tx_count, maximum 1024 for this scratch-backed helper
      a2 = output table ptr, entries are 40 bytes: 32-byte padded address + u64 count
      a3 = output table capacity in entries
      a4 = output distinct-count ptr

    Returns a0 = 0 on success, 1 if tx_count exceeds scratch capacity or output
    capacity. The algorithm is deterministic: copy sender lanes, stable radix-sort
    by address bytes 19..0, then compress equal sorted runs. No hash collisions or
    input-dependent probe lengths can weaken B1. -/
def b1SenderCountTableFunction : String :=
  "b1_sender_count_table:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1024; bgtu s1, t0, .Lb1sc_cap\n" ++
  "  bgtu s1, s3, .Lb1sc_cap\n" ++
  "  beqz s1, .Lb1sc_zero\n" ++
  "  la s5, b1sc_sort_a; la s6, b1sc_sort_b\n" ++
  -- Copy sender lanes into sort_a as 32-byte padded records.
  "  li s8, 0\n" ++
  ".Lb1sc_copy_loop:\n" ++
  "  bgeu s8, s1, .Lb1sc_copy_done\n" ++
  "  slli t0, s8, 6; add t1, s0, t0\n" ++
  "  slli t2, s8, 5; add t3, s5, t2\n" ++
  "  li t4, 0\n" ++
  ".Lb1sc_copy_bytes:\n" ++
  "  li t5, 32; beq t4, t5, .Lb1sc_copy_next\n" ++
  "  add t5, t1, t4; lbu t6, 0(t5); add t5, t3, t4; sb t6, 0(t5)\n" ++
  "  addi t4, t4, 1; j .Lb1sc_copy_bytes\n" ++
  ".Lb1sc_copy_next:\n" ++
  "  addi s8, s8, 1; j .Lb1sc_copy_loop\n" ++
  ".Lb1sc_copy_done:\n" ++
  -- Stable radix sort, least-significant address byte first: byte 19 down to 0.
  "  li s7, 19\n" ++
  ".Lb1sc_pass:\n" ++
  "  la s10, b1sc_counts\n" ++
  "  li t0, 0\n" ++
  ".Lb1sc_zero_counts:\n" ++
  "  li t1, 256; beq t0, t1, .Lb1sc_count_loop_init\n" ++
  "  slli t2, t0, 3; add t3, s10, t2; sd zero, 0(t3)\n" ++
  "  addi t0, t0, 1; j .Lb1sc_zero_counts\n" ++
  ".Lb1sc_count_loop_init:\n" ++
  "  li s8, 0\n" ++
  ".Lb1sc_count_loop:\n" ++
  "  bgeu s8, s1, .Lb1sc_prefix_init\n" ++
  "  slli t0, s8, 5; add t1, s5, t0; add t1, t1, s7; lbu t2, 0(t1)\n" ++
  "  slli t3, t2, 3; add t4, s10, t3; ld t5, 0(t4); addi t5, t5, 1; sd t5, 0(t4)\n" ++
  "  addi s8, s8, 1; j .Lb1sc_count_loop\n" ++
  ".Lb1sc_prefix_init:\n" ++
  "  li t0, 0; li t1, 0\n" ++
  ".Lb1sc_prefix_loop:\n" ++
  "  li t2, 256; beq t0, t2, .Lb1sc_scatter_init\n" ++
  "  slli t3, t0, 3; add t4, s10, t3; ld t5, 0(t4); sd t1, 0(t4); add t1, t1, t5\n" ++
  "  addi t0, t0, 1; j .Lb1sc_prefix_loop\n" ++
  ".Lb1sc_scatter_init:\n" ++
  "  li s8, 0\n" ++
  ".Lb1sc_scatter_loop:\n" ++
  "  bgeu s8, s1, .Lb1sc_swap\n" ++
  "  slli t0, s8, 5; add t1, s5, t0\n" ++
  "  add t2, t1, s7; lbu t2, 0(t2)\n" ++
  "  slli t3, t2, 3; add t4, s10, t3; ld t5, 0(t4); addi t6, t5, 1; sd t6, 0(t4)\n" ++
  "  slli t5, t5, 5; add t6, s6, t5\n" ++
  "  li t3, 0\n" ++
  ".Lb1sc_scatter_copy:\n" ++
  "  li t4, 32; beq t3, t4, .Lb1sc_scatter_next\n" ++
  "  add t4, t1, t3; lbu a0, 0(t4); add t4, t6, t3; sb a0, 0(t4)\n" ++
  "  addi t3, t3, 1; j .Lb1sc_scatter_copy\n" ++
  ".Lb1sc_scatter_next:\n" ++
  "  addi s8, s8, 1; j .Lb1sc_scatter_loop\n" ++
  ".Lb1sc_swap:\n" ++
  "  mv t0, s5; mv s5, s6; mv s6, t0\n" ++
  "  beqz s7, .Lb1sc_runs\n" ++
  "  addi s7, s7, -1; j .Lb1sc_pass\n" ++
  -- Compress sorted runs in s5 into the output table.
  ".Lb1sc_runs:\n" ++
  "  mv s11, s5\n" ++                                             -- current record ptr
  "  li s9, 1\n" ++                                                -- current run count
  "  li s8, 1\n" ++                                                -- i
  "  li s7, 0\n" ++                                                -- distinct count
  ".Lb1sc_run_loop:\n" ++
  "  bgeu s8, s1, .Lb1sc_write_last\n" ++
  "  slli t0, s8, 5; add t1, s5, t0\n" ++                         -- candidate record
  "  li t2, 0\n" ++
  ".Lb1sc_run_cmp:\n" ++
  "  li t3, 20; beq t2, t3, .Lb1sc_run_equal\n" ++
  "  add t3, s11, t2; lbu t4, 0(t3); add t3, t1, t2; lbu t5, 0(t3); bne t4, t5, .Lb1sc_run_new\n" ++
  "  addi t2, t2, 1; j .Lb1sc_run_cmp\n" ++
  ".Lb1sc_run_equal:\n" ++
  "  addi s9, s9, 1; addi s8, s8, 1; j .Lb1sc_run_loop\n" ++
  ".Lb1sc_run_new:\n" ++
  "  mv s6, t1\n" ++
  "  mv a0, s11; mv a1, s9; mv a2, s7; jal ra, b1sc_write_entry\n" ++
  "  addi s7, s7, 1; mv s11, s6; li s9, 1; addi s8, s8, 1; j .Lb1sc_run_loop\n" ++
  ".Lb1sc_write_last:\n" ++
  "  mv a0, s11; mv a1, s9; mv a2, s7; jal ra, b1sc_write_entry\n" ++
  "  addi s7, s7, 1; sd s7, 0(s4); li a0, 0; j .Lb1sc_ret\n" ++
  ".Lb1sc_zero:\n" ++
  "  sd zero, 0(s4); li a0, 0; j .Lb1sc_ret\n" ++
  ".Lb1sc_cap:\n" ++
  "  li a0, 1\n" ++
  ".Lb1sc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n" ++
  -- Write one 40-byte table entry. Uses parent s2 = table base.
  -- a0 = 32-byte address record ptr, a1 = count, a2 = output index.
  "b1sc_write_entry:\n" ++
  "  li t0, 40; mul t0, a2, t0; add t1, s2, t0\n" ++
  "  li t2, 0\n" ++
  ".Lb1sc_we_copy:\n" ++
  "  li t3, 32; beq t2, t3, .Lb1sc_we_count\n" ++
  "  add t3, a0, t2; lbu t4, 0(t3); add t3, t1, t2; sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1; j .Lb1sc_we_copy\n" ++
  ".Lb1sc_we_count:\n" ++
  "  sd a1, 32(t1); ret"

/-- Shared scratch arena for `b1_sender_count_table`. -/
def b1SenderCountTableScratchDataSection : String :=
  ".balign 32\n" ++
  "b1sc_sort_a:\n  .zero 32768\n" ++
  "b1sc_sort_b:\n  .zero 32768\n" ++
  ".balign 8\n" ++
  "b1sc_counts:\n  .zero 2048\n"

/-- Scratch/data for `b1_sender_count_table` and its focused probe. -/
def b1SenderCountTableDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "b1sc_out_count:\n  .zero 8\n" ++
  b1SenderCountTableScratchDataSection ++
  ".balign 32\n" ++
  -- Six sender lanes with 64-byte stride: A, B, A, C, B, A.
  "b1sc_probe_skip:\n" ++
  "  .rept 20\n  .byte 0x11\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x22\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x11\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x33\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x22\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x11\n  .endr\n  .zero 44\n" ++
  ".balign 8\n" ++
  "b1sc_probe_table:\n  .zero 320\n"

/-- `zisk_b1_sender_count_table`: focused probe for the deterministic sender table.
    Output at 0xa0010000:
      +0   status
      +8   distinct count
      +16  first three 40-byte table entries, sorted by address. -/
def ziskB1SenderCountTablePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, b1sc_probe_skip; li a1, 6; la a2, b1sc_probe_table; li a3, 8; la a4, b1sc_out_count\n" ++
  "  jal ra, b1_sender_count_table\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, b1sc_out_count; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, b1sc_probe_table; li t2, 0\n" ++
  ".Lb1scp_copy_out:\n" ++
  "  li t3, 120; beq t2, t3, .Lb1scp_done\n" ++
  "  add t3, t1, t2; lbu t4, 0(t3); addi t5, t0, 16; add t5, t5, t2; sb t4, 0(t5)\n" ++
  "  addi t2, t2, 1; j .Lb1scp_copy_out\n" ++
  ".Lb1scp_done:\n" ++
  "  j .Lb1scp_halt\n" ++
  b1SenderCountTableFunction ++ "\n" ++
  ".Lb1scp_halt:"

def ziskB1SenderCountTableProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskB1SenderCountTablePrologue
  dataAsm     := b1SenderCountTableDataSection
}

end EvmAsm.Codegen
