/-
  EvmAsm.Codegen.Programs.BlockVerdictSenderCounts

  Deterministic sender-count table helper for the multi-tx B1 final-nonce check.
  The current verdict tail scans prior/all senders per transaction; this helper
  provides the non-quadratic substrate: sort sender addresses, then count equal
  runs once.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## b1_sender_count_table

    Build a distinct sender-count table from the multi-tx skip-list sender lanes.

    Calling convention:
      a0 = skip-list ptr, where sender_i starts at a0 + i*64
      a1 = tx_count, maximum bvMtxSenderCountEntries for this scratch-backed helper
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
  "  li t0, " ++ toString bvMtxSenderCountEntries ++ "; bgtu s1, t0, .Lb1sc_cap\n" ++
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

/-! `b1_sender_table_find`

    Binary-search a sorted 40-byte sender-count table produced by
    `b1_sender_count_table`.

    Calling convention:
      a0 = table ptr, entries are 32-byte padded address + u64 count
      a1 = distinct sender count
      a2 = 20-byte address ptr

    Returns:
      a0 = 0 and a1 = entry ptr when found
      a0 = 1 when absent/malformed. -/
def b1SenderTableFind_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LI .x19 (0 : Word),
    .MV .x20 .x9,
    .BGEU .x19 .x20 (96 : BitVec 13),
    .ADD .x21 .x19 .x20,
    .SRLI .x21 .x21 (1 : BitVec 6),
    .LI .x5 (40 : Word),
    .MUL .x5 .x21 .x5,
    .ADD .x6 .x8 .x5,
    .LI .x7 (0 : Word),
    .LI .x28 (20 : Word),
    .BEQ .x7 .x28 (52 : BitVec 13),
    .ADD .x28 .x6 .x7,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x28 .x18 .x7,
    .LBU .x30 .x28 (0 : BitVec 12),
    .BLTU .x29 .x30 (16 : BitVec 13),
    .BLTU .x30 .x29 (20 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .ADDI .x19 .x21 (1 : BitVec 12),
    .JAL .x0 (-72 : BitVec 21),
    .MV .x20 .x21,
    .JAL .x0 (-80 : BitVec 21),
    .LI .x10 (0 : Word),
    .MV .x11 .x6,
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def b1SenderTableFindFunction : String :=
  "b1_sender_table_find:\n" ++ emitProgram b1SenderTableFind_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `b1SenderTableFind_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem b1SenderTableFindFunction_eq_prog :
    b1SenderTableFindFunction = "b1_sender_table_find:\n" ++ emitProgram b1SenderTableFind_prog := rfl

#guard b1SenderTableFindFunction.startsWith "b1_sender_table_find:\n"
#guard b1SenderTableFind_prog.length = 47
/-- Shared scratch arena for `b1_sender_count_table`. -/
def b1SenderCountTableScratchDataSection : String :=
  ".balign 32\n" ++
  "b1sc_sort_a:\n  .zero " ++ toString bvMtxSenderCountSortBytes ++ "\n" ++
  "b1sc_sort_b:\n  .zero " ++ toString bvMtxSenderCountSortBytes ++ "\n" ++
  ".balign 8\n" ++
  "b1sc_counts:\n  .zero 2048\n"

/-- Scratch/data for `b1_sender_count_table` and its focused probe. -/
def b1SenderCountTableDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "b1sc_out_count:\n  .zero 8\n" ++
  b1SenderCountTableScratchDataSection ++
  ".balign 32\n" ++
  -- Sender lanes with 64-byte stride. Mode 0 keeps the first six as
  -- A, B, A, C, B, A; the other modes seed distinct senders programmatically
  -- up to the full 200M transaction-capacity target.
  "b1sc_probe_skip:\n" ++
  "  .rept 20\n  .byte 0x11\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x22\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x11\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x33\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x22\n  .endr\n  .zero 44\n" ++
  "  .rept 20\n  .byte 0x11\n  .endr\n  .zero 44\n" ++
  "  .zero " ++ toString (bvMtxSenderCountSkipBytes - 384) ++ "\n" ++
  ".balign 8\n" ++
  "b1sc_probe_table:\n  .zero " ++ toString bvMtxSenderCountTableBytes ++ "\n"

/-- `zisk_b1_sender_count_table`: focused probe for the deterministic sender table.
    Output at 0xa0010000:
      +0   status
      +8   distinct count
      +16  first three 40-byte table entries, sorted by address. -/
def ziskB1SenderCountTablePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la a0, b1sc_probe_skip; li a1, 6; la a2, b1sc_probe_table; li a3, " ++ toString bvMtxSenderCountEntries ++ "; la a4, b1sc_out_count\n" ++
  "  li t0, 5; beq s1, t0, .Lb1scp_over_cap\n" ++
  "  li t0, 6; beq s1, t0, .Lb1scp_seq_repeated_valid\n" ++
  "  li t0, 7; beq s1, t0, .Lb1scp_seq_reuse\n" ++
  "  li t0, 8; beq s1, t0, .Lb1scp_seq_too_high\n" ++
  "  li t0, 9; beq s1, t0, .Lb1scp_seq17\n" ++
  "  li t0, 10; beq s1, t0, .Lb1scp_seq1024\n" ++
  "  li t0, 11; beq s1, t0, .Lb1scp_seq1025\n" ++
  "  li t0, 12; beq s1, t0, .Lb1scp_seq_full\n" ++
  "  beqz s1, .Lb1scp_call\n" ++
  "  li t0, 1; beq s1, t0, .Lb1scp_mode17\n" ++
  "  li t0, 2; beq s1, t0, .Lb1scp_mode1024\n" ++
  "  li t0, 3; beq s1, t0, .Lb1scp_mode1025\n" ++
  "  li t0, 4; beq s1, t0, .Lb1scp_mode_full\n" ++
  "  j .Lb1scp_call\n" ++
  ".Lb1scp_mode17:\n  li a1, 17; j .Lb1scp_seed_distinct\n" ++
  ".Lb1scp_mode1024:\n  li a1, 1024; j .Lb1scp_seed_distinct\n" ++
  ".Lb1scp_mode1025:\n  li a1, 1025; j .Lb1scp_seed_distinct\n" ++
  ".Lb1scp_mode_full:\n  li a1, " ++ toString bvMtxSenderCountEntries ++ "; j .Lb1scp_seed_distinct\n" ++
  ".Lb1scp_over_cap:\n  li a1, " ++ toString (bvMtxSenderCountEntries + 1) ++ "; j .Lb1scp_call\n" ++
  ".Lb1scp_seq_repeated_valid:\n  li a1, 6; li s2, 6; li s3, 0; j .Lb1scp_seq_call\n" ++
  ".Lb1scp_seq_reuse:\n  li a1, 6; li s2, 6; li s3, 1; j .Lb1scp_seq_call\n" ++
  ".Lb1scp_seq_too_high:\n  li a1, 6; li s2, 6; li s3, 2; j .Lb1scp_seq_call\n" ++
  ".Lb1scp_seq17:\n  li a1, 17; li s2, 17; li s3, 0; j .Lb1scp_seed_distinct_seq\n" ++
  ".Lb1scp_seq1024:\n  li a1, 1024; li s2, 1024; li s3, 0; j .Lb1scp_seed_distinct_seq\n" ++
  ".Lb1scp_seq1025:\n  li a1, 1025; li s2, 1025; li s3, 0; j .Lb1scp_seed_distinct_seq\n" ++
  ".Lb1scp_seq_full:\n  li a1, " ++ toString bvMtxSenderCountEntries ++ "; li s2, " ++ toString bvMtxSenderCountEntries ++ "; li s3, 0; j .Lb1scp_seed_distinct_seq\n" ++
  ".Lb1scp_seed_distinct_seq:\n" ++
  "  la t0, b1sc_probe_skip; li t1, 0\n" ++
  ".Lb1scp_seed_seq_loop:\n" ++
  "  bgeu t1, a1, .Lb1scp_seq_call\n" ++
  "  addi t3, t1, 1; srli t4, t3, 8; sb t4, 18(t0); andi t4, t3, 255; sb t4, 19(t0)\n" ++
  "  addi t0, t0, 64; addi t1, t1, 1; j .Lb1scp_seed_seq_loop\n" ++
  ".Lb1scp_seq_call:\n" ++
  "  jal ra, b1_sender_count_table\n" ++
  "  bnez a0, .Lb1scp_seq_build_fail\n" ++
  "  la t0, b1sc_out_count; ld t1, 0(t0); li s4, 0\n" ++
  ".Lb1scp_seq_zero_loop:\n" ++
  "  bgeu s4, t1, .Lb1scp_seq_loop_init\n" ++
  "  li t2, 40; mul t2, s4, t2; la t3, b1sc_probe_table; add t3, t3, t2; sd zero, 32(t3)\n" ++
  "  addi s4, s4, 1; j .Lb1scp_seq_zero_loop\n" ++
  ".Lb1scp_seq_loop_init:\n" ++
  "  li s4, 0; li s5, 5\n" ++
  ".Lb1scp_seq_loop:\n" ++
  "  bgeu s4, s2, .Lb1scp_seq_ok\n" ++
  "  slli t0, s4, 6; la a2, b1sc_probe_skip; add a2, a2, t0; la a0, b1sc_probe_table; la t1, b1sc_out_count; ld a1, 0(t1)\n" ++
  "  jal ra, b1_sender_table_find\n" ++
  "  bnez a0, .Lb1scp_seq_lookup_fail\n" ++
  "  mv t6, a1; ld t5, 32(t6); add t0, s5, t5; mv t1, t0\n" ++
  "  li t2, 2; bne s4, t2, .Lb1scp_seq_have_nonce\n" ++
  "  li t2, 1; beq s3, t2, .Lb1scp_seq_nonce_low\n" ++
  "  li t2, 2; beq s3, t2, .Lb1scp_seq_nonce_high\n" ++
  ".Lb1scp_seq_have_nonce:\n" ++
  "  bne t1, t0, .Lb1scp_seq_mismatch\n" ++
  "  addi t5, t5, 1; sd t5, 32(t6); addi s4, s4, 1; j .Lb1scp_seq_loop\n" ++
  ".Lb1scp_seq_nonce_low:\n  mv t1, s5; j .Lb1scp_seq_have_nonce\n" ++
  ".Lb1scp_seq_nonce_high:\n  addi t1, t0, 1; j .Lb1scp_seq_have_nonce\n" ++
  ".Lb1scp_seq_ok:\n" ++
  "  li t0, 0xa0010000; sd zero, 152(t0); sd s4, 160(t0); j .Lb1scp_halt\n" ++
  ".Lb1scp_seq_mismatch:\n" ++
  "  li t0, 0xa0010000; li t1, 40; sd t1, 152(t0); sd s4, 160(t0); j .Lb1scp_halt\n" ++
  ".Lb1scp_seq_lookup_fail:\n" ++
  "  li t0, 0xa0010000; li t1, 41; sd t1, 152(t0); sd s4, 160(t0); j .Lb1scp_halt\n" ++
  ".Lb1scp_seq_build_fail:\n" ++
  "  li t0, 0xa0010000; li t1, 42; sd t1, 152(t0); sd zero, 160(t0); j .Lb1scp_halt\n" ++
  ".Lb1scp_seed_distinct:\n" ++
  "  la t0, b1sc_probe_skip; li t1, 0\n" ++
  ".Lb1scp_seed_loop:\n" ++
  "  bgeu t1, a1, .Lb1scp_call\n" ++
  "  addi t3, t1, 1; srli t4, t3, 8; sb t4, 18(t0); andi t4, t3, 255; sb t4, 19(t0)\n" ++
  "  addi t0, t0, 64; addi t1, t1, 1; j .Lb1scp_seed_loop\n" ++
  ".Lb1scp_call:\n" ++
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
  "  li t0, 0xa0010000; ld t1, 0(t0); bnez t1, .Lb1scp_find_skip\n" ++
  "  la t2, b1sc_out_count; ld a1, 0(t2); addi t3, a1, -1; li t4, 40; mul t3, t3, t4\n" ++
  "  la a2, b1sc_probe_table; add a2, a2, t3; la a0, b1sc_probe_table\n" ++
  "  jal ra, b1_sender_table_find\n" ++
  "  li t0, 0xa0010000; sd a0, 136(t0); bnez a0, .Lb1scp_halt; ld t1, 32(a1); sd t1, 144(t0); j .Lb1scp_halt\n" ++
  ".Lb1scp_find_skip:\n" ++
  "  li t2, 9; sd t2, 136(t0); sd zero, 144(t0)\n" ++
  "  j .Lb1scp_halt\n" ++
  b1SenderCountTableFunction ++ "\n" ++
  b1SenderTableFindFunction ++ "\n" ++
  ".Lb1scp_halt:"

def ziskB1SenderCountTableProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskB1SenderCountTablePrologue
  dataAsm     := b1SenderCountTableDataSection
}

end EvmAsm.Codegen
