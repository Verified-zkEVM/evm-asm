/-
  EvmAsm.Codegen.Programs.BlockVerdictRecipientCredits

  Standalone B3.1 substrate: aggregate multi-transaction recipient value credits
  by recipient address before wiring the result into block_verdict.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## b3_recipient_credit_table

    Calling convention:
      a0 = recipient address array ptr (20-byte elements)
      a1 = tx value array ptr (32-byte big-endian u256 elements)
      a2 = tx count, bounded by `bvMtxActiveTxCap`
      a3 = out entry table ptr (64-byte entries)
      a4 = out count ptr

    Output entry layout:
      entry + 0  : recipient address (20 bytes)
      entry + 32 : aggregate credited value (32-byte big-endian u256)

    Returns:
      a0 = 0 on success
      a0 = 1 if an aggregate value overflows u256
      a0 = 2 if tx count exceeds `bvMtxActiveTxCap`

    Zero-value rows are retained as zero-credit entries. A later verdict caller can
    skip zero-credit accounts, but keeping them here makes the grouping exact and
    deterministic for probes and future composition. -/
def b3RecipientCreditTableFunction : String :=
  "b3_recipient_credit_table:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0                    # recipient cursor\n" ++
  "  mv s1, a1                    # value cursor\n" ++
  "  mv s2, a2                    # tx count\n" ++
  "  mv s3, a3                    # output table\n" ++
  "  mv s8, a4                    # output count ptr\n" ++
  "  li t0, " ++ toString bvMtxActiveTxCap ++ "\n" ++
  "  bltu t0, s2, .Lb3rct_too_many\n" ++
  "  sd zero, 0(s8)\n" ++
  "  li s4, 0                     # tx index\n" ++
  ".Lb3rct_tx_loop:\n" ++
  "  beq s4, s2, .Lb3rct_ok\n" ++
  "  ld s5, 0(s8)                 # current distinct count\n" ++
  "  li s6, 0                     # entry index\n" ++
  "  mv s7, s3                    # entry cursor\n" ++
  ".Lb3rct_find_loop:\n" ++
  "  beq s6, s5, .Lb3rct_new_entry\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s7\n" ++
  "  jal ra, .Lb3rct_addr_eq\n" ++
  "  bnez a0, .Lb3rct_existing_entry\n" ++
  "  addi s7, s7, 64\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lb3rct_find_loop\n" ++
  ".Lb3rct_existing_entry:\n" ++
  "  addi a0, s7, 32\n" ++
  "  mv a1, s1\n" ++
  "  addi a2, s7, 32\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lb3rct_sum_overflow\n" ++
  "  j .Lb3rct_next_tx\n" ++
  ".Lb3rct_new_entry:\n" ++
  "  mv t0, s7; li t1, 8\n" ++
  ".Lb3rct_zero_entry:\n" ++
  "  beqz t1, .Lb3rct_copy_addr\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lb3rct_zero_entry\n" ++
  ".Lb3rct_copy_addr:\n" ++
  "  mv t0, s0; mv t1, s7; li t2, 20\n" ++
  ".Lb3rct_addr_copy_loop:\n" ++
  "  beqz t2, .Lb3rct_copy_value\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lb3rct_addr_copy_loop\n" ++
  ".Lb3rct_copy_value:\n" ++
  "  mv t0, s1; addi t1, s7, 32; li t2, 32\n" ++
  ".Lb3rct_value_copy_loop:\n" ++
  "  beqz t2, .Lb3rct_count_entry\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Lb3rct_value_copy_loop\n" ++
  ".Lb3rct_count_entry:\n" ++
  "  addi s5, s5, 1\n" ++
  "  sd s5, 0(s8)\n" ++
  ".Lb3rct_next_tx:\n" ++
  "  addi s0, s0, 20\n" ++
  "  addi s1, s1, 32\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lb3rct_tx_loop\n" ++
  ".Lb3rct_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lb3rct_return\n" ++
  ".Lb3rct_sum_overflow:\n" ++
  "  li a0, 1\n" ++
  "  j .Lb3rct_return\n" ++
  ".Lb3rct_too_many:\n" ++
  "  sd zero, 0(s8)\n" ++
  "  li a0, 2\n" ++
  ".Lb3rct_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  ld s7, 64(sp); ld s8, 72(sp); addi sp, sp, 96\n" ++
  "  ret\n" ++
  ".Lb3rct_addr_eq:\n" ++
  "  li t0, 20\n" ++
  ".Lb3rct_addr_eq_loop:\n" ++
  "  beqz t0, .Lb3rct_addr_eq_yes\n" ++
  "  lbu t1, 0(a0); lbu t2, 0(a1)\n" ++
  "  bne t1, t2, .Lb3rct_addr_eq_no\n" ++
  "  addi a0, a0, 1; addi a1, a1, 1; addi t0, t0, -1\n" ++
  "  j .Lb3rct_addr_eq_loop\n" ++
  ".Lb3rct_addr_eq_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lb3rct_addr_eq_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_b3_recipient_credit_table`: known-answer probe.
    Five rows aggregate into three recipients:
      A = 5 + 7 = 12
      B = 0 + 1 = 1
      C = 2
    The B row models the sender=recipient overlap shape from later composition: the
    address is still credited exactly, without special-casing or skipping. -/
def ziskB3RecipientCreditTablePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, b3rct_recipients\n" ++
  "  li t1, 13\n" ++
  ".Lb3rct_probe_zero_recipients:\n" ++
  "  beqz t1, .Lb3rct_probe_recipients_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lb3rct_probe_zero_recipients\n" ++
  ".Lb3rct_probe_recipients_done:\n" ++
  "  la t0, b3rct_recipients\n" ++
  "  li t1, 0x11; sb t1, 19(t0); sb t1, 59(t0)\n" ++
  "  li t1, 0x22; sb t1, 39(t0); sb t1, 99(t0)\n" ++
  "  li t1, 0x33; sb t1, 79(t0)\n" ++
  "  la t0, b3rct_values\n" ++
  "  li t1, 20\n" ++
  ".Lb3rct_probe_zero_values:\n" ++
  "  beqz t1, .Lb3rct_probe_values_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lb3rct_probe_zero_values\n" ++
  ".Lb3rct_probe_values_done:\n" ++
  "  la t0, b3rct_values\n" ++
  "  li t1, 5; sb t1, 31(t0)\n" ++
  "  li t1, 7; sb t1, 95(t0)\n" ++
  "  li t1, 2; sb t1, 127(t0)\n" ++
  "  li t1, 1; sb t1, 159(t0)\n" ++
  "  la a0, b3rct_recipients\n" ++
  "  la a1, b3rct_values\n" ++
  "  li a2, 5\n" ++
  "  la a3, b3rct_out\n" ++
  "  la a4, b3rct_out_count\n" ++
  "  jal ra, b3_recipient_credit_table\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, b3rct_out_count; ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  la t0, b3rct_out\n" ++
  "  lbu t1, 19(t0); sd t1, 16(s0)\n" ++
  "  lbu t1, 63(t0); sd t1, 24(s0)\n" ++
  "  addi t0, t0, 64\n" ++
  "  lbu t1, 19(t0); sd t1, 32(s0)\n" ++
  "  lbu t1, 63(t0); sd t1, 40(s0)\n" ++
  "  addi t0, t0, 64\n" ++
  "  lbu t1, 19(t0); sd t1, 48(s0)\n" ++
  "  lbu t1, 63(t0); sd t1, 56(s0)\n" ++
  "  j .Lb3rct_done\n" ++
  u256AddBeFunction ++ "\n" ++
  b3RecipientCreditTableFunction ++ "\n" ++
  ".Lb3rct_done:"

def ziskB3RecipientCreditTableDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "b3rct_recipients:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "b3rct_values:\n  .zero 160\n" ++
  ".balign 32\n" ++
  "b3rct_out:\n  .zero 320\n" ++
  ".balign 8\n" ++
  "b3rct_out_count:\n  .zero 8\n"


end EvmAsm.Codegen
