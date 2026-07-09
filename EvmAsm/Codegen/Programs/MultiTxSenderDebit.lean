/-
  EvmAsm.Codegen.Programs.MultiTxSenderDebit

  Focused helper for the bmvmx.5.5.2.2 B2 cumulative-balance chain.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## multi_tx_running_sender_balance_step

    One update step for the B2.2 per-sender running-balance table. Entries are
    64 bytes: sender address lane at +0, running u256 BE balance at +32.
    Return status: 0 updated, 1 underflow, 2 table full.
-/
def multiTxRunningSenderBalanceStepFunction : String :=
  "multi_tx_running_sender_balance_step:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5\n" ++
  "  ld t0, 0(s1)                 # count\n" ++
  "  li t1, 0                     # k\n" ++
  ".Lmtxrb_scan:\n" ++
  "  bgeu t1, t0, .Lmtxrb_append\n" ++
  "  slli t2, t1, 6; add t2, s0, t2\n" ++
  "  li t3, 0\n" ++
  ".Lmtxrb_cmp:\n" ++
  "  li t4, 20; beq t3, t4, .Lmtxrb_found\n" ++
  "  add t5, t2, t3; lbu t5, 0(t5); add t6, s3, t3; lbu t6, 0(t6); bne t5, t6, .Lmtxrb_next\n" ++
  "  addi t3, t3, 1; j .Lmtxrb_cmp\n" ++
  ".Lmtxrb_next:\n" ++
  "  addi t1, t1, 1; j .Lmtxrb_scan\n" ++
  ".Lmtxrb_found:\n" ++
  "  addi a0, t2, 32; mv a1, s5; addi a2, t2, 32\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  beqz a0, .Lmtxrb_ok\n" ++
  "  li a0, 1; j .Lmtxrb_ret\n" ++
  ".Lmtxrb_append:\n" ++
  "  bgeu t0, s2, .Lmtxrb_full\n" ++
  "  slli t2, t0, 6; add t2, s0, t2\n" ++
  "  li t3, 0\n" ++
  ".Lmtxrb_copy_addr:\n" ++
  "  li t4, 20; beq t3, t4, .Lmtxrb_zero_addr_tail\n" ++
  "  add t5, s3, t3; lbu t5, 0(t5); add t6, t2, t3; sb t5, 0(t6); addi t3, t3, 1; j .Lmtxrb_copy_addr\n" ++
  ".Lmtxrb_zero_addr_tail:\n" ++
  "  li t4, 32; beq t3, t4, .Lmtxrb_append_sub\n" ++
  "  add t6, t2, t3; sb zero, 0(t6); addi t3, t3, 1; j .Lmtxrb_zero_addr_tail\n" ++
  ".Lmtxrb_append_sub:\n" ++
  "  mv a0, s4; mv a1, s5; addi a2, t2, 32\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  beqz a0, .Lmtxrb_append_count\n" ++
  "  li a0, 1; j .Lmtxrb_ret\n" ++
  ".Lmtxrb_append_count:\n" ++
  "  ld t0, 0(s1); addi t0, t0, 1; sd t0, 0(s1)\n" ++
  ".Lmtxrb_ok:\n" ++
  "  li a0, 0; j .Lmtxrb_ret\n" ++
  ".Lmtxrb_full:\n" ++
  "  li a0, 2\n" ++
  ".Lmtxrb_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64\n" ++
  "  ret"

/- Probe input after zisk length: +8 row_count, then 96-byte rows
   (sender lane, pre balance, debit). Output: status, count, then table. -/
def ziskMultiTxRunningSenderBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  sd zero, 0(s1); sd zero, 8(s1)\n" ++
  "  la t0, mtxrb_count; sd zero, 0(t0)\n" ++
  "  ld s2, 8(s0)                 # row_count\n" ++
  "  li s3, 0                     # i\n" ++
  ".Lmtxrb_probe_loop:\n" ++
  "  bgeu s3, s2, .Lmtxrb_probe_done_rows\n" ++
  "  li t0, 96; mul t0, s3, t0; addi t0, t0, 16; add s4, s0, t0\n" ++
  "  la a0, mtxrb_table; la a1, mtxrb_count; li a2, " ++ toString bvMtxSenderBalanceEntries ++ "; mv a3, s4; addi a4, s4, 32; addi a5, s4, 64\n" ++
  "  jal ra, multi_tx_running_sender_balance_step\n" ++
  "  bnez a0, .Lmtxrb_probe_status\n" ++
  "  addi s3, s3, 1; j .Lmtxrb_probe_loop\n" ++
  ".Lmtxrb_probe_done_rows:\n" ++
  "  li a0, 0\n" ++
  ".Lmtxrb_probe_status:\n" ++
  "  sd a0, 0(s1)\n" ++
  "  la t0, mtxrb_count; ld t0, 0(t0); sd t0, 8(s1)\n" ++
  "  la t1, mtxrb_table; addi t2, s1, 16; li t3, 0; li t4, 240   # remaining 256-byte probe output window\n" ++
  ".Lmtxrb_probe_copy:\n" ++
  "  beq t3, t4, .Lmtxrb_probe_done\n" ++
  "  add t5, t1, t3; lbu t5, 0(t5); add t6, t2, t3; sb t5, 0(t6); addi t3, t3, 1; j .Lmtxrb_probe_copy\n" ++
  ".Lmtxrb_probe_done:\n" ++
  "  j .Lmtxrb_probe_exit\n" ++
  u256SubBeFunction ++ "\n" ++
  multiTxRunningSenderBalanceStepFunction ++ "\n" ++
  ".Lmtxrb_probe_exit:"

def ziskMultiTxRunningSenderBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mtxrb_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "mtxrb_table:\n  .zero " ++ toString bvMtxSenderBalanceTableBytes ++ "\n"

def ziskMultiTxRunningSenderBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMultiTxRunningSenderBalancePrologue
  dataAsm     := ziskMultiTxRunningSenderBalanceDataSection
}

end EvmAsm.Codegen
