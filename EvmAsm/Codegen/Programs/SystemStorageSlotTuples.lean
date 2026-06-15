/-
  EvmAsm.Codegen.Programs.SystemStorageSlotTuples

  Reconstruct a slot tuple sequence from captured system-call SSTORE rows followed
  by regular user transaction SSTORE rows. This is the merge substrate for
  validating EIP-7928 block_access_index=0 storage tuple sequences precisely.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.SlotTupleSequencesMatch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## system_user_exec_log_slot_tuples
    a0 = addrHash ptr (32B)   a1 = slotKey ptr (32B)
    a2 = system storage-log base (128B rows)   a3 = system row count
    a4 = user storage-log base (128B rows)     a5 = user row count
    a6 = user exec_log_txindex base            a7 = out buffer ptr
    a0 (output) = total tuple count. If total exceeds bsrMaxTuplesPerSlot,
    output writes are suppressed and the caller must reject conservatively.

    Captured system rows all belong to block_access_index 0, so this helper uses
    a zero-filled txindex arena for the system-side call. User rows keep their
    existing txindex arena and are appended after the system tuples. -/
def systemUserExecLogSlotTuplesFunction : String :=
  "system_user_exec_log_slot_tuples:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                    # addrHash ptr\n" ++
  "  mv s1, a1                    # slotKey ptr\n" ++
  "  mv s2, a2                    # system log base\n" ++
  "  mv s3, a3                    # system row count\n" ++
  "  mv s4, a4                    # user log base\n" ++
  "  mv s5, a5                    # user row count\n" ++
  "  mv s6, a6                    # user txindex base\n" ++
  "  mv s7, a7                    # out buffer\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; la a4, sust_zero_txindex; la a5, sust_sysbuf\n" ++
  "  jal ra, exec_log_slot_tuples\n" ++
  "  mv s8, a0                    # system tuple count\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s4; mv a3, s5; mv a4, s6; la a5, sust_userbuf\n" ++
  "  jal ra, exec_log_slot_tuples\n" ++
  "  mv s9, a0                    # user tuple count\n" ++
  "  add t0, s8, s9\n" ++
  "  li t1, " ++ toString bsrMaxTuplesPerSlot ++ "; bgtu t0, t1, .Lsust_ret_total\n" ++
  "  li t2, 0                     # copy system tuples\n" ++
  ".Lsust_copy_sys:\n" ++
  "  beq t2, s8, .Lsust_copy_user_start\n" ++
  "  slli t3, t2, 5; slli t4, t2, 3; add t3, t3, t4\n" ++
  "  la t5, sust_sysbuf; add t5, t5, t3; add t6, s7, t3\n" ++
  "  ld t0, 0(t5); sd t0, 0(t6); ld t0, 8(t5); sd t0, 8(t6)\n" ++
  "  ld t0, 16(t5); sd t0, 16(t6); ld t0, 24(t5); sd t0, 24(t6); ld t0, 32(t5); sd t0, 32(t6)\n" ++
  "  addi t2, t2, 1; j .Lsust_copy_sys\n" ++
  ".Lsust_copy_user_start:\n" ++
  "  li t2, 0\n" ++
  ".Lsust_copy_user:\n" ++
  "  beq t2, s9, .Lsust_ret_total\n" ++
  "  add t3, s8, t2; slli t4, t3, 5; slli t3, t3, 3; add t4, t4, t3\n" ++
  "  slli t3, t2, 5; slli t5, t2, 3; add t3, t3, t5\n" ++
  "  la t5, sust_userbuf; add t5, t5, t3; add t6, s7, t4\n" ++
  "  ld t0, 0(t5); sd t0, 0(t6); ld t0, 8(t5); sd t0, 8(t6)\n" ++
  "  ld t0, 16(t5); sd t0, 16(t6); ld t0, 24(t5); sd t0, 24(t6); ld t0, 32(t5); sd t0, 32(t6)\n" ++
  "  addi t2, t2, 1; j .Lsust_copy_user\n" ++
  ".Lsust_ret_total:\n" ++
  "  add a0, s8, s9\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

def systemUserExecLogSlotTuplesData : String :=
  ".balign 8\n" ++
  "sust_zero_txindex:\n  .zero " ++ toString bvSystemStorageTxindexBytes ++ "\n" ++
  ".balign 32\n" ++
  "sust_sysbuf:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n" ++
  "sust_userbuf:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n" ++
  "sust_out:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n"

def ziskSystemUserExecLogSlotTuplesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, sust_probe_addr; li t1, 0xaaaaaaaaaaaaaaaa; sd t1, 0(t0); sd t1, 8(t0); sd t1, 16(t0); sd t1, 24(t0)\n" ++
  "  la t0, sust_probe_slot; li t1, 7; sd t1, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, sust_probe_sys_log; la t1, sust_probe_addr\n" ++
  "  ld t2, 0(t1); sd t2, 0(t0); ld t2, 8(t1); sd t2, 8(t0); ld t2, 16(t1); sd t2, 16(t0); ld t2, 24(t1); sd t2, 24(t0)\n" ++
  "  la t1, sust_probe_slot; ld t2, 0(t1); sd t2, 32(t0); ld t2, 8(t1); sd t2, 40(t0); ld t2, 16(t1); sd t2, 48(t0); ld t2, 24(t1); sd t2, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0); li t2, 0x44; sd t2, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  la t0, sust_probe_user_log; la t1, sust_probe_addr\n" ++
  "  ld t2, 0(t1); sd t2, 0(t0); ld t2, 8(t1); sd t2, 8(t0); ld t2, 16(t1); sd t2, 16(t0); ld t2, 24(t1); sd t2, 24(t0)\n" ++
  "  la t1, sust_probe_slot; ld t2, 0(t1); sd t2, 32(t0); ld t2, 8(t1); sd t2, 40(t0); ld t2, 16(t1); sd t2, 48(t0); ld t2, 24(t1); sd t2, 56(t0)\n" ++
  "  li t2, 0x44; sd t2, 64(t0); sd zero, 72(t0); sd zero, 80(t0); sd zero, 88(t0); li t2, 0x99; sd t2, 96(t0); sd zero, 104(t0); sd zero, 112(t0); sd zero, 120(t0)\n" ++
  "  la t0, sust_probe_user_txindex; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, sust_exp_sys_ok; sd zero, 0(t0); li t1, 0x44; sd t1, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++
  "  la t0, sust_exp_sys_bad; sd zero, 0(t0); li t1, 0x45; sd t1, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++
  "  la t0, sust_exp_mix_ok; sd zero, 0(t0); li t1, 0x44; sd t1, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0); li t1, 2; sd t1, 40(t0); li t1, 0x99; sd t1, 48(t0); sd zero, 56(t0); sd zero, 64(t0); sd zero, 72(t0)\n" ++
  "  la t0, sust_exp_mix_bad_user; sd zero, 0(t0); li t1, 0x44; sd t1, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0); li t1, 2; sd t1, 40(t0); li t1, 0x9a; sd t1, 48(t0); sd zero, 56(t0); sd zero, 64(t0); sd zero, 72(t0)\n" ++
  "  # system-only: expect one tuple and exact match; forged system value rejects\n" ++
  "  la a0, sust_probe_addr; la a1, sust_probe_slot; la a2, sust_probe_sys_log; li a3, 1; la a4, sust_probe_user_log; li a5, 0; la a6, sust_probe_user_txindex; la a7, sust_out\n" ++
  "  jal ra, system_user_exec_log_slot_tuples\n" ++
  "  li s0, 0xa0010000; sd a0, 0(s0)\n" ++
  "  la a0, sust_exp_sys_ok; li a1, 1; la a2, sust_out; li a3, 1; jal ra, slot_tuple_sequences_match; sd a0, 8(s0)\n" ++
  "  la a0, sust_exp_sys_bad; li a1, 1; la a2, sust_out; li a3, 1; jal ra, slot_tuple_sequences_match; sd a0, 16(s0)\n" ++
  "  # mixed system + user: expect two tuples and forged user value rejects\n" ++
  "  la a0, sust_probe_addr; la a1, sust_probe_slot; la a2, sust_probe_sys_log; li a3, 1; la a4, sust_probe_user_log; li a5, 1; la a6, sust_probe_user_txindex; la a7, sust_out\n" ++
  "  jal ra, system_user_exec_log_slot_tuples\n" ++
  "  sd a0, 24(s0)\n" ++
  "  la a0, sust_exp_mix_ok; li a1, 2; la a2, sust_out; li a3, 2; jal ra, slot_tuple_sequences_match; sd a0, 32(s0)\n" ++
  "  la a0, sust_exp_sys_bad; li a1, 1; la a2, sust_out; li a3, 2; jal ra, slot_tuple_sequences_match; sd a0, 40(s0)\n" ++
  "  la a0, sust_exp_mix_bad_user; li a1, 2; la a2, sust_out; li a3, 2; jal ra, slot_tuple_sequences_match; sd a0, 48(s0)\n" ++
  "  j .Lsust_pdone\n" ++
  systemUserExecLogSlotTuplesFunction ++ "\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  ".Lsust_pdone:"

def ziskSystemUserExecLogSlotTuplesDataSection : String :=
  ".section .data\n" ++
  systemUserExecLogSlotTuplesData ++ "\n" ++
  execLogSlotTuplesData ++ "\n" ++
  ".balign 32\n" ++
  "sust_probe_addr:\n  .zero 32\n" ++
  "sust_probe_slot:\n  .zero 32\n" ++
  "sust_probe_sys_log:\n  .zero 128\n" ++
  "sust_probe_user_log:\n  .zero 128\n" ++
  "sust_probe_user_txindex:\n  .zero 8\n" ++
  "sust_exp_sys_ok:\n  .zero 40\n" ++
  "sust_exp_sys_bad:\n  .zero 40\n" ++
  "sust_exp_mix_ok:\n  .zero 80\n" ++
  "sust_exp_mix_bad_user:\n  .zero 80\n"

def ziskSystemUserExecLogSlotTuplesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSystemUserExecLogSlotTuplesPrologue
  dataAsm     := ziskSystemUserExecLogSlotTuplesDataSection
}

end EvmAsm.Codegen
