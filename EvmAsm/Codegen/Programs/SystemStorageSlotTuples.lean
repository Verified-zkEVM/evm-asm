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

    lv44p.2.2: system rows are NOT all block_access_index 0. Begin-of-block system
    calls (EIP-2935/4788) run at index 0; END-of-block calls (EIP-7002/7251) run at
    index N+1, AFTER every user transaction. Both live in the same system log
    (`bv_system_storage_log`) with their real per-row index in the txindex array. To
    reconstruct the spec's ordered net-change sequence this helper runs THREE
    `exec_log_slot_tuples` passes with a txindex window filter and concatenates them
    in block_access_index order: begin-system (window [0,1)), then user (1..N), then
    end-system (window [1, 2^64)). Each pass independently re-seeds its running value
    from the FIRST matching row's `original`, which equals the running value at that
    point (original = the pre-write value, accumulated across prior segments), so the
    split passes preserve net-change continuity exactly without shared state.

    The caller sets `sust_sys_txindex_ptr` to the real system txindex array
    (`bv_system_storage_txindex`); a 0 ptr falls back to the all-zero array (so the
    standalone probe / legacy callers see every system row at index 0 = begin-only,
    byte-identical to the prior system-first behaviour). -/
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
  -- resolve the system txindex array (caller-set ptr, 0 => all-zero array)
  "  la t0, sust_sys_txindex_ptr; ld t0, 0(t0); bnez t0, .Lsust_systx_set; la t0, sust_zero_txindex\n" ++
  ".Lsust_systx_set:\n" ++
  "  la t1, sust_systx; sd t0, 0(t1)\n" ++
  -- PASS 1: begin-of-block system rows (block_access_index 0): txindex window [0,1)
  "  la t1, els_txfilter_lo; sd zero, 0(t1); la t1, els_txfilter_hi; li t2, 1; sd t2, 0(t1)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; la t0, sust_systx; ld a4, 0(t0); la a5, sust_sysbuf\n" ++
  "  jal ra, exec_log_slot_tuples\n" ++
  "  mv s8, a0                    # begin-system tuple count\n" ++
  -- PASS 2: user rows (block_access_index 1..N): no txindex filter
  "  la t1, els_txfilter_hi; sd zero, 0(t1)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s4; mv a3, s5; mv a4, s6; la a5, sust_userbuf\n" ++
  "  jal ra, exec_log_slot_tuples\n" ++
  "  mv s9, a0                    # user tuple count\n" ++
  -- PASS 3: end-of-block system rows (block_access_index >= 1, i.e. N+1): window [1, 2^64)
  "  la t1, els_txfilter_lo; li t2, 1; sd t2, 0(t1); la t1, els_txfilter_hi; li t2, -1; sd t2, 0(t1)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; la t0, sust_systx; ld a4, 0(t0); la a5, sust_endbuf\n" ++
  "  jal ra, exec_log_slot_tuples\n" ++
  "  la t0, sust_endcount; sd a0, 0(t0)        # end-system tuple count\n" ++
  -- clear the txindex filter so other exec_log_slot_tuples callers are unaffected
  "  la t1, els_txfilter_lo; sd zero, 0(t1); la t1, els_txfilter_hi; sd zero, 0(t1)\n" ++
  -- total = begin + user + end; bail (return true count) if it would overflow out
  "  la t0, sust_endcount; ld t0, 0(t0); add t6, s8, s9; add t6, t6, t0\n" ++
  "  li t1, " ++ toString bsrMaxTuplesPerSlot ++ "; bgtu t6, t1, .Lsust_ret_total\n" ++
  -- segment 1: sust_sysbuf[0..s8) -> out[0..s8)
  "  li t2, 0\n" ++
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
  "  beq t2, s9, .Lsust_copy_end_start\n" ++
  "  add t3, s8, t2; slli t4, t3, 5; slli t3, t3, 3; add t4, t4, t3\n" ++
  "  slli t3, t2, 5; slli t5, t2, 3; add t3, t3, t5\n" ++
  "  la t5, sust_userbuf; add t5, t5, t3; add t6, s7, t4\n" ++
  "  ld t0, 0(t5); sd t0, 0(t6); ld t0, 8(t5); sd t0, 8(t6)\n" ++
  "  ld t0, 16(t5); sd t0, 16(t6); ld t0, 24(t5); sd t0, 24(t6); ld t0, 32(t5); sd t0, 32(t6)\n" ++
  "  addi t2, t2, 1; j .Lsust_copy_user\n" ++
  ".Lsust_copy_end_start:\n" ++
  "  li t2, 0\n" ++
  ".Lsust_copy_end:\n" ++
  "  la t0, sust_endcount; ld t0, 0(t0); beq t2, t0, .Lsust_ret_total\n" ++
  "  add t3, s8, s9; add t3, t3, t2; slli t4, t3, 5; slli t3, t3, 3; add t4, t4, t3\n" ++
  "  slli t3, t2, 5; slli t5, t2, 3; add t3, t3, t5\n" ++
  "  la t5, sust_endbuf; add t5, t5, t3; add t6, s7, t4\n" ++
  "  ld t0, 0(t5); sd t0, 0(t6); ld t0, 8(t5); sd t0, 8(t6)\n" ++
  "  ld t0, 16(t5); sd t0, 16(t6); ld t0, 24(t5); sd t0, 24(t6); ld t0, 32(t5); sd t0, 32(t6)\n" ++
  "  addi t2, t2, 1; j .Lsust_copy_end\n" ++
  ".Lsust_ret_total:\n" ++
  "  la t0, sust_endcount; ld t0, 0(t0); add a0, s8, s9; add a0, a0, t0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- Production guest data for `system_user_exec_log_slot_tuples`.
    KEEP: sust_sysbuf / sust_userbuf / sust_endbuf (+ counts/txindex).
    `sust_out` is probe-only (production writes via caller a7 = `atsc_execbuf`). -/
def systemUserExecLogSlotTuplesData : String :=
  ".balign 8\n" ++
  "sust_zero_txindex:\n  .zero " ++ toString bvSystemStorageTxindexBytes ++ "\n" ++
  -- lv44p.2.2: caller-set real system txindex array (0 => sust_zero_txindex), and the
  -- resolved ptr + end-of-block tuple count used by the three-pass reconstruction.
  "sust_sys_txindex_ptr:\n  .zero 8\n" ++
  "sust_systx:\n  .zero 8\n" ++
  "sust_endcount:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "sust_sysbuf:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n" ++
  "sust_userbuf:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n" ++
  "sust_endbuf:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n"

/-- Probe-only output buffer for `zisk_system_user_exec_log_slot_tuples`. -/
def systemUserExecLogSlotTuplesProbeOutData : String :=
  ".balign 32\n" ++
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
  systemUserExecLogSlotTuplesProbeOutData ++ "\n" ++
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
