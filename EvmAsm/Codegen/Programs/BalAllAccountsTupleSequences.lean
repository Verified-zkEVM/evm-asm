/-
  EvmAsm.Codegen.Programs.BalAllAccountsTupleSequences

  `bal_all_accounts_tuple_sequences_consistent` (bead bmvmx.1.6.6 — the all-accounts
  tuple-sequence wrapper) — runs the per-account all-slots tuple check
  `account_tuple_sequences_consistent` (#8602) over EVERY account in the
  block_access_list, completing the consensus-binding per-tx tuple-sequence soundness
  layer (the Q5 gap) at the block level.

  Mirrors `bal_all_accounts_storage_consistent` (#8576): the top-level RECIPIENT is
  SKIPPED (its storage is keyed on `env.ADDRESS` big-endian and checked inside
  block_verdict), and each nested CALLEE's exec-log key is the address BYTE-REVERSED
  (LE stack-word), produced via `bal_addr_to_exec_log_key` (#8575) from the BAL
  account's 20-byte big-endian address. The derived key is passed to
  `account_tuple_sequences_consistent`, which compares — per storage slot — the BAL's
  declared per-tx `(block_access_index, new_value)` tuple sequence against the sequence
  reconstructed from the append-per-write storage exec-log + `exec_log_txindex`.

  Single-tx blocks degenerate to one tuple per slot (= the final), so this is a no-op
  there; it bites once the multi-tx loop sets `current_block_access_index` per tx
  (.57.11.6.3). A BAL account whose address item is not exactly 20 bytes is skipped.

  Conservative: any parse failure or per-account tuple-sequence mismatch returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalAddrExecLogKey
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.SlotTupleSequencesMatch
import EvmAsm.Codegen.Programs.AccountTupleSequencesConsistent

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_tuple_sequences_consistent
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec storage-log base   a3 = exec-log entry count   a4 = exec_log_txindex base
    a5 = recipient 20-byte big-endian address ptr (SKIPPED — checked in block_verdict)
    a0 (output) = 0 every non-recipient account's per-slot tuple sequences match exec / 1. -/
def balAllAccountsTupleSequencesConsistentFunction : String :=
  "bal_all_accounts_tuple_sequences_consistent:\n" ++
  "  li a6, 1                    # legacy ABI: one skipped recipient\n" ++
  "  j bal_all_accounts_tuple_sequences_consistent_skip_list\n" ++
  "bal_all_accounts_tuple_sequences_consistent_skip_list:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # exec-log base\n" ++
  "  mv s3, a3                   # exec-log entry count\n" ++
  "  mv s4, a4                   # exec_log_txindex base\n" ++
  "  mv s5, a5                   # skip-list ptr (32-byte-strided 20B BE entries)\n" ++
  "  mv s10, a6                  # skip-list count\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbatsc_fail\n" ++
  "  mv s6, a0                   # BAL cursor\n" ++
  "  mv s7, a1                   # BAL end\n" ++
  ".Lbatsc_loop:\n" ++
  "  beq s6, s7, .Lbatsc_ok\n" ++
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbatsc_fail\n" ++
  "  mv s6, a0; sub s8, a0, a2; mv s9, a2   # AccountChanges ptr/len\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbatsc_fail\n" ++
  "  jal ra, rlp_walk_next                             # item 0 = address\n" ++
  "  bnez a1, .Lbatsc_fail\n" ++
  "  li t2, 20; bne a2, t2, .Lbatsc_next   # not 20B -> skip\n" ++
  "  sub s11, a0, a2             # addr ptr (20B BE)\n" ++
  -- EIP-2935/EIP-4788 modeled-system rows are checked here too: the
  -- account-level comparator merges captured system storage rows with the user
  -- exec log, so forged system tuple sequences reject precisely instead of being
  -- hidden behind a modeled-account bypass.
  "  li t4, 0                    # skip-list index\n" ++
  ".Lbatsc_skip_outer:\n" ++
  "  beq t4, s10, .Lbatsc_callee # not in skip-list -> check it\n" ++
  "  slli t5, t4, 5; add t5, s5, t5\n" ++
  "  li t6, 0                    # byte index\n" ++
  ".Lbatsc_skip_cmp:\n" ++
  "  li a0, 20; beq t6, a0, .Lbatsc_next      # all 20 bytes equal skip entry -> skip\n" ++
  "  add a0, s11, t6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Lbatsc_skip_advance\n" ++
  "  addi t6, t6, 1; j .Lbatsc_skip_cmp\n" ++
  ".Lbatsc_skip_advance:\n" ++
  "  addi t4, t4, 1; j .Lbatsc_skip_outer\n" ++

  ".Lbatsc_callee:\n" ++
  "  mv a0, s11                              # addr ptr (20B BE)\n" ++
  "  la a1, batsc_key\n" ++
  "  jal ra, bal_addr_to_exec_log_key           # batsc_key = addr byte-reversed (LE callee key)\n" ++
  "  mv a0, s8; mv a1, s9; la a2, batsc_key; mv a3, s2; mv a4, s3; mv a5, s4; mv a6, s11\n" ++
  "  jal ra, account_tuple_sequences_consistent\n" ++
  "  bnez a0, .Lbatsc_fail\n" ++
  ".Lbatsc_next:\n" ++
  "  j .Lbatsc_loop\n" ++
  ".Lbatsc_ok:\n" ++
  "  li a0, 0; j .Lbatsc_ret\n" ++
  ".Lbatsc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbatsc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  ld s11, 96(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

/-- `zisk_bal_all_accounts_tuple_sequences_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : exec-log entry count
      bytes 24..56 : recipient address (20B BE in the low bytes, padded to 32)
      bytes 56..    : exec_log_txindex (count × 8B), exec-log (count × 128B), the BAL section
    Output: bytes 0..8 = status (0 consistent / 1 mismatch). -/
def ziskBalAllAccountsTupleSequencesConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # exec-log entry count\n" ++
  "  addi a5, t6, 24             # recipient ptr\n" ++
  "  addi a4, t6, 56             # exec_log_txindex base\n" ++
  "  slli t0, a3, 3; add a2, a4, t0   # exec-log base = txindex_base + count*8\n" ++
  "  slli t0, a3, 7; add a0, a2, t0   # BAL section ptr = log_base + count*128\n" ++
  "  jal ra, bal_all_accounts_tuple_sequences_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbatsc_pdone\n" ++
  balAllAccountsTupleSequencesConsistentFunction ++ "\n" ++
  accountTupleSequencesConsistentFunction ++ "\n" ++
  systemUserExecLogSlotTuplesFunction ++ "\n" ++
  balSlotTupleSequenceFunction ++ "\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  balAddrToExecLogKeyFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lbatsc_pdone:"

/-- `zisk_bal_all_accounts_tuple_sequences_consistent_skip_list`: probe for the new
    skip-list ABI. Input after the ziskemu length wrapper:
      +8 BAL len, +16 user exec-log entry count, +24 skip count, +32 system row count,
      +40 skip list, then user txindex array, user exec log, system log, and BAL section. -/
def ziskBalAllAccountsTupleSequencesConsistentSkipListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # user exec-log entry count\n" ++
  "  ld a6, 24(t6)               # skip-list count\n" ++
  "  ld t2, 32(t6)               # system row count\n" ++
  "  la t0, bv_system_storage_log_count; sd t2, 0(t0)\n" ++
  "  addi a5, t6, 40             # skip-list base\n" ++
  "  slli t0, a6, 5; add a4, a5, t0   # user txindex base\n" ++
  "  slli t0, a3, 3; add a2, a4, t0   # user exec-log base\n" ++
  "  slli t0, a3, 7; add t3, a2, t0   # system log input base\n" ++
  "  la t4, bv_system_storage_log; mv t5, t2\n" ++
  ".Lbatsc_sys_copy_rows:\n" ++
  "  beqz t5, .Lbatsc_sys_copy_done\n" ++
  "  ld t0, 0(t3); sd t0, 0(t4); ld t0, 8(t3); sd t0, 8(t4)\n" ++
  "  ld t0, 16(t3); sd t0, 16(t4); ld t0, 24(t3); sd t0, 24(t4)\n" ++
  "  ld t0, 32(t3); sd t0, 32(t4); ld t0, 40(t3); sd t0, 40(t4)\n" ++
  "  ld t0, 48(t3); sd t0, 48(t4); ld t0, 56(t3); sd t0, 56(t4)\n" ++
  "  ld t0, 64(t3); sd t0, 64(t4); ld t0, 72(t3); sd t0, 72(t4)\n" ++
  "  ld t0, 80(t3); sd t0, 80(t4); ld t0, 88(t3); sd t0, 88(t4)\n" ++
  "  ld t0, 96(t3); sd t0, 96(t4); ld t0, 104(t3); sd t0, 104(t4)\n" ++
  "  ld t0, 112(t3); sd t0, 112(t4); ld t0, 120(t3); sd t0, 120(t4)\n" ++
  "  addi t3, t3, 128; addi t4, t4, 128; addi t5, t5, -1; j .Lbatsc_sys_copy_rows\n" ++
  ".Lbatsc_sys_copy_done:\n" ++
  "  mv a0, t3                    # BAL section ptr = system base + system_count*128\n" ++
  "  jal ra, bal_all_accounts_tuple_sequences_consistent_skip_list\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbatsc_sl_pdone\n" ++
  balAllAccountsTupleSequencesConsistentFunction ++ "\n" ++
  accountTupleSequencesConsistentFunction ++ "\n" ++
  systemUserExecLogSlotTuplesFunction ++ "\n" ++
  balSlotTupleSequenceFunction ++ "\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  balAddrToExecLogKeyFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lbatsc_sl_pdone:"

def ziskBalAllAccountsTupleSequencesConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "batsc_key:\n  .zero 32\n" ++ "\n" ++
  accountTupleSequencesConsistentData ++ "\n" ++   -- atsc_* + tuple buffers
  accountTupleSequencesConsistentEmptySystemData ++ "\n" ++
  balSlotTupleSequenceData ++ "\n" ++               -- bts_*
  ziskRlpFieldToU64DataSection ++ "\n" ++           -- rfu_*
  execLogSlotTuplesData                             -- els_*

def ziskBalAllAccountsTupleSequencesConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsTupleSequencesConsistentPrologue
  dataAsm     := ziskBalAllAccountsTupleSequencesConsistentDataSection
}

def ziskBalAllAccountsTupleSequencesConsistentSkipListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsTupleSequencesConsistentSkipListPrologue
  dataAsm     := ziskBalAllAccountsTupleSequencesConsistentDataSection
}

end EvmAsm.Codegen
