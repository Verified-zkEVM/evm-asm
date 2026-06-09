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
import EvmAsm.Codegen.Programs.RlpRead
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
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # exec-log base\n" ++
  "  mv s3, a3                   # exec-log entry count\n" ++
  "  mv s4, a4                   # exec_log_txindex base\n" ++
  "  mv s5, a5                   # recipient 20B BE addr ptr\n" ++
  "  mv a0, s0; mv a1, s1; la a2, batsc_acct_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbatsc_fail\n" ++
  "  la t0, batsc_acct_count; ld s6, 0(t0)   # account count\n" ++
  "  li s7, 0                    # account index\n" ++
  ".Lbatsc_loop:\n" ++
  "  beq s7, s6, .Lbatsc_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s7; la a3, batsc_acct_off; la a4, batsc_acct_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbatsc_fail\n" ++
  "  la t0, batsc_acct_off; ld t1, 0(t0); add s8, s0, t1   # AccountChanges ptr\n" ++
  "  la t0, batsc_acct_len; ld s9, 0(t0)                   # AccountChanges len\n" ++
  "  mv a0, s8; mv a1, s9; li a2, 0; la a3, batsc_addr_off; la a4, batsc_addr_len\n" ++
  "  jal ra, rlp_list_nth_item                             # item 0 = address\n" ++
  "  bnez a0, .Lbatsc_fail\n" ++
  "  la t0, batsc_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lbatsc_next   # not 20B -> skip\n" ++
  "  la t0, batsc_addr_off; ld t1, 0(t0); add t3, s8, t1   # addr ptr (20B BE)\n" ++
  "  # --- skip the top-level recipient (BE-keyed storage checked in block_verdict) ---\n" ++
  "  li t4, 0\n" ++
  ".Lbatsc_rcmp:\n" ++
  "  li t5, 20; beq t4, t5, .Lbatsc_next      # all 20 bytes equal recipient -> skip\n" ++
  "  add t5, t3, t4; lbu t6, 0(t5)\n" ++
  "  add t5, s5, t4; lbu a0, 0(t5)\n" ++
  "  bne t6, a0, .Lbatsc_callee                # differs from recipient -> a callee\n" ++
  "  addi t4, t4, 1; j .Lbatsc_rcmp\n" ++
  ".Lbatsc_callee:\n" ++
  "  la t0, batsc_addr_off; ld t1, 0(t0); add a0, s8, t1   # addr ptr (re-derive across calls)\n" ++
  "  la a1, batsc_key\n" ++
  "  jal ra, bal_addr_to_exec_log_key           # batsc_key = addr byte-reversed (LE callee key)\n" ++
  "  mv a0, s8; mv a1, s9; la a2, batsc_key; mv a3, s2; mv a4, s3; mv a5, s4\n" ++
  "  jal ra, account_tuple_sequences_consistent\n" ++
  "  bnez a0, .Lbatsc_fail\n" ++
  ".Lbatsc_next:\n" ++
  "  addi s7, s7, 1; j .Lbatsc_loop\n" ++
  ".Lbatsc_ok:\n" ++
  "  li a0, 0; j .Lbatsc_ret\n" ++
  ".Lbatsc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbatsc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
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
  balSlotTupleSequenceFunction ++ "\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  balAddrToExecLogKeyFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lbatsc_pdone:"

def ziskBalAllAccountsTupleSequencesConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "batsc_acct_count:\n  .zero 8\n" ++
  "batsc_acct_off:\n  .zero 8\n" ++
  "batsc_acct_len:\n  .zero 8\n" ++
  "batsc_addr_off:\n  .zero 8\n" ++
  "batsc_addr_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "batsc_key:\n  .zero 32\n" ++ "\n" ++
  accountTupleSequencesConsistentData ++ "\n" ++   -- atsc_* + tuple buffers
  balSlotTupleSequenceData ++ "\n" ++               -- bts_*
  ziskRlpFieldToU64DataSection ++ "\n" ++           -- rfu_*
  execLogSlotTuplesData                             -- els_*

def ziskBalAllAccountsTupleSequencesConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsTupleSequencesConsistentPrologue
  dataAsm     := ziskBalAllAccountsTupleSequencesConsistentDataSection
}

end EvmAsm.Codegen
