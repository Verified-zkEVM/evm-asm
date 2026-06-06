/-
  EvmAsm.Codegen.Programs.BlockVerdict

  Full state-transition verdict: rebuild header RLP, validate header pair,
  recompute post-state root with system writes + BAL + withdrawals, and compare
  against the payload state root. Static block_state_root arenas are sized from
  execution-specs limits; see docs/agents/eest-static-layout.md.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.SystemWrites
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.BalAccountStateRoot
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptDeleteAcc
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.AccountFieldGetters
import EvmAsm.Codegen.Programs.BalCodePreimages
import EvmAsm.Codegen.Programs.BalAccountAccessDescriptors
import EvmAsm.Codegen.Programs.BalStorageAccessDescriptors
import EvmAsm.Codegen.Programs.BlockVerdictModeledSystem
import EvmAsm.Codegen.Programs.BlockhashRequiredHeaders
import EvmAsm.Codegen.Programs.BlockRlpSize
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.BlockVerdictGasResults
import EvmAsm.Codegen.Programs.BlockVerdictTransactions
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
namespace EvmAsm.Codegen

open EvmAsm.Rv64

private def bsrBalGasCost : Nat := 2000
/-- Static BAL/state replay arena capacity. This is sized like the former 1G
    worst-case BAL budget, but high declared block gas is not itself a layout
    error: the guest first applies Amsterdam's gas-derived BAL rule, then checks
    actual decoded item counts against these arenas. -/
private def bsrMaxBalItems : Nat := 500000
private def bsrModeledSystemChanges : Nat := 2
private def bsrMaxWithdrawalChanges : Nat := 16
private def bsrMaxAuxChanges : Nat := bsrModeledSystemChanges + bsrMaxWithdrawalChanges
private def bsrMaxStateChanges : Nat :=
  bsrMaxBalItems + bsrModeledSystemChanges + bsrMaxWithdrawalChanges
private def bsrMaxAccessAccounts : Nat := runtimeAccessAccountOutcomeCapacity
private def bsrMaxAccountAccessOutcomes : Nat := runtimeAccessAccountOutcomeCapacity
private def bsrMaxStorageAccessOutcomes : Nat := storageAccessOutcomeMaxRecords

private def bsrAccountRecordBytes : Nat := 24
private def bsrPathBytes : Nat := 64
private def bsrEncodedAccountBytes : Nat := 256
private def bsrSystemAccountBytes : Nat := 128
private def bsrStateChangeBytes : Nat := 40
private def baapStorageDescBytes : Nat := 40

/-! ## bsr_sys_change -- record one system-contract storage-write change.
    a0 = contract addr ptr (20 B)   a1 = slot_key ptr (32 B)
    a2 = value ptr   a3 = value len   a4 = change index
    Reads shared state from bsr_root_p / bsr_wit_p / bsr_wl_v; writes the change
    entry at bsr_changes[index]. a0 (output) = 0 ok / 1 conservative. -/
def bsrSysChangeFunction : String :=
  "bsr_sys_change:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  # keccak(addr, 20) -> bsr_kbuf\n" ++
  "  mv a0, s0; li a1, 20; la a2, bsr_kbuf; jal ra, zkvm_keccak256\n" ++
  "  # path = bsr_paths + 64*index; bytes_to_nibbles(bsr_kbuf, 32, path)\n" ++
  "  slli t0, s4, 6; la t1, bsr_paths; add t2, t1, t0\n" ++
  "  la t3, bsr_pathp; sd t2, 0(t3)              # stash path ptr\n" ++
  "  la a0, bsr_kbuf; li a1, 32; mv a2, t2; jal ra, bytes_to_nibbles\n" ++
  "  # mpt_walk(root, witness, wlen, path, 64, bsr_acct, bsr_acct_len)\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, bsr_pathp; ld a3, 0(t0); li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  bnez a0, .Lbsc_fail\n" ++
  "  # account_apply_storage_slot_acc(acct, len, slot, val, vlen, newacct, bsr_tmplen)\n" ++
  "  # The accumulator helper replays non-empty system-contract storage roots.\n" ++
  "  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); mv a2, s1; mv a3, s2; mv a4, s3\n" ++
  "  slli t0, s4, 7; la t1, bsr_newaccts; add a5, t1, t0; la a6, bsr_tmplen\n" ++
  "  jal ra, account_apply_storage_slot_acc\n" ++
  "  bnez a0, .Lbsc_fail\n" ++
  "  # record change[index] = (path, 64, newacct, tmplen, is_insert=0) -- 40 B\n" ++
  "  slli t0, s4, 5; slli t4, s4, 3; add t0, t0, t4; la t1, bsr_changes; add t1, t1, t0\n" ++
  "  la t2, bsr_pathp; ld t2, 0(t2); sd t2, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  slli t0, s4, 7; la t2, bsr_newaccts; add t2, t2, t0; sd t2, 16(t1)\n" ++
  "  la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1)\n" ++
  "  sd zero, 32(t1)             # is_insert = 0 (system contract MODIFY)\n" ++
  "  li a0, 0; j .Lbsc_ret\n" ++
  ".Lbsc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## bsr_beacon_change -- record the EIP-4788 two-slot account change.
    EIP-4788 writes two storage slots in the same beacon-roots account.  The
    state trie must therefore receive one account-leaf descriptor whose
    storageRoot reflects both slot writes, not two duplicate state descriptors.
    a4 = change index. -/
def bsrBeaconChangeFunction : String :=
  "bsr_beacon_change:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a4                   # state change index\n" ++
  "  la a0, bsr_addr_4788; li a1, 20; la a2, bsr_kbuf; jal ra, zkvm_keccak256\n" ++
  "  slli t0, s0, 6; la t1, bsr_paths; add t2, t1, t0\n" ++
  "  la t3, bsr_pathp; sd t2, 0(t3)\n" ++
  "  la a0, bsr_kbuf; li a1, 32; mv a2, t2; jal ra, bytes_to_nibbles\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, bsr_pathp; ld a3, 0(t0); li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); li a2, 2; la a3, aps_off; la a4, aps_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lbbc_fail\n" ++
  "  la t0, aps_off; ld t0, 0(t0); la t1, bsr_acct; add t1, t1, t0; la t0, baap_storage_root_ptr; sd t1, 0(t0)\n" ++
  "  la t2, aps_empty_root; li t3, 32\n" ++
  ".Lbbc_empty_cmp:\n" ++
  "  beqz t3, .Lbbc_empty\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbbc_nonempty\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbbc_empty_cmp\n" ++
  ".Lbbc_empty:\n" ++
  "  li t0, 1; la t1, baap_storage_empty_flag; sd t0, 0(t1); j .Lbbc_init\n" ++
  ".Lbbc_nonempty:\n" ++
  "  la t0, baap_storage_empty_flag; sd zero, 0(t0)\n" ++
  ".Lbbc_init:\n" ++
  "  la t0, baap_storage_values; la t1, baap_storage_value_cursor; sd t0, 0(t1)\n" ++
  "  la t0, baap_sc_out_count; sd zero, 0(t0)\n" ++
  "  # Descriptor 0: timestamp slot -> timestamp value.\n" ++
  "  la t0, swd_4788_vlen; ld a1, 0(t0); beqz a1, .Lbbc_after_ts\n" ++
  "  la a0, swd_4788_val; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, srss_rlpval_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la a0, swd_4788_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256\n" ++
  "  la a0, srss_key; li a1, 32; la a2, baap_storage_paths; jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_ts_insert\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la a3, baap_storage_paths; li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbbc_ts_modify\n" ++
  "  li t0, 1; bne a0, t0, .Lbbc_fail\n" ++
  ".Lbbc_ts_insert:\n" ++
  "  li t5, 1; j .Lbbc_ts_mode\n" ++
  ".Lbbc_ts_modify:\n" ++
  "  li t5, 0\n" ++
  ".Lbbc_ts_mode:\n" ++
  "  la t1, baap_storage_desc; la t2, baap_storage_paths; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)\n" ++
  "  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1); la t4, srss_rlpval_len; ld t4, 0(t4); sd t4, 24(t1); sd t5, 32(t1)\n" ++
  "  add t3, t3, t4; addi t3, t3, 7; andi t3, t3, -8; sd t3, 0(t2)\n" ++
  "  la t0, baap_sc_out_count; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lbbc_after_ts:\n" ++
  "  # Descriptor 1: timestamp+8191 slot -> parent_beacon_block_root, unless zero.\n" ++
  "  la t0, swd_4788_root_vlen; ld a1, 0(t0); beqz a1, .Lbbc_apply_storage\n" ++
  "  la a0, swd_4788_root_val; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, srss_rlpval_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la a0, swd_4788_root_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256\n" ++
  "  la a0, srss_key; li a1, 32; la a2, baap_storage_paths; addi a2, a2, 64; jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_root_insert\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la a3, baap_storage_paths; addi a3, a3, 64; li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbbc_root_modify\n" ++
  "  li t0, 1; bne a0, t0, .Lbbc_fail\n" ++
  ".Lbbc_root_insert:\n" ++
  "  li t5, 1; j .Lbbc_root_mode\n" ++
  ".Lbbc_root_modify:\n" ++
  "  li t5, 0\n" ++
  ".Lbbc_root_mode:\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)\n" ++
  "  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1); la t4, srss_rlpval_len; ld t4, 0(t4); sd t4, 24(t1); sd t5, 32(t1)\n" ++
  "  add t3, t3, t4; addi t3, t3, 7; andi t3, t3, -8; sd t3, 0(t2)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)\n" ++
  ".Lbbc_apply_storage:\n" ++
  "  la t0, baap_sc_out_count; ld a4, 0(t0); beqz a4, .Lbbc_fail\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); beqz t0, .Lbbc_apply_nonempty\n" ++
  "  la a0, aps_empty_root; mv a1, zero; mv a2, zero; la a3, baap_storage_desc; j .Lbbc_apply_call\n" ++
  ".Lbbc_apply_nonempty:\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0); la a3, baap_storage_desc\n" ++
  ".Lbbc_apply_call:\n" ++
  "  la a5, aps_newsroot; jal ra, mpt_state_root_ins\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); la a2, aps_newsroot\n" ++
  "  slli t0, s0, 7; la t1, bsr_newaccts; add a3, t1, t0; la a4, bsr_tmplen\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  slli t0, s0, 5; slli t4, s0, 3; add t0, t0, t4; la t1, bsr_changes; add t1, t1, t0\n" ++
  "  la t2, bsr_pathp; ld t2, 0(t2); sd t2, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  slli t0, s0, 7; la t2, bsr_newaccts; add t2, t2, t0; sd t2, 16(t1)\n" ++
  "  la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1); sd zero, 32(t1)\n" ++
  "  li a0, 0; j .Lbbc_ret\n" ++
  ".Lbbc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## block_state_root -- post-state root after system writes + withdrawals.
    a0 = pre-state root ptr   a1 = witness   a2 = witness_len
    a3 = wds descriptors   a4 = n_wds   a5 = out_root   a6 = SSZ_BASE
    a0 (output) = 0 ok / 1 conservative (any miss / unsupported case). -/
def blockStateRootFunction : String :=
  "block_state_root:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  la t0, bsr_root_p; sd a0, 0(t0)\n" ++
  "  la t0, bsr_wit_p;  sd a1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;   sd a2, 0(t0)\n" ++
  "  la t0, bsr_ssz_p;  sd a6, 0(t0)\n" ++
  "  la t0, bsr_fail_code; sd zero, 0(t0); li t1, 262144; bgtu a2, t1, .Lbsr_cons_change_cap\n" ++
  "  mv s3, a3                   # wds descriptors\n" ++
  "  mv s4, a4                   # n_wds\n" ++
  "  mv s5, a5                   # out_root\n" ++
  "  # derive the system writes (SSZ_BASE in a6)\n" ++
  "  mv a0, a6; jal ra, system_write_descriptors\n" ++
  "  # system change 0 = EIP-2935\n" ++
  "  la a0, bsr_addr_2935; la a1, swd_2935_slot; la a2, swd_2935_val\n" ++
  "  la t0, swd_2935_vlen; ld a3, 0(t0); li a4, 0\n" ++
  "  jal ra, bsr_sys_change; bnez a0, .Lbsr_cons_sys2935\n" ++
  "  # system change 1 = EIP-4788 (timestamp + parent-root slots in one account)\n" ++
  "  li a4, 1\n" ++
  "  jal ra, bsr_beacon_change; bnez a0, .Lbsr_cons_sys4788\n" ++
  "  # BAL account changes are tx-execution account post-values.\n" ++
  "  li s1, 2                     # change counter (2 system changes already recorded)\n" ++
  "  la t0, bsr_changed_account_count; sd zero, 0(t0)\n" ++
  "  la t0, bsr_bal_count; sd zero, 0(t0)\n" ++
  "  la t0, bsr_ssz_p; ld t0, 0(t0); addi t0, t0, 60; la t1, bsr_exec_p; sd t0, 0(t1)\n" ++
  "  la t0, bsr_ssz_p; ld a0, 0(t0); la a1, bsr_bal_start; la a2, bsr_bal_len; la a3, bsr_bal_count\n" ++
  "  jal ra, bal_section_info; bnez a0, .Lbsr_cons_bal_section\n" ++
  "  la t0, bsr_bal_count; ld t6, 0(t0); beqz t6, .Lbsr_bal_done\n" ++
  "  la t0, bsr_exec_p; ld a0, 0(t0); addi a0, a0, 412; jal ra, bgv_u64le\n" ++
  "  li t0, " ++ toString bsrBalGasCost ++ "; divu t1, a0, t0\n" ++
  "  la t2, bsr_bal_count; ld t6, 0(t2); bgtu t6, t1, .Lbsr_cons_change_cap; add t0, s1, t6; li t1, " ++ toString bsrMaxStateChanges ++ "; bgtu t0, t1, .Lbsr_cons_change_cap\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, bsr_bal_start; ld a3, 0(t0); la t0, bsr_bal_len; ld a4, 0(t0); mv a5, t6\n" ++
  "  li t0, 1; la t1, bara_skip_modeled_system; sd t0, 0(t1)\n" ++
  "  la a6, basr_records; la a7, basr_accounts\n" ++
  "  jal ra, bal_account_record_array; bnez a0, .Lbsr_cons_bal_records\n" ++
  "  # BAL storage replay reads the shared witness globals.\n" ++
  "  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)\n" ++
  "  li s0, 0                     # scan BAL records; append only changed accounts\n" ++
  ".Lbsr_bal_copy:\n" ++
  "  la t6, bsr_bal_count; ld t6, 0(t6); beq s0, t6, .Lbsr_bal_copied\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n" ++
  "  ld t4, 16(t3); li t5, 3; beq t4, t5, .Lbsr_bal_copy_load_item\n" ++
  ".Lbsr_bal_copy_load_item:\n" ++
  "  la t0, bsr_bal_start; ld a0, 0(t0); la t0, bsr_bal_len; ld a1, 0(t0); mv a2, s0\n" ++
  "  la a3, baada_item_off; la a4, baada_item_len\n" ++
  "  jal ra, rlp_list_nth_item; bnez a0, .Lbsr_cons_bal_desc\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n" ++
  "  ld a0, 0(t3); ld a1, 8(t3); la t0, bsr_bal_start; ld t0, 0(t0); la t1, baada_item_off; ld t1, 0(t1); add a2, t0, t1\n" ++
  "  la t1, baada_item_len; ld a3, 0(t1); ld a4, 16(t3)\n" ++
  "  la t0, bsr_bal_item_ptr; sd a2, 0(t0); la t0, bsr_bal_item_len; sd a3, 0(t0)\n" ++
  "  mv a0, a2; mv a1, a3; jal ra, bal_account_is_modeled_system\n" ++
  "  li t0, 1; beq a0, t0, .Lbsr_bal_copy_system2935\n  li t0, 2; beq a0, t0, .Lbsr_bal_copy_system4788\n  bnez a0, .Lbsr_cons_bal_desc\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n  ld t4, 16(t3); li t5, 3; beq t4, t5, .Lbsr_bal_copy_next\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n" ++
  "  ld a0, 0(t3); ld a1, 8(t3); la t0, bsr_bal_item_ptr; ld a2, 0(t0); la t0, bsr_bal_item_len; ld a3, 0(t0); ld a4, 16(t3)\n" ++
  "  slli t2, s1, 5; slli t3, s1, 3; add t2, t2, t3; la t3, bsr_changes; add a5, t3, t2\n" ++
  "  slli t2, s1, 6; la t3, basr_paths; add a6, t3, t2\n" ++
  "  slli t2, s1, 8; la t3, basr_values; add a7, t3, t2\n" ++
  "  jal ra, bal_account_change_descriptor; bnez a0, .Lbsr_cons_bal_desc\n" ++
  "  la t0, bsr_changed_account_count; ld t1, 0(t0); li t2, " ++ toString bsrMaxAccessAccounts ++ "; bgeu t1, t2, .Lbsr_changed_addr_record_skip\n" ++
  "  slli t2, t1, 5; la t3, bsr_changed_accounts; add t3, t3, t2\n" ++
  "  la t4, bsr_bal_item_ptr; ld a0, 0(t4); la t4, bsr_bal_item_len; ld a1, 0(t4); li a2, 0; la a3, baada_item_off; la a4, baada_item_len\n" ++
  "  jal ra, rlp_list_nth_item; bnez a0, .Lbsr_cons_bal_desc\n" ++
  "  la t4, baada_item_len; ld t4, 0(t4); li t5, 20; bne t4, t5, .Lbsr_cons_bal_desc\n" ++
  "  la t4, bsr_bal_item_ptr; ld t4, 0(t4); la t5, baada_item_off; ld t5, 0(t5); add t4, t4, t5\n" ++
  "  li t5, 0\n" ++
  ".Lbsr_changed_addr_copy:\n" ++
  "  li t6, 20; beq t5, t6, .Lbsr_changed_addr_pad\n" ++
  "  add a0, t4, t5; lbu a1, 0(a0); add a0, t3, t5; sb a1, 0(a0)\n" ++
  "  addi t5, t5, 1; j .Lbsr_changed_addr_copy\n" ++
  ".Lbsr_changed_addr_pad:\n" ++
  "  li t6, 32; beq t5, t6, .Lbsr_changed_addr_done\n" ++
  "  add a0, t3, t5; sb zero, 0(a0); addi t5, t5, 1; j .Lbsr_changed_addr_pad\n" ++
  ".Lbsr_changed_addr_done:\n" ++
  "  addi t1, t1, 1; la t0, bsr_changed_account_count; sd t1, 0(t0)\n" ++
  ".Lbsr_changed_addr_record_skip:\n" ++
  "  addi s1, s1, 1\n" ++
  ".Lbsr_bal_copy_next:\n" ++
  "  addi s0, s0, 1; j .Lbsr_bal_copy\n" ++
  ".Lbsr_bal_copy_system2935:\n  la t0, bsr_bal_item_ptr; ld a0, 0(t0); la t0, bsr_bal_item_len; ld a1, 0(t0); li a2, 0\n  jal ra, bsr_apply_modeled_system_post_fields; bnez a0, .Lbsr_cons_bal_desc\n  j .Lbsr_bal_copy_next\n" ++
  ".Lbsr_bal_copy_system4788:\n  la t0, bsr_bal_item_ptr; ld a0, 0(t0); la t0, bsr_bal_item_len; ld a1, 0(t0); li a2, 1\n  jal ra, bsr_apply_modeled_system_post_fields; bnez a0, .Lbsr_cons_bal_desc\n  j .Lbsr_bal_copy_next\n" ++
  ".Lbsr_bal_copied:\n" ++
  "  la t6, bsr_bal_count; ld t6, 0(t6); bnez t6, .Lbsr_access_descriptors\n" ++
  ".Lbsr_bal_done:\n" ++
  ".Lbsr_access_descriptors:\n" ++
  "  la t0, " ++ runtimeAccessAccountOutcomeCountLabel ++ "; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbsr_storage_access\n" ++
  "  add t2, s1, t1; li t3, " ++ toString bsrMaxStateChanges ++ "; bgtu t2, t3, .Lbsr_cons_change_cap\n" ++
  "  slli t2, s1, 5; slli t3, s1, 3; add t2, t2, t3; la t3, bsr_changes; add a4, t3, t2\n" ++
  "  la a5, bsr_access_paths\n" ++
  "  la a0, " ++ runtimeAccessAccountOutcomeTableLabel ++ "; mv a1, t1\n" ++
  "  la a2, bsr_changed_accounts; la t0, bsr_changed_account_count; ld a3, 0(t0)\n" ++
  "  la a6, bsr_access_count\n" ++
  "  jal ra, bal_account_access_outcome_descriptors; bnez a0, .Lbsr_cons_account_access\n" ++
  "  la t0, bsr_access_count; ld t0, 0(t0); add s1, s1, t0\n" ++
  ".Lbsr_storage_access:\n" ++
  "  la t0, evm_storage_access_outcome_count; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbsr_withdrawals\n" ++
  "  add t2, s1, t1; li t3, " ++ toString bsrMaxStateChanges ++ "; bgtu t2, t3, .Lbsr_cons_change_cap\n" ++
  "  la t0, bsr_storage_access_window; li t2, 1; sd t2, 0(t0); sd zero, 8(t0); sd t1, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, bsr_storage_access_path_count; sd zero, 0(t0)\n" ++
  "  li s0, 0\n" ++
  ".Lbsr_storage_access_loop:\n" ++
  "  la t0, bsr_changed_account_count; ld t6, 0(t0)\n" ++
  "  beq s0, t6, .Lbsr_withdrawals\n" ++
  "  slli t2, s0, 5; la t3, bsr_changed_accounts; add t4, t3, t2; la t3, bsr_storage_account_token; add t3, t3, t2\n" ++
  "  sd zero, 0(t3); sw zero, 8(t3); li t5, 0\n" ++
  ".Lbsr_storage_token_copy:\n" ++
  "  li a0, 20; beq t5, a0, .Lbsr_storage_token_done\n" ++
  "  add a0, t4, t5; lbu a1, 0(a0); addi a0, t5, 12; add a0, t3, a0; sb a1, 0(a0)\n" ++
  "  addi t5, t5, 1; j .Lbsr_storage_token_copy\n" ++
  ".Lbsr_storage_token_done:\n" ++
  "  slli t2, s1, 5; slli t3, s1, 3; add t2, t2, t3; la t3, bsr_changes; add a5, t3, t2\n" ++
  "  la t0, bsr_storage_access_path_count; ld t2, 0(t0); slli t2, t2, 6; la t3, bsr_storage_access_paths; add a6, t3, t2\n" ++
  "  la a0, evm_storage_access_outcomes; la t0, evm_storage_access_outcome_count; ld a1, 0(t0); la a2, bsr_storage_access_window; li a3, 1\n" ++
  "  slli t2, s0, 5; la t3, bsr_storage_account_token; add a4, t3, t2; la a7, bsr_access_count\n" ++
  "  jal ra, bal_storage_access_outcome_descriptors; bnez a0, .Lbsr_cons_storage_access\n" ++
  "  la t0, bsr_access_count; ld t0, 0(t0); add t2, s1, t0; li t3, " ++ toString bsrMaxStateChanges ++ "; bgtu t2, t3, .Lbsr_cons_change_cap\n" ++
  "  la t4, bsr_storage_access_path_count; ld t5, 0(t4); add t5, t5, t0; li t6, " ++ toString bsrMaxStorageAccessOutcomes ++ "; bgtu t5, t6, .Lbsr_cons_change_cap; sd t5, 0(t4)\n" ++
  "  mv s1, t2; addi s0, s0, 1; j .Lbsr_storage_access_loop\n" ++
  ".Lbsr_withdrawals:\n" ++
  "  # withdrawal changes: change counter s1 starts after system/BAL changes.\n" ++
  "  # Zero-amount withdrawals are no-ops and do not advance the change counter.\n" ++
  "  li s0, 0                     # withdrawal index\n" ++
  ".Lbsr_wl:\n" ++
  "  beq s0, s4, .Lbsr_apply\n" ++
  "  slli t0, s0, 4; add t0, s3, t0; ld a0, 0(t0); ld a1, 8(t0)   # wd[i] rlp ptr/len\n" ++
  "  slli t1, s1, 6; la t2, bsr_paths; add a2, t2, t1; la a3, bsr_delta\n" ++
  "  jal ra, withdrawal_to_path_delta; bnez a0, .Lbsr_cons_wd_decode\n" ++
  "  # zero-amount withdrawal (delta == 0) -> no state change -> skip.\n" ++
  "  la t0, bsr_delta; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2\n" ++
  "  ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbsr_wl_next\n" ++
  "  li t0, " ++ toString bsrMaxWithdrawalChanges ++ "; bgeu s0, t0, .Lbsr_cons_change_cap\n" ++
  "  # Repeated withdrawals to the same recipient accumulate into one state change.\n" ++
  "  li t6, 2                     # scan recorded withdrawal changes [2, s1)\n" ++
  ".Lbsr_dup_scan:\n" ++
  "  beq t6, s1, .Lbsr_no_dup\n" ++
  "  slli t0, t6, 5; slli t1, t6, 3; add t0, t0, t1; la t1, bsr_changes; add t0, t1, t0\n" ++
  "  ld t0, 0(t0)                  # prev path from descriptor (bsr_paths or basr_paths)\n" ++
  "  addi t2, s0, " ++ toString bsrModeledSystemChanges ++ "; slli t2, t2, 6; la t1, bsr_paths; add t1, t1, t2 # current withdrawal path\n" ++
  "  li t2, 64\n" ++
  ".Lbsr_dup_cmp:\n" ++
  "  beqz t2, .Lbsr_dup_found\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbsr_dup_next\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbsr_dup_cmp\n" ++
  ".Lbsr_dup_next:\n" ++
  "  addi t6, t6, 1; j .Lbsr_dup_scan\n" ++
  ".Lbsr_dup_found:\n" ++
  "  slli t0, t6, 5; slli t1, t6, 3; add t0, t0, t1; la t1, bsr_changes; add t0, t1, t0\n" ++
  "  la t1, bsr_prev_desc; sd t0, 0(t1)\n" ++
  "  ld t1, 16(t0); la t2, bsr_prev_acct; sd t1, 0(t2)\n" ++
  "  ld a1, 24(t0); mv a0, t1; la a2, bsr_delta; la a3, bsr_acct; la a4, bsr_tmplen\n" ++
  "  jal ra, account_add_balance; bnez a0, .Lbsr_cons_dup_add\n" ++
  "  la t0, bsr_prev_acct; ld a0, 0(t0); la a1, bsr_acct; la t0, bsr_tmplen; ld a2, 0(t0)\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  la t0, bsr_prev_desc; ld t0, 0(t0); la t1, bsr_tmplen; ld t1, 0(t1); sd t1, 24(t0)\n" ++
  "  j .Lbsr_wl_next\n" ++
  ".Lbsr_no_dup:\n" ++
  "  li t0, " ++ toString bsrMaxStateChanges ++ "; bge s1, t0, .Lbsr_cons_change_cap # cap to the change-buffer size\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  addi t1, s0, " ++ toString bsrModeledSystemChanges ++ "; slli t1, t1, 6; la t2, bsr_paths; add a3, t2, t1; li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbsr_wl_found\n" ++
  "  li t0, 1; bne a0, t0, .Lbsr_cons_wd_walk   # parse-fail (2) -> conservative\n" ++
  "  # NOT-FOUND: create the account. fresh = empty_account + delta (balance 0 -> delta).\n" ++
  "  la a0, bsr_empty_account; li a1, 70; la a2, bsr_delta\n" ++
  "  addi t1, s0, " ++ toString bsrModeledSystemChanges ++ "; slli t1, t1, 7; la t2, bsr_newaccts; add a3, t2, t1; la a4, bsr_tmplen\n" ++
  "  jal ra, account_add_balance; bnez a0, .Lbsr_cons_new_add\n" ++
  "  li t5, 1; j .Lbsr_wl_record   # is_insert = 1\n" ++
  ".Lbsr_wl_found:\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); la a2, bsr_delta\n" ++
  "  addi t1, s0, " ++ toString bsrModeledSystemChanges ++ "; slli t1, t1, 7; la t2, bsr_newaccts; add a3, t2, t1; la a4, bsr_tmplen\n" ++
  "  jal ra, account_add_balance; bnez a0, .Lbsr_cons_found_add\n" ++
  "  li t5, 0                      # is_insert = 0 (MODIFY existing)\n" ++
  ".Lbsr_wl_record:\n" ++
  "  slli t0, s1, 5; slli t6, s1, 3; add t0, t0, t6; la t1, bsr_changes; add t1, t1, t0   # *40\n" ++
  "  addi t2, s0, " ++ toString bsrModeledSystemChanges ++ "; slli t2, t2, 6; la t3, bsr_paths; add t3, t3, t2; sd t3, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  addi t2, s0, " ++ toString bsrModeledSystemChanges ++ "; slli t2, t2, 7; la t3, bsr_newaccts; add t3, t3, t2; sd t3, 16(t1)\n" ++
  "  la t3, bsr_tmplen; ld t3, 0(t3); sd t3, 24(t1)\n" ++
  "  sd t5, 32(t1)               # is_insert\n" ++
  "  addi s1, s1, 1               # advance change counter (only on a recorded change)\n" ++
  ".Lbsr_wl_next:\n" ++
  "  addi s0, s0, 1; j .Lbsr_wl\n" ++
  ".Lbsr_apply:\n" ++
  "  la t0, bsr_change_count; sd s1, 0(t0)\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la a3, bsr_changes; mv a4, s1; mv a5, s5     # change count = s1 (40-byte recs)\n" ++
  "  jal ra, mpt_state_root_ins\n" ++
  "  beqz a0, .Lbsr_ret\n" ++
  "  li t0, 130; la t1, bsr_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lbsr_ret\n" ++
  ".Lbsr_cons_sys2935:\n" ++
  "  li t0, 101; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_sys4788:\n" ++
  "  li t0, 102; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_bal_section:\n" ++
  "  li t0, 110; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_change_cap:\n" ++
  "  li t0, 111; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_bal_records:\n" ++
  "  li t0, 112; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_bal_desc:\n" ++
  "  li t0, 113; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_account_access:\n" ++
  "  li t0, 114; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_storage_access:\n" ++
  "  li t0, 115; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_wd_decode:\n" ++
  "  li t0, 120; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_dup_add:\n" ++
  "  li t0, 121; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_wd_walk:\n" ++
  "  li t0, 122; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_new_add:\n" ++
  "  li t0, 123; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_found_add:\n" ++
  "  li t0, 124; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons:\n" ++
  "  li a0, 1\n" ++
  ".Lbsr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## public_keys_valid -- structural stateless-input public key guard.
    a0 = SSZ_BASE   a1 = exec_payload ptr
    a0 (output) = 0 ok, 1 malformed/mismatched public_keys.

    Amsterdam passes `stateless_input.public_keys` to `execute_block`; the
    executable spec rejects if the count differs from the transaction count,
    and then compares each supplied 65-byte uncompressed SEC1 public key against
    recovered transaction keys. This guard implements the count check plus the
    cheap canonical shape checks that catch malformed optional-proof fixtures:
    each key is exactly an SSZ fixed 65-byte entry, starts with 0x04, and does
    not have an all-zero 64-byte coordinate payload. -/
def publicKeysValidFunction : String :=
  "public_keys_valid:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s1, a1                   # exec_payload\n" ++
  "  # tx_count from the SSZ transactions list.\n" ++
  "  addi a0, s1, 504; jal ra, bgv_u32le\n" ++
  "  mv s2, a0                   # transactions_offset\n" ++
  "  addi a0, s1, 508; jal ra, bgv_u32le\n" ++
  "  mv s3, a0                   # withdrawals_offset\n" ++
  "  li s4, 0                    # tx_count\n" ++
  "  bleu s3, s2, .Lpkv_have_tx_count\n" ++
  "  sub t0, s3, s2\n" ++
  "  li t1, 4; bltu t0, t1, .Lpkv_fail\n" ++
  "  add t2, s1, s2\n" ++
  "  mv a0, t2; jal ra, bgv_u32le\n" ++
  "  andi t1, a0, 3; bnez t1, .Lpkv_fail\n" ++
  "  srli s4, a0, 2\n" ++
  "  slli t1, s4, 2; bgtu t1, t0, .Lpkv_fail\n" ++
  ".Lpkv_have_tx_count:\n" ++
  "  # public_keys start = SSZ_BASE + outer.offsets[3]. End = zisk input\n" ++
  "  # payload start + host length; host length includes schema id + SSZ bytes.\n" ++
  "  addi a0, s0, 12; jal ra, bgv_u32le\n" ++
  "  add s5, s0, a0              # public_keys ptr\n" ++
  "  li a0, 0x40000008; jal ra, bgv_u64le\n" ++
  "  li t0, 0x40000010; add s6, t0, a0     # end of host payload\n" ++
  "  bltu s6, s5, .Lpkv_fail\n" ++
  "  sub s7, s6, s5              # public_keys byte length\n" ++
  "  li t0, 65\n" ++
  "  remu t1, s7, t0; bnez t1, .Lpkv_fail\n" ++
  "  divu s8, s7, t0             # public key count\n" ++
  "  bne s8, s4, .Lpkv_fail\n" ++
  "  la t0, bv_public_keys_ptr; sd s5, 0(t0)\n" ++
  "  la t0, bv_public_keys_len; sd s7, 0(t0)\n" ++
  "  li s9, 0\n" ++
  ".Lpkv_loop:\n" ++
  "  beq s9, s8, .Lpkv_ok\n" ++
  "  li t0, 65; mul t1, s9, t0; add t2, s5, t1\n" ++
  "  lbu t3, 0(t2); li t4, 4; bne t3, t4, .Lpkv_fail\n" ++
  "  li t3, 1; li t4, 0\n" ++
  ".Lpkv_coord_loop:\n" ++
  "  li t5, 65; beq t3, t5, .Lpkv_coord_done\n" ++
  "  add t6, t2, t3; lbu t6, 0(t6); or t4, t4, t6\n" ++
  "  addi t3, t3, 1; j .Lpkv_coord_loop\n" ++
  ".Lpkv_coord_done:\n" ++
  "  beqz t4, .Lpkv_fail\n" ++
  "  addi s9, s9, 1; j .Lpkv_loop\n" ++
  ".Lpkv_ok:\n" ++
  "  li a0, 0; j .Lpkv_ret\n" ++
  ".Lpkv_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpkv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-! ## block_verdict -- step2_verdict with the FULL (system + withdrawal) recompute.
    a0 = params ptr (the step2_verdict struct)   a1 = SSZ_BASE
    a0 (output) = verdict bit. -/
def blockVerdictFunction : String :=
  "block_verdict:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # params\n" ++
  "  mv s3, a1                   # SSZ_BASE\n" ++
  "  la t0, bv_fail_code; sd zero, 0(t0)\n" ++
  "  la t0, bv_header_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_state_status; sd zero, 0(t0)\n" ++
  "  ld a0, 0(s0); ld a1, 32(s0); ld a2, 40(s0); ld a3, 48(s0); ld a4, 56(s0)\n" ++
  "  la a5, sv_this_rlp; la a6, sv_this_rlp_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  ld a0, 0(s0); la t0, sv_this_rlp_len; ld a1, 0(t0); mv a2, s3\n" ++
  "  jal ra, block_rlp_rebuilt_size\n" ++
  "  bnez a0, .Lbv_block_rlp_parse_fail\n" ++
  "  la t0, bv_block_rlp_len; sd a1, 0(t0)\n" ++
  "  li t1, 0x800000; bgtu a1, t1, .Lbv_block_rlp_limit_fail\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 8(s0); ld a3, 16(s0)\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  mv s1, a0\n" ++
  "  la t0, bv_header_status; sd s1, 0(t0)\n" ++
  "  ld a0, 24(s0); ld a1, 80(s0); ld a2, 88(s0); ld a3, 64(s0); ld a4, 72(s0)\n" ++
  "  la a5, sv_recomputed; mv a6, s3\n" ++
  "  jal ra, block_state_root\n" ++
  "  mv s2, a0\n" ++
  "  la t0, bv_state_status; sd s2, 0(t0)\n" ++
  "  la t0, sv_recomputed; ld t1, 0(s0); addi t1, t1, 52; li t2, 32\n" ++
  ".Lbv_cmp:\n" ++
  "  beqz t2, .Lbv_cmpok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_cmp_mismatch\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_cmp\n" ++
  ".Lbv_cmpok:\n" ++
  "  bnez s1, .Lbv_header_fail\n" ++
  "  bnez s2, .Lbv_state_fail\n" ++
  "  # NO-TRANSACTION gate: this verdict does NOT validate transactions, so it can\n" ++
  "  # only soundly judge no-tx blocks. A tx-bearing INVALID block whose invalid tx\n" ++
  "  # is rejected (no state change) would otherwise match the recompute -> false\n" ++
  "  # positive. tx list is empty iff transactions_offset == withdrawals_offset.\n" ++
  "  ld t4, 0(s0)                # exec_payload from extracted params\n" ++
  "  la t5, bv_exec_p; sd t4, 0(t5)\n" ++
  "  addi a0, t4, 504; jal ra, bgv_u32le        # transactions_offset\n" ++
  "  la t5, bv_tx_off; sd a0, 0(t5)\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 508; jal ra, bgv_u32le   # withdrawals_offset\n" ++
  "  la t5, bv_tx_off; ld t3, 0(t5)\n" ++
  "  bgtu a0, t3, .Lbv_tx_present # wd_off > tx_off => transactions present\n" ++
  "  j .Lbv_after_tx_gate\n" ++
  blockVerdictEmptyTransactionCheckAsm ++
  "  la t5, bsr_bal_count; ld t5, 0(t5); beqz t5, .Lbv_no_bal_for_tx  # tx blocks need BAL replay\n" ++
  "  # Any included transaction must consume nonzero gas. This catches rejected\n" ++
  "  # tx payloads whose state/BAL roots otherwise match the conservative replay.\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # gas_used\n" ++
  "  beqz a0, .Lbv_zero_gas_used\n" ++
  "  # Witness headers must cover concrete in-window BLOCKHASH ancestor accesses\n" ++
  "  # visible in transaction code. execution-specs indexes block_hashes and\n" ++
  "  # fails validation if an accessed ancestor is absent.\n" ++
  "  la t5, svf_codes_ptr; ld a0, 0(t5)\n" ++
  "  la t5, svf_codes_len; ld a1, 0(t5)\n" ++
  "  la a2, bv_blockhash_required_headers\n" ++
  "  jal ra, codes_blockhash_required_headers\n" ++
  "  bnez a0, .Lbv_blockhash_headers_fail\n" ++
  "  la t5, bv_blockhash_required_headers; ld t4, 0(t5)\n" ++
  "  la t5, svf_headers_count; ld t3, 0(t5)\n" ++
  "  bgtu t4, t3, .Lbv_blockhash_headers_fail\n" ++
  ".Lbv_after_tx_gate:\n" ++
  "  mv a0, s3\n" ++
  "  la t2, bv_exec_p; ld a1, 0(t2)\n" ++
  "  jal ra, public_keys_valid\n" ++
  "  bnez a0, .Lbv_public_keys_fail\n" ++
  "  # EIP-7928 BAL gas-limit rule: reject if the block_access_list exceeds the\n" ++
  "  # gas limit (a semantic invalidity not caught by header/state checks).\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  add t0, s3, a0              # NPR = SSZ_BASE + outer.offsets[0]\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2)\n" ++
  "  la t2, bv_npr_p;  sd t0, 0(t2)\n" ++
  "  addi a0, t1, 528; jal ra, bgv_u32le        # bal_off\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); add a0, t1, a0   # bal_start\n" ++
  "  la t2, bv_bal_start; sd a0, 0(t2)\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); addi a0, t0, 4; jal ra, bgv_u32le   # vh_off\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); add a1, t0, a0   # bal_end\n" ++
  "  la t2, bv_bal_start; ld t3, 0(t2); sub a1, a1, t3   # bal_len (a1 survives bgv_u64le)\n" ++
  "  la t2, bv_bal_len; sd a1, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le   # a0 = gas_limit\n" ++
  "  mv a2, a0                                  # gas_limit\n" ++
  "  la t2, bv_bal_start; ld a0, 0(t2)          # bal_start\n" ++
  "  la t2, bv_bal_len; ld a1, 0(t2)            # bal_len\n" ++
  "  jal ra, bal_gas_valid\n" ++
  "  bnez a0, .Lbv_bal_gas_fail          # BAL gas exceeded (or parse fail) -> invalid\n" ++
  "  # Witness integrity: for every BAL account with non-empty pre-state code,\n" ++
  "  # witness.codes must contain that code hash, matching execution-specs'\n" ++
  "  # WitnessState.get_code behavior for missing non-empty code preimages.\n" ++
  "  # Pure BAL account-touch rows are safe to ignore only for withdrawal-only\n" ++
  "  # blocks: zero-amount withdrawals may touch an account without reading code.\n" ++
  "  la t2, bbcv_skip_touch_only; sd zero, 0(t2)\n" ++
  "  ld t4, 0(s0)\n" ++
  "  addi a0, t4, 504; jal ra, bgv_u32le        # transactions_offset\n" ++
  "  mv t3, a0\n" ++
  "  ld t4, 0(s0)\n" ++
  "  addi a0, t4, 508; jal ra, bgv_u32le        # withdrawals_offset\n" ++
  "  bleu a0, t3, .Lbv_code_preimage_no_txs\n" ++
  "  sub t5, a0, t3                             # tx list byte length\n" ++
  "  li t6, 4; bltu t5, t6, .Lbv_code_preimage_no_txs\n" ++
  "  ld t4, 0(s0); add t4, t4, t3               # tx list ptr\n" ++
  "  mv a0, t4; jal ra, bgv_u32le               # first offset = 4 * tx_count\n" ++
  "  andi t6, a0, 3; bnez t6, .Lbv_code_preimage_no_txs\n" ++
  "  srli t6, a0, 2\n" ++
  "  beqz t6, .Lbv_code_preimage_no_txs\n" ++
  "  bgtu a0, t5, .Lbv_code_preimage_no_txs\n" ++
  "  j .Lbv_code_preimage_flag_done             # transactions present\n" ++
  ".Lbv_code_preimage_no_txs:\n" ++
  "  ld t5, 72(s0)\n" ++
  "  beqz t5, .Lbv_code_preimage_flag_done\n" ++
  "  li t6, 1; la t2, bbcv_skip_touch_only; sd t6, 0(t2)\n" ++
  ".Lbv_code_preimage_flag_done:\n" ++
  "  li t6, 1; la t2, bbcv_fee_recipient_valid; sd t6, 0(t2)\n  la a0, bbcv_fee_recipient; ld a1, 0(s0); addi a1, a1, 32; li a2, 20\n  jal ra, mset_memcpy\n" ++
  "  la t2, bv_bal_start; ld a0, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a1, 0(t2)\n" ++
  "  ld a2, 8(s0)                  # parent header RLP\n" ++
  "  ld a3, 16(s0)                 # parent header RLP length\n" ++
  "  ld a4, 80(s0)                 # witness.state ptr\n" ++
  "  ld a5, 88(s0)                 # witness.state len\n" ++
  "  la t2, svf_codes_ptr; ld a6, 0(t2)\n" ++
  "  la t2, svf_codes_len; ld a7, 0(t2)\n" ++
  "  jal ra, bal_code_preimages_valid\n" ++
  "  bnez a0, .Lbv_code_preimage_fail\n" ++
  "  # Upfront sender gas pre-charge gate for the currently parse-supported\n" ++
  "  # one-transaction path. Use the selected public key tail (x||y) and the\n" ++
  "  # pre-account record table materialized by block_state_root.\n" ++
  "  la a0, bv_simple_transfer_tx\n" ++
  "  jal ra, simple_transfer_tx_context\n" ++
  "  la t2, bv_simple_transfer_tx; ld t0, 0(t2); bnez t0, .Lbv_after_tx_gas_precharge\n" ++
  "  ld t0,  96(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 104(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 112(t2); bnez t0, .Lbv_tx_gas_precharge_nonzero_value\n" ++
  "  ld t0, 120(t2); beqz t0, .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_tx_gas_precharge_nonzero_value:\n" ++
  "  ld a0, 8(t2); ld a1, 16(t2); ld a3, 24(t2); ld a2, 32(t2)\n" ++
  "  la t2, bv_bal_start; ld a4, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a5, 0(t2)\n" ++
  "  la a6, basr_records; la a7, bv_tx_gas_precharge\n" ++
  "  jal ra, tx_gas_bal_post_verify\n" ++
  "  la t2, bv_tx_gas_precharge; ld t0, 0(t2); bnez t0, .Lbv_tx_gas_precharge_fail\n" ++
  ".Lbv_after_tx_gas_precharge:\n" ++
  "  # EIP-8037 tx inclusion gas gate: reject parse-supported legacy tx blocks\n" ++
  "  # whose worst regular/state gas exceeds the remaining 2D block budget.\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)             # exec_payload\n" ++
  "  la t2, bv_bal_start; ld a1, 0(t2)          # bal_start\n" ++
  "  la t2, bv_bal_len; ld a2, 0(t2)            # bal_len\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  mv a3, a0                                  # gas_limit\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  jal ra, eip8037_tx_gas_gate\n" ++
  "  bnez a0, .Lbv_eip8037_gas_fail\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la t2, bvgr_runtime_gas_left_ptr; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_runtime_refund_counter_ptr; ld a2, 0(t2)\n" ++
  "  la t2, bvgr_runtime_calldata_floor_ptr; ld a3, 0(t2)\n" ++
  "  la t2, bvgr_runtime_count; ld a4, 0(t2)\n" ++
  "  li a5, 16\n" ++
  "  jal ra, block_verdict_gas_result_arena_prepare\n" ++
  "  bnez a0, .Lbv_after_gas_result_gate\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  la a2, bvgr_gas_left\n" ++
  "  la a3, bvgr_refund_counter\n" ++
  "  la a4, bvgr_calldata_floor\n" ++
  "  la t2, bvgr_arena_tx_count; ld a5, 0(t2)\n" ++
  "  la a6, bvgr_block_gas_increments\n" ++
  "  jal ra, eip7778_remaining_block_gas_from_results\n" ++
  "  la t2, bv_eip7778_status; sd a0, 0(t2)\n" ++
  "  la t2, bv_eip7778_index; sd a1, 0(t2)\n" ++
  "  la t2, bv_eip7778_used; sd a2, 0(t2)\n" ++
  "  bnez a0, .Lbv_eip7778_block_gas_fail\n" ++
  ".Lbv_after_gas_result_gate:\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  mv a1, s3\n" ++
  "  la t2, bv_bal_start; ld a2, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a3, 0(t2)\n" ++
  "  jal ra, eip7702_nonce_reuse_guard\n" ++
  "  bnez a0, .Lbv_eip7702_nonce_reuse_fail\n" ++
  "  la t2, bvgr_arena_status; ld t2, 0(t2); bnez t2, .Lbv_receipts_no_runtime_gas\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la a1, bvgr_receipt_gas_increments\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  jal ra, block_receipt_records_materialize\n" ++
  "  la t2, brr_status; ld t2, 0(t2); bnez t2, .Lbv_receipt_records_fail\n" ++
  "  li a0, 1; j .Lbv_ret\n" ++
  ".Lbv_receipts_no_runtime_gas:\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  jal ra, block_receipt_records_materialize\n" ++
  "  li a0, 1; j .Lbv_ret\n" ++
  ".Lbv_cmp_mismatch:\n" ++
  "  li t0, 1; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_header_fail:\n" ++
  "  li t0, 2; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_state_fail:\n" ++
  "  li t0, 3; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_no_bal_for_tx:\n" ++
  "  li t0, 4; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_zero_gas_used:\n" ++
  "  li t0, 5; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_public_keys_fail:\n" ++
  "  li t0, 6; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_gas_fail:\n" ++
  "  li t0, 7; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_code_preimage_fail:\n" ++
  "  li t0, 11; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_rlp_parse_fail:\n" ++
  "  li t0, 12; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_rlp_limit_fail:\n" ++
  "  li t0, 13; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip8037_gas_fail:\n" ++
  "  addi t0, a0, 7; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip7702_nonce_reuse_fail:\n" ++
  "  li t0, 14; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_blockhash_headers_fail:\n" ++
  "  li t0, 15; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_empty_tx_fail:\n" ++
  "  li t0, 16; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_tx_gas_precharge_fail:\n" ++
  "  li t0, 17; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip7778_block_gas_fail:\n" ++
  "  li t0, 19; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_receipt_records_fail:\n" ++
  "  li t0, 25; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lbv_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## stateless_verdict_v2 -- real-SSZ glue calling block_verdict (system writes). -/
def statelessVerdictV2Function : String :=
  "stateless_verdict_v2:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi s0, s0, 18\n" ++
  "  mv a0, s0; la a1, svf_payload; la a2, svf_wds_ptr; la a3, svf_wds_count\n" ++
  "  jal ra, extract_payload_and_withdrawals\n" ++
  "  mv a0, s0; la a1, svf_witness; la a2, svf_witness_len\n" ++
  "  jal ra, extract_witness_state_section\n" ++
  "  la t0, svf_witness; ld a0, 0(t0)\n" ++
  "  la t0, svf_witness_len; ld a1, 0(t0)\n" ++
  "  jal ra, witness_index_build\n" ++
  "  bnez a0, .Lv2_witness_index_fail\n" ++
  "  # Mirror execution-specs validate_headers(witness.headers): the witness\n" ++
  "  # header list must be a contiguous parent-hash chain before validation can\n" ++
  "  # succeed. SSZ offsets are read bytewise because SSZ_BASE is unaligned.\n" ++
  "  addi a0, s0, 4; jal ra, bgv_u32le          # witness outer offset\n" ++
  "  add t0, s0, a0; la t1, svf_witness_section; sd t0, 0(t1)\n" ++
  "  addi a0, s0, 8; jal ra, bgv_u32le          # chain_config outer offset\n" ++
  "  add t0, s0, a0; la t1, svf_witness_end; sd t0, 0(t1)\n" ++
  "  la t1, svf_witness_section; ld t0, 0(t1); addi a0, t0, 4; jal ra, bgv_u32le # codes offset\n" ++
  "  mv t5, a0\n" ++
  "  la t1, svf_witness_section; ld t0, 0(t1); addi a0, t0, 8; jal ra, bgv_u32le # headers offset\n" ++
  "  mv t6, a0\n" ++
  "  bltu t6, t5, .Lv2_witness_offsets_fail\n" ++
  "  la t1, svf_witness_section; ld t0, 0(t1); add t2, t0, t5\n" ++
  "  la t3, svf_codes_ptr; sd t2, 0(t3)\n" ++
  "  sub t4, t6, t5; la t3, svf_codes_len; sd t4, 0(t3)\n" ++
  "  add t2, t0, t6\n" ++
  "  la t3, svf_headers_ptr; sd t2, 0(t3)\n" ++
  "  la t1, svf_witness_end; ld t1, 0(t1); bltu t1, t2, .Lv2_headers_bounds_fail\n" ++
  "  sub a1, t1, t2; la t3, svf_headers_len; sd a1, 0(t3)\n" ++
  "  mv a0, t2; la a2, svf_headers_count; jal ra, headers_validate_chain\n" ++
  "  bnez a0, .Lv2_headers_fail\n" ++
  "  # execution-specs uses the last validated witness header as parent_header.\n" ++
  "  la t0, svf_headers_count; ld t0, 0(t0); beqz t0, .Lv2_headers_fail\n" ++
  "  addi t0, t0, -1; slli t1, t0, 2\n" ++
  "  la t2, svf_headers_ptr; ld t2, 0(t2); add t3, t2, t1\n" ++
  "  lwu t4, 0(t3); add t5, t2, t4\n" ++
  "  la t6, svf_parent_rlp; sd t5, 0(t6)\n" ++
  "  la t6, svf_headers_len; ld t6, 0(t6); sub t4, t6, t4\n" ++
  "  la t6, svf_parent_rlp_len; sd t4, 0(t6)\n" ++
  "  mv a0, t5; mv a1, t4; la a2, svf_parent_sr\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lv2_parent_header_fail\n" ++
  "  la t0, svf_wds_count; ld s1, 0(t0)\n" ++
  "  la t0, svf_wds_ptr;   ld s2, 0(t0)\n" ++
  "  la s3, svf_descriptors\n" ++
  "  la s4, svf_rlp_arena\n" ++
  "  li s5, 0\n" ++
  ".Lv2_wl:\n" ++
  "  bge s5, s1, .Lv2_wd\n" ++
  "  mv a0, s2; mv a1, s4; la a2, svf_wd_len\n" ++
  "  jal ra, ssz_withdrawal_to_rlp\n" ++
  "  sd s4, 0(s3); la t0, svf_wd_len; ld t1, 0(t0); sd t1, 8(s3)\n" ++
  "  addi s2, s2, 44; addi s4, s4, 72; addi s3, s3, 16; addi s5, s5, 1; j .Lv2_wl\n" ++
  ".Lv2_wd:\n" ++
  "  addi a0, s0, 56; jal ra, bgv_u32le; mv s3, a0     # execution_requests offset\n" ++
  "  addi a0, s0, 4;  jal ra, bgv_u32le; mv s4, a0     # witness offset = NPR end\n" ++
  "  addi a0, s0, 16; add a0, a0, s3                   # er section start\n" ++
  "  sub a1, s4, s3; addi a1, a1, -16                  # er section len\n" ++
  "  la a2, erh_requests_hash\n" ++
  "  jal ra, execution_requests_hash\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  la t1, sv_params\n" ++
  "  la t0, svf_payload;        ld t0, 0(t0); sd t0, 0(t1)\n" ++
  "  la t0, svf_parent_rlp;     ld t0, 0(t0); sd t0, 8(t1)\n" ++
  "  la t0, svf_parent_rlp_len; ld t0, 0(t0); sd t0, 16(t1)\n" ++
  "  la t0, svf_parent_sr;      sd t0, 24(t1)\n" ++
  "  la t0, svf_zero32;         sd t0, 32(t1)\n" ++
  "  la t0, svf_zero32;         sd t0, 40(t1)\n" ++
  "  addi t0, s0, 24;           sd t0, 48(t1)\n" ++
  "  la t0, erh_requests_hash;  sd t0, 56(t1)\n" ++
  "  la t0, svf_descriptors;    sd t0, 64(t1)\n" ++
  "  la t0, svf_wds_count;      ld t0, 0(t0); sd t0, 72(t1)\n" ++
  "  la t0, svf_witness;        ld t0, 0(t0); sd t0, 80(t1)\n" ++
  "  la t0, svf_witness_len;    ld t0, 0(t0); sd t0, 88(t1)\n" ++
  "  la a0, sv_params; mv a1, s0\n" ++
  "  jal ra, block_verdict\n" ++
  "  j .Lv2_ret\n" ++
  ".Lv2_headers_fail:\n" ++
  "  li t0, 10; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_witness_index_fail:\n" ++
  "  li t0, 20; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_witness_offsets_fail:\n" ++
  "  li t0, 21; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_headers_bounds_fail:\n" ++
  "  li t0, 22; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_parent_header_fail:\n" ++
  "  li t0, 23; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_requests_hash_fail:\n" ++
  "  li t0, 24; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lv2_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/- `zisk_stateless_verdict_v2`: probe. Fed the SAME `-i` input as the guest.
   Output OUTPUT+0 = verdict bit (system writes + withdrawals modeled). -/
def ziskStatelessVerdictV2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  jal ra, stateless_verdict_v2\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)            # OUTPUT+0 = verdict bit\n" ++
  "  la t1, bv_fail_code; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, bv_header_status; ld t2, 0(t1); sd t2, 16(t0)\n" ++
  "  la t1, bv_state_status; ld t2, 0(t1); sd t2, 24(t0)\n" ++
  "  la t1, bsr_bal_count; ld t2, 0(t1); sd t2, 32(t0)\n" ++
  "  la t1, bsr_fail_code; ld t2, 0(t1); sd t2, 40(t0)\n" ++
  "  la t1, bsr_change_count; ld t2, 0(t1); sd t2, 48(t0)\n" ++
  "  la t1, bsr_wl_v; ld t2, 0(t1); sd t2, 56(t0)\n" ++
  "  la t1, baacd_fail_code; ld t2, 0(t1); sd t2, 64(t0)\n" ++
  "  la t1, bacv_fail_code; ld t2, 0(t1); sd t2, 72(t0)\n" ++
  "  la t1, baap_fail_code; ld t2, 0(t1); sd t2, 80(t0)\n" ++
  "  la t1, sri_fail_index; ld t2, 0(t1); sd t2, 88(t0)\n" ++
  "  la t1, sri_fail_mode; ld t2, 0(t1); sd t2, 96(t0)\n" ++
  "  la t1, sri_fail_status; ld t2, 0(t1); sd t2, 104(t0)\n" ++
  "  la t1, bv_block_rlp_len; ld t2, 0(t1); sd t2, 112(t0)\n" ++
  "  la t1, brr_status; ld t2, 0(t1); sd t2, 120(t0)\n" ++
  "  la t1, brr_control; ld t2, 0(t1); sd t2, 128(t0)\n" ++
  "  la t1, brr_append_status; ld t2, 0(t1); sd t2, 136(t0)\n" ++
  "  la t1, brr_records; ld t2, 0(t1); sd t2, 144(t0)\n" ++
  "  la t1, brr_records; ld t2, 8(t1); sd t2, 152(t0)\n" ++
  "  la t1, brr_records; ld t2, 16(t1); sd t2, 160(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 0(t1); sd t2, 168(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 8(t1); sd t2, 176(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 16(t1); sd t2, 184(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 24(t1); sd t2, 192(t0)\n" ++
  "  la t1, sv_params; ld t1, 0(t1); addi t1, t1, 52\n" ++
  "  ld t2, 0(t1); sd t2, 200(t0)\n" ++
  "  ld t2, 8(t1); sd t2, 208(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 216(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 224(t0)\n" ++
  "  la t1, bvgr_arena_status; ld t2, 0(t1); sd t2, 232(t0)\n" ++
  "  la t1, bvgr_arena_tx_count; ld t2, 0(t1); sd t2, 240(t0)\n" ++
  "  la t1, bvgr_arena_runtime_count; ld t2, 0(t1); sd t2, 248(t0)\n" ++
  "  la t1, bvgr_arena_status; ld t2, 0(t1); sd t2, 256(t0)\n" ++
  "  la t1, bvgr_arena_tx_count; ld t2, 0(t1); sd t2, 264(t0)\n" ++
  "  la t1, bvgr_arena_runtime_count; ld t2, 0(t1); sd t2, 272(t0)\n" ++
  "  la t1, bvgr_arena_fail_index; ld t2, 0(t1); sd t2, 280(t0)\n" ++
  "  la t1, bvgr_arena_substatus; ld t2, 0(t1); sd t2, 288(t0)\n" ++
  "  la t1, bv_eip7778_status; ld t2, 0(t1); sd t2, 296(t0)\n" ++
  "  la t1, bv_eip7778_index; ld t2, 0(t1); sd t2, 304(t0)\n" ++
  "  la t1, bv_eip7778_used; ld t2, 0(t1); sd t2, 312(t0)\n" ++
  "  la t1, bvgr_tx_gas_limits; ld t2, 0(t1); sd t2, 320(t0)\n" ++
  "  la t1, bvgr_block_gas_increments; ld t2, 0(t1); sd t2, 328(t0)\n" ++
  "  la t1, bvgr_receipt_gas_increments; ld t2, 0(t1); sd t2, 336(t0)\n" ++
  "  j .Lv2_pdone\n" ++
  zkvmSha256Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalToPathDeltaFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  accountAtHeaderStateRootFunction ++ "\n" ++
  extcodesizeAtHeaderStateRootFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptStateRootFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  withdrawalsStateRootFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  validateHeaderRlpPairFunction ++ "\n" ++
  bhrRevLeBeFunction ++ "\n" ++
  blockHeaderSszToRlpFunction ++ "\n" ++
  rlpBytesEncodedSizeFunction ++ "\n" ++
  rlpListEncodedSizeFunction ++ "\n" ++
  blockRlpRebuiltSizeFunction ++ "\n" ++
  executionRequestsHashFunction ++ "\n" ++
  step2VerdictFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  ephU32leFunction ++ "\n" ++
  extractParentHeaderAndStateRootFunction ++ "\n" ++
  spwU32leFunction ++ "\n" ++
  extractPayloadAndWithdrawalsFunction ++ "\n" ++
  swsU32leFunction ++ "\n" ++
  extractWitnessStateSectionFunction ++ "\n" ++
  swrRevLeBeFunction ++ "\n" ++
  sszWithdrawalToRlpFunction ++ "\n" ++
  statelessVerdictFromSszFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  accountApplyStorageSlotAccFunction ++ "\n" ++
  swdReadU64leFunction ++ "\n" ++
  swdWriteBe32U64Function ++ "\n" ++
  swdWriteBe8Function ++ "\n" ++
  swdMinimalCopyFunction ++ "\n" ++
  systemWriteDescriptorsFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  accountIsEip161EmptyFunction ++ "\n" ++
  balAccountHasStateChangeFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountAccessOutcomeDescriptorsFunction ++ "\n" ++
  balStorageAccessOutcomeDescriptorsFunction ++ "\n" ++
  balAccountRecordArrayFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++
  bsrSysChangeFunction ++ "\n" ++
  bsrBeaconChangeFunction ++ "\n" ++
  bsrApplyModeledSystemPostFieldsFunction ++ "\n" ++
  blockStateRootFunction ++ "\n" ++
  codesBlockhashRequiredHeadersFunction ++ "\n" ++
  publicKeysValidFunction ++ "\n" ++
  receiptRecordsFunction ++ "\n" ++
  blockReceiptRecordsMaterializeFunction ++ "\n" ++
  blockVerdictFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  balSectionInfoFunction ++ "\n" ++
  balGasValidFunction ++ "\n" ++
  codeHashAtHeaderStateRootFunction ++ "\n" ++
  balCodePreimagesValidFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  txGasSenderBalLookupFunction ++ "\n" ++
  simpleTransferTxContextFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  txEffectiveGasPricingFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  txUpfrontPrechargeFunction ++ "\n" ++
  txGasBalPostVerifyFunction ++ "\n" ++
  accessListCountFunction ++ "\n" ++
  intrinsicGasAmsterdamCountsFunction ++ "\n" ++
  eip8037TxGasGateFunction ++ "\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  eip7778RemainingBlockGasFromResultsFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  blockVerdictGasResultArenaPrepareFunction ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  enrgU32leFunction ++ "\n" ++
  eip7702NonceReuseGuardFunction ++ "\n" ++
  statelessVerdictV2Function ++ "\n" ++
  ".Lv2_pdone:"

def ziskStatelessVerdictV2DataSection : String :=
  ziskStatelessVerdictDataSection ++ "\n" ++
  runtimeAccessAccountOutcomeData ++ "\n" ++
  storageAccessGasData ++ "\n" ++
  executionRequestsHashDataSection ++ "\n" ++
  ".balign 8\n" ++
  "sltr_field_len:\n  .zero 8\n" ++
  "sltr_nibble_count:\n  .zero 8\n" ++
  "sltr_hp_len:\n  .zero 8\n" ++
  "sltr_cursor:\n  .zero 8\n" ++
  "sltr_total_payload:\n  .zero 8\n" ++
  "sltr_nibbles:\n  .zero 2048\n" ++
  "sltr_hp_buf:\n  .zero 1024\n" ++
  "sltr_payload_buf:\n  .zero 16384\n" ++
  "sltr_node_buf:\n  .zero 16384\n" ++
  ".balign 32\n" ++
  "srss_key:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "srss_rlpval:\n  .zero 40\n" ++
  "srss_rlpval_len:\n  .zero 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  "aps_witness_ptr:\n  .zero 8\n" ++
  "aps_witness_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aps_newsroot:\n  .zero 32\n" ++
  "aps_path:\n  .zero 64\n" ++
  "aps_empty_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "swd_2935_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_2935_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_val:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "swd_2935_vlen:\n  .zero 8\n" ++
  "swd_4788_vlen:\n  .zero 8\n" ++
  "swd_4788_root_vlen:\n  .zero 8\n" ++
  "swd_ts_be8:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bsr_root_p:\n  .zero 8\n" ++
  "bsr_wit_p:\n  .zero 8\n" ++
  "bsr_wl_v:\n  .zero 8\n" ++
  "bsr_ssz_p:\n  .zero 8\n" ++
  "bsr_bal_start:\n  .zero 8\n" ++
  "bsr_bal_len:\n  .zero 8\n" ++
  "bsr_bal_count:\n  .zero 8\n" ++
  "bsr_exec_p:\n  .zero 8\n" ++
  "bsr_tx_off:\n  .zero 8\n" ++
  "bsr_pathp:\n  .zero 8\n" ++
  "bsr_acct_len:\n  .zero 8\n" ++
  "bsr_tmplen:\n  .zero 8\n" ++
  "bsr_prev_desc:\n  .zero 8\n" ++
  "bsr_prev_acct:\n  .zero 8\n" ++ ziskBalAccountHasStateChangeDataSection ++
  "bsr_bal_item_ptr:\n  .zero 8\n" ++
  "bsr_bal_item_len:\n  .zero 8\n" ++
  ziskBalAccountIsModeledSystemDataSection ++
  ".balign 32\n" ++
  "bsr_kbuf:\n  .zero 32\n" ++
  "bsr_delta:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsr_acct:\n  .zero 256\n" ++
  "bsr_paths:\n  .zero " ++ toString (bsrMaxAuxChanges * bsrPathBytes) ++
  "\nbsr_newaccts:\n  .zero " ++ toString (bsrMaxAuxChanges * bsrSystemAccountBytes) ++
  "\nbsr_changes:\n  .zero " ++ toString (bsrMaxStateChanges * bsrStateChangeBytes) ++ "\n" ++
  "bsr_changed_account_count:\n  .zero 8\n" ++
  "bsr_access_count:\n  .zero 8\n" ++
  "bsr_storage_access_path_count:\n  .zero 8\n" ++
  "bsr_storage_access_window:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "bsr_changed_accounts:\n  .zero " ++ toString (bsrMaxAccessAccounts * 32) ++ "\n" ++
  "bsr_access_paths:\n  .zero " ++ toString (bsrMaxAccountAccessOutcomes * bsrPathBytes) ++ "\n" ++
  "bsr_storage_account_token:\n  .zero " ++ toString (bsrMaxAccessAccounts * 32) ++ "\n" ++
  "bsr_storage_access_paths:\n  .zero " ++ toString (bsrMaxStorageAccessOutcomes * bsrPathBytes) ++ "\n" ++
  "baaod_hash:\n  .zero 32\n" ++
  "bsaod_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsaod_empty_value:\n  .zero 1\n" ++
  "baaod_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 32\n" ++
  "bsr_addr_2935:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  ".balign 32\n" ++
  "bsr_addr_4788:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02\n" ++
  ".balign 8\n" ++
  "bgv_count:\n  .zero 8\n" ++
  "bgv_off:\n  .zero 8\n" ++
  "bgv_size:\n  .zero 8\n" ++
  "bgv_acctlen:\n  .zero 8\n" ++
  "bv_exec_p:\n  .zero 8\n" ++
  "bv_npr_p:\n  .zero 8\n" ++
  "bv_bal_start:\n  .zero 8\n" ++
  "bv_bal_len:\n  .zero 8\n" ++
  "bv_tx_off:\n  .zero 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\nbv_tx_list_len:\n  .zero 8\nbv_tx_count:\n  .zero 8\nbv_tx_index:\n  .zero 8\nbv_tx_item_start:\n  .zero 8\n" ++
  "bv_public_keys_ptr:\n  .zero 8\n" ++
  "bv_public_keys_len:\n  .zero 8\n" ++
  "bv_fail_code:\n  .zero 8\n" ++
  "bv_header_status:\n  .zero 8\n" ++
  "bv_state_status:\n  .zero 8\n" ++
  "bv_block_rlp_len:\n  .zero 8\n" ++
  "bv_blockhash_required_headers:\n  .zero 8\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_tx_gas:\n  .zero 8\n" ++
  "brr_receipt_gas_ptr:\n  .zero 8\n" ++
  "brr_receipt_gas_count:\n  .zero 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero 1024\n" ++
  "bvgr_runtime_gas_left_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_refund_counter_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_calldata_floor_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_count:\n  .zero 8\n" ++
  "bv_eip7778_status:\n  .zero 8\n" ++
  "bv_eip7778_index:\n  .zero 8\n" ++
  "bv_eip7778_used:\n  .zero 8\n" ++
  "bvgr_status:\n  .zero 8\n" ++
  "bvgr_count:\n  .zero 8\n" ++
  "bvgr_fail_index:\n  .zero 8\n" ++
  "bvgr_tx_type:\n  .zero 8\n" ++
  "bvgr_tx_inner:\n  .zero 8\n" ++
  "bvgr_nonce:\n  .zero 8\n" ++
  "bvgr_gas:\n  .zero 8\n" ++
  "bvgr_arena_status:\n  .zero 8\n" ++
  "bvgr_arena_tx_count:\n  .zero 8\n" ++
  "bvgr_arena_runtime_count:\n  .zero 8\n" ++
  "bvgr_arena_fail_index:\n  .zero 8\n" ++
  "bvgr_arena_substatus:\n  .zero 8\n" ++
  "bvgr_tx_gas_limits:\n  .zero 128\n" ++
  "bvgr_gas_left:\n  .zero 128\n" ++
  "bvgr_refund_counter:\n  .zero 128\n" ++
  "bvgr_calldata_floor:\n  .zero 128\n" ++
  "bvgr_block_gas_increments:\n  .zero 128\n" ++
  "bvgr_receipt_gas_increments:\n  .zero 128\n" ++
  "bvgr_before_refund:\n  .zero 128\n" ++
  "bvgr_applied_refund:\n  .zero 128\n" ++
  blockVerdictTxGasPrechargeDataSection ++
  eip7702NonceReuseGuardDataSection ++
  "brl_item_start:\n  .zero 8\n" ++
  "brl_item_end:\n  .zero 8\n" ++
  "brl_wd_len:\n  .zero 8\n" ++
  "brl_wd_buf:\n  .zero 72\n" ++
  "svf_witness_section:\n  .zero 8\n" ++
  "svf_witness_end:\n  .zero 8\n" ++
  "svf_codes_ptr:\n  .zero 8\n" ++
  "svf_codes_len:\n  .zero 8\n" ++
  "svf_headers_ptr:\n  .zero 8\n" ++
  "svf_headers_len:\n  .zero 8\n" ++
  "svf_headers_count:\n  .zero 8\n" ++
  "bbcv_count:\n  .zero 8\n" ++
  "bbcv_off:\n  .zero 8\n" ++
  "bbcv_size:\n  .zero 8\n" ++
  "bbcv_acct_len:\n  .zero 8\n" ++
  "bbcv_addr_off:\n  .zero 8\n" ++
  "bbcv_addr_len:\n  .zero 8\n" ++
  "bbcv_acct_struct:\n  .zero 104\n" ++
  "aahsr_state_root:\n  .zero 32\n" ++
  "bbcv_field_off:\n  .zero 8\n" ++
  "bbcv_field_len:\n  .zero 8\n" ++
  "bbcv_field_count:\n  .zero 8\n" ++
  "bbcv_balance_count:\n  .zero 8\n" ++
  "bbcv_nonce_count:\n  .zero 8\n" ++
  "bbcv_skip_touch_only:\n  .zero 8\n" ++
  "bbcv_touch_only:\n  .zero 8\n" ++
  "bbcv_fee_recipient_valid:\n  .zero 8\n.balign 8\nbbcv_fee_recipient:\n  .zero 20\n" ++
  ".balign 32\n" ++
  "bbcv_sys_2935:\n" ++
  "  .byte 0x00, 0x00, 0xf9, 0x08, 0x27, 0xf1, 0xc5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7a, 0x02, 0x33, 0x5b, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  "bbcv_sys_4788:\n" ++
  "  .byte 0x00, 0x0f, 0x3d, 0xf6, 0xd7, 0x32, 0x80, 0x7e\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xb7, 0xb8, 0xbb, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xbe, 0xac, 0x02\n" ++
  "bbcv_sys_7002:\n" ++
  "  .byte 0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5\n" ++
  "  .byte 0x5e, 0x80, 0xd1, 0x9a, 0xd8, 0x35, 0x79, 0xa6\n" ++
  "  .byte 0x4c, 0x00, 0x70, 0x02\n" ++
  "bbcv_sys_7251:\n" ++
  "  .byte 0x00, 0x00, 0xbb, 0xdd, 0xc7, 0xce, 0x48, 0x86\n" ++
  "  .byte 0x42, 0xfb, 0x57, 0x9f, 0x8b, 0x00, 0xf3, 0xa5\n" ++
  "  .byte 0x90, 0x00, 0x72, 0x51\n" ++
  "bbcv_sys_6110:\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40\n" ++
  "  .byte 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30\n" ++
  "  .byte 0x3d, 0x77, 0x05, 0xfa\n" ++
  ".balign 32\n" ++
  "bbcv_code_hash:\n  .zero 32\n" ++
  "bbcv_sender_addr:\n  .zero 32\n" ++
  "bbcv_create_addr:\n  .zero 32\n" ++
  "bbcv_create2_salt:\n  .zero 32\n" ++
  "ac2_inner_digest:\n  .zero 32\n" ++
  "ac2_outer_digest:\n  .zero 32\n" ++
  "ac2_preimage:\n  .zero 88\n" ++
  "ac_buffer:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_nonce_be:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "ac_digest:\n  .zero 32\n" ++
  "bbcv_stop_code_hash:\n" ++
  "  .quad 0x14281e7a9e7836bc, 0x7d818f8229424636, 0x9165d677b4f71266, 0x8ac9bc64e0a996ff\n" ++
  ".balign 32\n" ++
  "chahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "chahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "chahsr_empty_code_hash:\n" ++
  "  .quad 0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b\n" ++
  "ad_offset:\n  .zero 8\n" ++
  "ad_length:\n  .zero 8\n" ++
  "aa_value_len:\n  .zero 8\n" ++
  "ecsahsr_dummy_offset:\n  .zero 8\n" ++
  "ecsahsr_code_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n  .zero 256\n" ++
  "ecsahsr_state_root:\n  .zero 32\n" ++
  "mlk_keccak_buf:\n  .zero 32\n" ++
  "mlk_nibble_buf:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ecsahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "ecsahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32\n" ++
  "bsg_count:\n  .zero 8\n" ++
  "bsg_off:\n  .zero 8\n" ++
  "bsg_len:\n  .zero 8\n" ++
  "bsg_tx_nonce:\n  .zero 8\n" ++
  "bsg_slot_count:\n  .zero 8\n" ++
  "bsg_slot_off:\n  .zero 8\n" ++
  "bsg_slot_len:\n  .zero 8\n" ++
  "bsg_slot_ptr:\n  .zero 8\n" ++
  "bsg_slot_item_len:\n  .zero 8\n" ++
  "bsg_changes_off:\n  .zero 8\n" ++
  "bsg_changes_len:\n  .zero 8\n" ++
  "bsg_changes_ptr:\n  .zero 8\n" ++
  "bsg_change_count:\n  .zero 8\n" ++
  "bsg_change_off:\n  .zero 8\n" ++
  "bsg_change_len:\n  .zero 8\n" ++
  "bsg_change_ptr:\n  .zero 8\n" ++
  "bsg_change_item_len:\n  .zero 8\n" ++
  "bsg_idx_off:\n  .zero 8\n" ++
  "bsg_idx_len:\n  .zero 8\n" ++
  "bsg_index:\n  .zero 8\n" ++
  "bsg_value_off:\n  .zero 8\n" ++
  "bsg_value_len:\n  .zero 8\n" ++
  "bsg_tx_type:\n  .zero 8\n" ++
  "bsg_tx_inner:\n  .zero 8\n" ++
  "bsg_tx_gas:\n  .zero 8\n" ++
  "bsg_gas_field:\n  .zero 8\n" ++
  "bsg_to_field:\n  .zero 8\n" ++
  "bsg_data_field:\n  .zero 8\n" ++
  "bsg_access_field:\n  .zero 8\n" ++
  "bsg_auth_field:\n  .zero 8\n" ++
  "bsg_intrinsic_gas:\n  .zero 8\n" ++
  "bsg_floor_gas:\n  .zero 8\n" ++
  "bsg_data_ptr:\n  .zero 8\n" ++
  "bsg_data_off:\n  .zero 8\n" ++
  "bsg_data_len:\n  .zero 8\n" ++
  "bsg_to_off:\n  .zero 8\n" ++
  "bsg_to_len:\n  .zero 8\n" ++
  "bsg_access_off:\n  .zero 8\n" ++
  "bsg_access_len:\n  .zero 8\n" ++
  "bsg_access_addrs:\n  .zero 8\n" ++
  "bsg_access_slots:\n  .zero 8\n" ++
  "bsg_auth_off:\n  .zero 8\n" ++
  "bsg_auth_len:\n  .zero 8\n" ++
  "bsg_auth_count:\n  .zero 8\n" ++
  "bsg_header_gas_used:\n  .zero 8\n" ++
  "bsg_min_block_gas:\n  .zero 8\n" ++
  "alc_scratch:\n  .zero 8\n" ++
  "alc_entry_offset:\n  .zero 8\n" ++
  "alc_entry_length:\n  .zero 8\n" ++
  "alc_keys_offset:\n  .zero 8\n" ++
  "alc_keys_length:\n  .zero 8\n" ++
  "bsg_worst_state:\n  .zero 8\n" ++
  "bsg_prior_state:\n  .zero 8\n" ++
  "bsr_fail_code:\n  .zero 8\n" ++
  "bsr_change_count:\n  .zero 8\n" ++
  "sri_cur_mode:\n  .zero 8\n" ++
  "sri_fail_index:\n  .zero 8\n" ++
  "sri_fail_mode:\n  .zero 8\n" ++
  "sri_fail_status:\n  .zero 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
  "baap_bal_len:\n  .zero 8\n" ++
  "baap_nonce_len:\n  .zero 8\n" ++
  "baap_tmp_len:\n  .zero 8\n" ++
  "baap_tmp2_len:\n  .zero 8\n" ++
  "baap_fail_code:\n  .zero 8\n" ++
  "baap_sc_off:\n  .zero 8\n" ++
  "baap_sc_len:\n  .zero 8\n" ++
  "baap_sc_ptr:\n  .zero 8\n" ++
  "baap_sc_count:\n  .zero 8\n" ++
  "baap_sc_index:\n  .zero 8\n" ++
  "baap_sc_out_count:\n  .zero 8\n" ++
  "baap_storage_empty_flag:\n  .zero 8\n" ++
  "baap_force_storage_clear:\n  .zero 8\n" ++
  "baap_storage_delete_flag:\n  .zero 8\n" ++
  "baap_storage_delete_count:\n  .zero 8\n" ++
  "baap_storage_delete_index:\n  .zero 8\n" ++
  "baap_storage_root_ptr:\n  .zero 8\n" ++
  "baap_walk_val_len:\n  .zero 8\n" ++
  "mdacc_witness_len:\n  .zero 8\n" ++
  "mdacc_survivor_nibble:\n  .zero 8\n" ++
  "mdacc_child_ptr:\n  .zero 8\n" ++
  "mdacc_child_len:\n  .zero 8\n" ++
  "mdacc_leaf_path_len:\n  .zero 8\n" ++
  "mdacc_ext_path_len:\n  .zero 8\n" ++
  "mdacc_leaf_value_ptr:\n  .zero 8\n" ++
  "mdacc_leaf_value_len:\n  .zero 8\n" ++
  "mee_path_off:\n  .zero 8\n" ++
  "mee_path_len:\n  .zero 8\n" ++
  "baap_item_off:\n  .zero 8\n" ++
  "baap_item_len:\n  .zero 8\n" ++
  "baap_slot_changes_off:\n  .zero 8\n" ++
  "baap_slot_changes_len:\n  .zero 8\n" ++
  "baap_slot_changes_ptr:\n  .zero 8\n" ++
  "baap_slot_changes_count:\n  .zero 8\n" ++
  "baap_val_off:\n  .zero 8\n" ++
  "baap_val_len:\n  .zero 8\n" ++
  "baap_code_list_off:\n  .zero 8\n" ++
  "baap_code_list_len:\n  .zero 8\n" ++
  "baap_code_list_ptr:\n  .zero 8\n" ++
  "baap_code_count:\n  .zero 8\n" ++
  "baap_code_item_ptr:\n  .zero 8\n" ++
  "baap_code_off:\n  .zero 8\n" ++
  "baap_code_len:\n  .zero 8\n" ++
  "baap_tmp3_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "baap_bal:\n  .zero 32\n" ++
  "baap_nonce:\n  .zero 32\n" ++
  "baap_slot:\n  .zero 32\n" ++
  "baap_code_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "baap_tmp2:\n  .zero 512\n" ++
  "baap_tmp3:\n  .zero 512\n" ++
  "baap_storage_value_cursor:\n  .zero 8\n" ++
  "baap_walk_val:\n  .zero 128\n" ++
  "baap_storage_desc:\n  .zero " ++ toString (bsrMaxBalItems * baapStorageDescBytes) ++ "\n" ++
  "baap_storage_paths:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++ "\n" ++
  "baap_storage_delete_paths:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++ "\n" ++
  "baap_storage_values:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++ "\n" ++
  "mdacc_leaf_path:\n  .zero 128\n" ++
  "mdacc_collapsed_path:\n  .zero 128\n" ++
  "bacp_off:\n  .zero 8\n" ++
  "bacp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baacd_value_len:\n  .zero 8\n" ++
  "baacd_is_empty:\n  .zero 8\n" ++
  "baacd_fail_code:\n  .zero 8\n" ++
  "aie_offset:\n  .zero 8\n" ++
  "aie_length:\n  .zero 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  "bacv_fail_code:\n  .zero 8\n" ++
  "baada_item_off:\n  .zero 8\n" ++
  "baada_item_len:\n  .zero 8\n" ++
  "basr_records:\n  .zero " ++ toString (bsrMaxStateChanges * bsrAccountRecordBytes) ++
  "\nbasr_paths:\n  .zero " ++ toString (bsrMaxStateChanges * bsrPathBytes) ++
  "\nbasr_values:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++
  "\nbasr_accounts:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++ "\n" ++
  "bara_item_off:\n  .zero 8\n" ++
  "bara_item_len:\n  .zero 8\n" ++
  "bara_acct_len:\n  .zero 8\n" ++
  "bara_bal_end:\n  .zero 8\n" ++
  "bara_next_item:\n  .zero 8\n" ++
  "bara_skip_modeled_system:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bara_path:\n  .zero 64\n" ++
  "bara_acct:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bara_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  ".balign 8\n" ++
  "bsr_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  "iw_empty_trie_root:\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  ".balign 8\n" ++
  "iwd_ptr:\n  .zero 8\n" ++
  "iwd_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ins_wl:\n  .zero 8\n" ++
  "ins_node_len:\n  .zero 8\n" ++
  "ins_ref_len:\n  .zero 8\n" ++
  "mle_path_off:\n  .zero 8\n" ++
  "mle_path_len:\n  .zero 8\n" ++
  "ins_kcount:\n  .zero 8\n" ++
  "ins_lv_ptr:\n  .zero 8\n" ++
  "ins_lv_len:\n  .zero 8\n" ++
  "ins_m:\n  .zero 8\n" ++
  "ins_niba:\n  .zero 8\n" ++
  "ins_nibb:\n  .zero 8\n" ++
  "ins_node2_len:\n  .zero 8\n" ++
  "ins_ref2_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "ins_meta:\n  .zero 48\n" ++
  ".balign 8\n" ++
  "ins_stack:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_k:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_ref:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_ref2:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_node:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_node2:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_empty_branch:\n" ++
  "  .byte 0xd1,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80\n" ++
  ".balign 8\n" ++
  "mxne_field_len:\n  .zero 8\n" ++
  "mxne_hp_len:\n  .zero 8\n" ++
  "mxne_cursor:\n  .zero 8\n" ++
  "mxne_total_payload:\n  .zero 8\n" ++
  "mxne_hp_buf:\n  .zero 1024\n" ++
  "mxne_payload_buf:\n  .zero 16384\n"


end EvmAsm.Codegen
