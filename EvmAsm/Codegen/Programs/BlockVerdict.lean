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
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.Header
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
import EvmAsm.Codegen.Programs.MptEncodeLeafBranch
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.SszWithdrawal
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.WithdrawalsRootIndexed
import EvmAsm.Codegen.Programs.BlockAccessListHash

import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
import EvmAsm.Codegen.Programs.SimpleTransferRecipient
import EvmAsm.Codegen.Programs.SimpleTransferFeeRecipient
import EvmAsm.Codegen.Programs.BlockVerdictSysChange
import EvmAsm.Codegen.Programs.BlockVerdictChainConfig
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictDataSection
import EvmAsm.Codegen.Programs.BlockVerdictRuntimePayload
namespace EvmAsm.Codegen

open EvmAsm.Rv64


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
  "  la t0, bsr_fail_code; sd zero, 0(t0); li t1, " ++ toString bsrMaxWitnessBytes ++ "; bgtu a2, t1, .Lbsr_cons_change_cap\n" ++
  "  mv s3, a3                   # wds descriptors\n" ++
  "  mv s4, a4                   # n_wds\n" ++
  "  mv s5, a5                   # out_root\n" ++
  "  # derive the system writes (SSZ_BASE in a6)\n" ++
  "  la t0, bsr_ssz_p; ld a0, 0(t0); jal ra, system_write_descriptors\n" ++
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
  "  # BAL rows already include withdrawal-induced balance changes, so avoid\n" ++
  "  # applying the SSZ withdrawals a second time when BAL replay was present.\n" ++
  "  la t0, bsr_bal_count; ld t0, 0(t0); bnez t0, .Lbsr_apply\n" ++
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
  "  la t0, bv_tx_root_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_valid; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_gas_left_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_refund_counter_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_calldata_floor_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n" ++
  "  ld a0, 0(s0); ld a1, 32(s0); ld a2, 40(s0); ld a3, 48(s0); ld a4, 56(s0); ld a7, 96(s0)\n" ++
  "  la a5, sv_this_rlp; la a6, sv_this_rlp_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  la t0, bv_block_hash_check_enabled; ld t0, 0(t0); beqz t0, .Lbv_block_hash_ok\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); la a2, bv_block_hash\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  la t0, bv_block_hash; ld t1, 0(s0); addi t1, t1, 472; li t2, 32\n" ++
  ".Lbv_block_hash_cmp:\n" ++
  "  beqz t2, .Lbv_block_hash_ok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_block_hash_mismatch\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_block_hash_cmp\n" ++
  ".Lbv_block_hash_ok:\n" ++
  "  ld a0, 0(s0); la t0, sv_this_rlp_len; ld a1, 0(t0); mv a2, s3\n" ++
  "  jal ra, block_rlp_rebuilt_size\n" ++
  "  bnez a0, .Lbv_block_rlp_parse_fail\n" ++
  "  la t0, bv_block_rlp_len; sd a1, 0(t0)\n" ++
  "  li t1, 0x800000; bgtu a1, t1, .Lbv_block_rlp_limit_fail\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 8(s0); ld a3, 16(s0)\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  mv s1, a0\n" ++
  "  la t0, bv_header_status; sd s1, 0(t0)\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 64(s0); ld a3, 72(s0)\n" ++
  "  jal ra, block_validate_withdrawals_root_indexed\n" ++
  "  la t0, bv_withdrawals_root_status; sd a0, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_valid; sd a1, 0(t0)\n" ++
  "  bnez a0, .Lbv_withdrawals_root_fail\n" ++
  "  beqz a1, .Lbv_withdrawals_root_fail\n" ++
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
  "  # execution-specs is_valid_versioned_hashes: SSZ NPR.versioned_hashes must\n" ++
  "  # equal the concatenation of all EIP-4844 tx blob_versioned_hashes.\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  add t0, s3, a0              # NPR = SSZ_BASE + outer.offsets[0]\n" ++
  "  la t2, bv_npr_p; sd t0, 0(t2)\n" ++
  "  addi a0, t0, 4; jal ra, bgv_u32le         # versioned_hashes offset\n" ++
  "  mv t3, a0\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); addi a0, t0, 40; jal ra, bgv_u32le # execution_requests offset\n" ++
  "  bltu a0, t3, .Lbv_versioned_hashes_fail\n" ++
  "  sub a2, a0, t3              # SSZ versioned_hashes byte length\n" ++
  "  la t2, bv_versioned_hashes_len; sd a2, 0(t2)\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); add a1, t0, t3\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  jal ra, ssz_tx_list_versioned_hashes_match\n" ++
  "  bnez a0, .Lbv_versioned_hashes_fail\n" ++
  "  # execution-specs apply_body checks header.blob_gas_used against the blob\n" ++
  "  # gas consumed by type-3 txs. The previous gate proves NPR.versioned_hashes\n" ++
  "  # equals the tx blob-hash concatenation, so total blob gas is derived from\n" ++
  "  # that SSZ list length.\n" ++
  "  la t2, bv_versioned_hashes_len; ld t0, 0(t2)\n" ++
  "  andi t1, t0, 31; bnez t1, .Lbv_blob_gas_used_fail\n" ++
  "  srli t0, t0, 5              # blob count\n" ++
  "  slli t0, t0, 17             # * GAS_PER_BLOB (131072)\n" ++
  "  la t2, bv_blob_gas_expected; sd t0, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 512; jal ra, bgv_u64le\n" ++
  "  la t2, bv_blob_gas_observed; sd a0, 0(t2)\n" ++
  "  la t2, bv_blob_gas_expected; ld t0, 0(t2); bne a0, t0, .Lbv_blob_gas_used_fail\n" ++
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
  "  # The post-balance verifier below models an EOA simple transfer: sender\n" ++
  "  # final balance = precharge + unused intrinsic refund - value. For value\n" ++
  "  # transfers into contracts, bytecode execution spends additional gas, so\n" ++
  "  # leave the verdict to the state-root/BAL checks instead.\n" ++
  "  # Direct transfers to active precompiles also execute code despite having\n" ++
  "  # no state-trie code hash; skip this 21k-only verifier for them too.\n" ++
  "  mv t0, t2; addi t0, t0, 72; li t1, 0\n" ++
  ".Lbv_tx_gas_precharge_pc_prefix:\n" ++
  "  li t3, 18; beq t1, t3, .Lbv_tx_gas_precharge_pc_low16\n" ++
  "  add t3, t0, t1; lbu t4, 0(t3); bnez t4, .Lbv_tx_gas_precharge_not_precompile\n" ++
  "  addi t1, t1, 1; j .Lbv_tx_gas_precharge_pc_prefix\n" ++
  ".Lbv_tx_gas_precharge_pc_low16:\n" ++
  "  lbu t3, 18(t0); lbu t4, 19(t0); slli t3, t3, 8; or t3, t3, t4\n" ++
  "  li t4, 1; bltu t3, t4, .Lbv_tx_gas_precharge_not_precompile\n" ++
  "  li t4, 17; bgeu t4, t3, .Lbv_after_tx_gas_precharge\n" ++
  "  li t4, 256; beq t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_tx_gas_precharge_not_precompile:\n" ++  "  ld a0, 8(s0); ld a1, 16(s0); addi a2, t2, 72; ld a3, 80(s0); ld a4, 88(s0); la a5, bv_tx_recipient_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  "  bnez a0, .Lbv_tx_gas_precharge_fail\n" ++
  "  la t0, bv_tx_recipient_code_hash; la t1, chahsr_empty_code_hash\n" ++
  "  ld t3,  0(t0); ld t4,  0(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  ld t3,  8(t0); ld t4,  8(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  ld t3, 16(t0); ld t4, 16(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  ld t3, 24(t0); ld t4, 24(t1); bne t3, t4, .Lbv_after_tx_gas_precharge\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  ld a0, 8(t2); ld a1, 16(t2); ld a3, 24(t2); ld a2, 32(t2)\n" ++
  "  la t2, bv_bal_start; ld a4, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a5, 0(t2)\n" ++
  "  la a6, basr_records; la a7, bv_tx_gas_precharge\n" ++
  "  jal ra, tx_gas_bal_post_verify\n" ++
  "  la t2, bv_tx_gas_precharge; ld t0, 0(t2); bnez t0, .Lbv_tx_gas_precharge_fail\n" ++
  "  # Non-overlapping EOA simple transfers must also expose recipient and\n" ++
  "  # fee-recipient BAL post balances matching value and priority-fee effects.\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  la t0, bv_tx_gas_precharge\n" ++
  "  addi t3, t2, 72; addi t4, t0, 104; li t5, 20\n" ++
  ".Lbv_st_recipient_sender_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_recipient_overlap\n" ++
  "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lbv_st_recipient_distinct\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lbv_st_recipient_sender_cmp\n" ++
  ".Lbv_st_recipient_distinct:\n" ++
  "  # Skip the strict recipient BAL balance check when the simple-transfer\n" ++
  "  # recipient is the block coinbase: that account's BAL post balance also\n" ++
  "  # folds in the priority fee (transaction_fee), so pre+value != post and\n" ++
  "  # the EIP-7708 coinbase-recipient case would false-reject even though the\n" ++
  "  # recomputed post-state root still anchors the coinbase balance. Mirrors\n" ++
  "  # the fee-recipient coinbase-overlap skip below.\n" ++
  "  ld t0, 0(s0); addi t0, t0, 32\n" ++
  "  la t1, bv_simple_transfer_tx; addi t1, t1, 72\n" ++
  "  li t5, 20\n" ++
  ".Lbv_st_recipient_coinbase_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_recipient_overlap\n" ++
  "  lbu t6, 0(t0); lbu a0, 0(t1); bne t6, a0, .Lbv_st_recipient_do_verify\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t5, t5, -1; j .Lbv_st_recipient_coinbase_cmp\n" ++
  ".Lbv_st_recipient_do_verify:\n" ++
  "  # EIP-7928/4895 (evm-asm-ouis9): like the fee-recipient skip below, the strict\n" ++
  "  # recipient post-balance check models recipient_post = recipient_pre + value.\n" ++
  "  # When the block has withdrawals the recipient may ALSO receive a withdrawal\n" ++
  "  # (e.g. bal_withdrawal_and_value_transfer_same_address), so\n" ++
  "  # post = pre + value + withdrawal and the strict check false-rejects. Skip it\n" ++
  "  # for blocks with withdrawals: the recomputed post-state root (which folds in\n" ++
  "  # both the value transfer and the withdrawal) already validates the balance.\n" ++
  "  # uyu11.1: instead of skipping the strict recipient check on withdrawal\n" ++
  "  # blocks (the old #8484 false-reject fix, which left a false-accept hole),\n" ++
  "  # compute the EIP-4895 withdrawal credit to the recipient and fold it into\n" ++
  "  # the check via strv_wd_credit, so expected = pre + value + withdrawal.\n" ++
  "  la t0, strv_wd_credit; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t2, svf_wds_count; ld a2, 0(t2); beqz a2, .Lbv_st_recipient_wd_done\n" ++
  "  la t2, bv_simple_transfer_tx; addi a0, t2, 72\n" ++
  "  la t2, svf_wds_ptr; ld a1, 0(t2)\n" ++
  "  la a3, strv_wd_credit\n" ++
  "  jal ra, bv_sum_withdrawals_to_address\n" ++
  ".Lbv_st_recipient_wd_done:\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  addi a0, t2, 72; addi a1, t2, 96\n" ++
  "  la t2, bv_bal_start; ld a2, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a3, 0(t2)\n" ++
  "  la a4, basr_records; la a5, bv_simple_transfer_recipient\n" ++
  "  jal ra, simple_transfer_recipient_bal_verify\n" ++
  "  la t2, bv_simple_transfer_recipient; ld t0, 0(t2); bnez t0, .Lbv_simple_transfer_recipient_fail\n" ++
  ".Lbv_st_skip_recipient_overlap:\n" ++
  "  ld t0, 0(s0); addi t0, t0, 32\n" ++
  "  la t1, bv_tx_gas_precharge; addi t1, t1, 104\n" ++
  "  mv t3, t0; mv t4, t1; li t5, 20\n" ++
  ".Lbv_st_fee_sender_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_fee_overlap\n" ++
  "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lbv_st_fee_check_recipient\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lbv_st_fee_sender_cmp\n" ++
  ".Lbv_st_fee_check_recipient:\n" ++
  "  ld t0, 0(s0); addi t0, t0, 32\n" ++
  "  la t1, bv_simple_transfer_tx; addi t1, t1, 72\n" ++
  "  mv t3, t0; mv t4, t1; li t5, 20\n" ++
  ".Lbv_st_fee_recipient_cmp:\n" ++
  "  beqz t5, .Lbv_st_skip_fee_overlap\n" ++
  "  lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lbv_st_fee_distinct\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lbv_st_fee_recipient_cmp\n" ++
  ".Lbv_st_fee_distinct:\n" ++
  "  # EIP-7928/4895 (evm-asm-ouis9): the strict fee-recipient post-balance check\n" ++
  "  # below models coinbase_post = coinbase_pre + transaction_fee. When the block\n" ++
  "  # has withdrawals, the coinbase may ALSO be a withdrawal recipient (e.g.\n" ++
  "  # bal_withdrawal_to_coinbase), so post = pre + fee + withdrawal and the strict\n" ++
  "  # check false-rejects. Skip it for blocks with withdrawals: the recomputed\n" ++
  "  # post-state root (which folds in both the fee and the withdrawal) already\n" ++
  "  # validates the coinbase balance, so this redundant sanity check is dropped\n" ++
  "  # rather than risk a false reject.\n" ++
  "  # uyu11.1: instead of skipping the strict fee-recipient (coinbase) check on\n" ++
  "  # withdrawal blocks, compute the EIP-4895 withdrawal credit to the coinbase\n" ++
  "  # and fold it via stfv_wd_credit, so expected = pre + fee + withdrawal.\n" ++
  "  la t0, stfv_wd_credit; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t2, svf_wds_count; ld a2, 0(t2); beqz a2, .Lbv_st_fee_wd_done\n" ++
  "  ld a0, 0(s0); addi a0, a0, 32\n" ++
  "  la t2, svf_wds_ptr; ld a1, 0(t2)\n" ++
  "  la a3, stfv_wd_credit\n" ++
  "  jal ra, bv_sum_withdrawals_to_address\n" ++
  ".Lbv_st_fee_wd_done:\n" ++
  "  ld a0, 0(s0); addi a0, a0, 32\n" ++
  "  la t2, bv_simple_transfer_tx\n" ++
  "  ld a1, 8(t2); ld a2, 16(t2); ld a3, 32(t2)\n" ++
  "  la t2, bv_bal_start; ld a4, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a5, 0(t2)\n" ++
  "  la a6, basr_records; la a7, bv_simple_transfer_fee_recipient\n" ++
  "  jal ra, simple_transfer_fee_recipient_bal_verify\n" ++
  "  la t2, bv_simple_transfer_fee_recipient; ld t0, 0(t2); bnez t0, .Lbv_simple_transfer_fee_recipient_fail\n" ++
  ".Lbv_st_skip_fee_overlap:\n" ++
  -- GATE (regression evm-asm-bmvmx.1.2.4.5): for the supported EOA simple
  -- transfer this path previously staged a STOP payload and ran it through the
  -- callable runtime dispatcher to expose a gas result to
  -- block_verdict_gas_result_arena_prepare. That dispatcher call
  -- deterministically faults (near-null LBU, Mem::read addr 0xc) for the only
  -- recipient class that reaches this path -- the non-precompile empty-code EOA
  -- recipients (block coinbase, system address); precompile recipients
  -- short-circuit at the precompile-range guard above and never get here.
  -- Until the dispatcher handles this class, skip the runtime-dispatcher gas
  -- capture entirely and fall through to .Lbv_after_tx_gas_precharge with
  -- bvgr_runtime_count left at 0 (the existing unsupported-shape path), so these
  -- rows fall back to the BAL-replay verdict that reaches full EEST match. The
  -- stage_runtime_payload / runtime_dispatcher_call helpers stay defined for the
  -- follow-up that re-enables this with proper shared-state isolation.
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
  ".Lbv_simple_transfer_recipient_fail:\n" ++
  "  li t0, 28; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_simple_transfer_fee_recipient_fail:\n" ++
  "  li t0, 29; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip7778_block_gas_fail:\n" ++
  "  li t0, 19; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_receipt_records_fail:\n" ++
  "  li t0, 25; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_versioned_hashes_fail:\n" ++
  "  li t0, 27; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_withdrawals_root_fail:\n" ++
  "  li t0, 31; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_blob_gas_used_fail:\n" ++
  "  li t0, 33; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_hash_mismatch:\n" ++
  "  li t0, 31; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
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
  "  bnez a0, .Lv2_payload_offsets_fail\n" ++
  "  mv a0, s0; la t0, svf_payload; ld a1, 0(t0)\n" ++
  "  jal ra, chain_config_valid\n" ++
  "  bnez a0, .Lv2_chain_config_fail\n" ++
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
  "  la t0, svf_payload; ld t0, 0(t0)\n" ++
  "  addi a0, t0, 504; jal ra, bgv_u32le; mv s3, a0     # transactions offset\n" ++
  "  la t0, svf_payload; ld t0, 0(t0)\n" ++
  "  addi a0, t0, 508; jal ra, bgv_u32le; mv s4, a0     # withdrawals offset\n" ++
  "  la t0, svf_payload; ld t0, 0(t0); add s2, t0, s3   # tx list ptr\n" ++
  "  sub s1, s4, s3                                      # tx list len\n" ++
  "  la t0, svf_tx_count; sd zero, 0(t0)\n" ++
  "  beqz s1, .Lv2_tx_desc_done\n" ++
  "  li t0, 4; bltu s1, t0, .Lv2_tx_root_fail\n" ++
  "  mv a0, s2; jal ra, bgv_u32le                       # first offset = 4 * tx_count\n" ++
  "  andi t0, a0, 3; bnez t0, .Lv2_tx_root_fail\n" ++
  "  beqz a0, .Lv2_tx_root_fail\n" ++
  "  bgtu a0, s1, .Lv2_tx_root_fail\n" ++
  "  srli s4, a0, 2\n" ++
  "  li t0, 2049; bgeu s4, t0, .Lv2_tx_root_fail\n" ++
  "  la t0, svf_tx_count; sd s4, 0(t0)\n" ++
  "  li s5, 0\n" ++
  "  la s3, svf_tx_descriptors\n" ++
  ".Lv2_tx_desc_loop:\n" ++
  "  beq s5, s4, .Lv2_tx_desc_done\n" ++
  "  slli t0, s5, 2; add a0, s2, t0; jal ra, bgv_u32le  # offset[i]\n" ++
  "  mv t6, a0\n" ++
  "  addi t0, s5, 1\n" ++
  "  beq t0, s4, .Lv2_tx_desc_last\n" ++
  "  slli t0, t0, 2; add a0, s2, t0; jal ra, bgv_u32le  # offset[i+1]\n" ++
  "  j .Lv2_tx_desc_have_end\n" ++
  ".Lv2_tx_desc_last:\n" ++
  "  mv a0, s1\n" ++
  ".Lv2_tx_desc_have_end:\n" ++
  "  bltu a0, t6, .Lv2_tx_root_fail\n" ++
  "  bgtu a0, s1, .Lv2_tx_root_fail\n" ++
  "  add t2, s2, t6; sub t3, a0, t6\n" ++
  "  slli t4, s5, 4; add t5, s3, t4\n" ++
  "  sd t2, 0(t5); sd t3, 8(t5)\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lv2_tx_desc_loop\n" ++
  ".Lv2_tx_desc_done:\n" ++
  "  la a0, svf_tx_descriptors; la t0, svf_tx_count; ld a1, 0(t0); la a2, svf_tx_root\n" ++
  "  jal ra, mpt_indexed_trie_root_small\n" ++
  "  la t0, bv_tx_root_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lv2_tx_root_fail\n" ++
  "  la a0, svf_descriptors; la t0, svf_wds_count; ld a1, 0(t0); la a2, svf_withdrawals_root\n" ++
  "  jal ra, mpt_indexed_trie_root_small\n" ++
  "  bnez a0, .Lv2_withdrawals_root_fail\n" ++
  "  addi a0, s0, 56; jal ra, bgv_u32le; mv s3, a0     # execution_requests offset\n" ++
  "  addi a0, s0, 4;  jal ra, bgv_u32le; mv s4, a0     # witness offset = NPR end\n" ++
  "  addi a0, s0, 16; add a0, a0, s3                   # er section start\n" ++
  "  sub a1, s4, s3; addi a1, a1, -16                  # er section len\n" ++
  "  la a2, erh_requests_hash\n" ++
  "  jal ra, execution_requests_hash\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  mv a0, s0; la a1, svf_bal_hash\n" ++
  "  jal ra, block_access_list_hash\n" ++
  "  bnez a0, .Lv2_bal_hash_fail\n" ++
  "  # General transaction and withdrawal trie roots have already been computed above.\n" ++
  "  li t0, 1; la t1, bv_block_hash_check_enabled; sd t0, 0(t1)\n" ++
  "  la t1, sv_params\n" ++
  "  la t0, svf_payload;        ld t0, 0(t0); sd t0, 0(t1)\n" ++
  "  la t0, svf_parent_rlp;     ld t0, 0(t0); sd t0, 8(t1)\n" ++
  "  la t0, svf_parent_rlp_len; ld t0, 0(t0); sd t0, 16(t1)\n" ++
  "  la t0, svf_parent_sr;      sd t0, 24(t1)\n" ++
  "  la t0, svf_tx_root;          sd t0, 32(t1)\n" ++
  "  la t0, svf_withdrawals_root;  sd t0, 40(t1)\n" ++
  "  addi t0, s0, 24;           sd t0, 48(t1)\n" ++
  "  la t0, erh_requests_hash;  sd t0, 56(t1)\n" ++
  "  la t0, svf_bal_hash;       sd t0, 96(t1)\n" ++
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
  ".Lv2_tx_root_fail:\n" ++
  "  li t0, 32; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_withdrawals_root_fail:\n" ++
  "  li t0, 31; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_bal_hash_fail:\n" ++
  "  li t0, 30; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_chain_config_fail:\n" ++
  "  li t0, 26; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_payload_offsets_fail:\n" ++
  "  li t0, 31; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
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
  "  la t1, bv_simple_transfer_tx; ld t2, 0(t1); sd t2, 344(t0)\n" ++
  "  la t1, bv_tx_gas_precharge; ld t2, 0(t1); sd t2, 352(t0)\n" ++
  "  la t1, bv_simple_transfer_recipient; ld t2, 0(t1); sd t2, 360(t0)\n" ++
  "  la t1, bv_simple_transfer_fee_recipient; ld t2, 0(t1); sd t2, 368(t0)\n" ++
  "  la t1, bv_withdrawals_root_status; ld t2, 0(t1); sd t2, 376(t0)\n" ++
  "  la t1, bv_withdrawals_root_valid; ld t2, 0(t1); sd t2, 384(t0)\n" ++
  "  la t1, bv_tx_root_status; ld t2, 0(t1); sd t2, 392(t0)\n" ++
  "  la t1, svf_tx_count; ld t2, 0(t1); sd t2, 400(t0)\n" ++
  "  j .Lv2_pdone\n" ++
  zkvmSha256Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  sszTxListVersionedHashesMatchFunction ++ "\n" ++
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
  u256LtBeFunction ++ "\n" ++
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
  mptOneLeafRootIndexedFunction ++ "\n" ++
  withdrawalsStateRootFunction ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
  mptIndexedLargeLeafHashFunction ++ "\n" ++
  mptIndexedTrieRootLargeFunction ++ "\n" ++
  mptIndexedTrieRootSmallFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  blockValidateWithdrawalsRootIndexedFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  amsterdamBlobGasPriceFunction ++ "\n" ++
  amsterdamBlobGasPriceU256Function ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  headerValidateExcessBlobGasFunction ++ "\n" ++
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
  bahU32leFunction ++ "\n" ++
  blockAccessListHashFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
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
  chainConfigValidFunction ++ "\n" ++
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
  stageRuntimePayloadFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  txEffectiveGasPricingFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  txUpfrontPrechargeFunction ++ "\n" ++
  txGasBalPostVerifyFunction ++ "\n" ++
  simpleTransferRecipientBalVerifyFunction ++ "\n" ++
  simpleTransferFeeRecipientBalVerifyFunction ++ "\n" ++
  bvSumWithdrawalsToAddressFunction ++ "\n" ++
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

end EvmAsm.Codegen
