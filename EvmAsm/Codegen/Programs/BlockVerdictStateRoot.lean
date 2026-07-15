/-
  EvmAsm.Codegen.Programs.BlockVerdictStateRoot

  block_state_root + stateless_verdict_v2 String defs, extracted from
  BlockVerdict.lean to keep that file under the 1500-line FileSizeGuard cap
  (EvmAsm/Codegen/Programs/FileSizeGuard.lean). Byte-identical move: these two
  defs do not reference block_verdict, so relocating them leaves the emitted
  assembly unchanged. Re-imported by BlockVerdict.lean for the probe prologue.
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
import EvmAsm.Codegen.Programs.BlockVerdictGasResultArena
import EvmAsm.Codegen.Programs.BlockVerdictTxGasLimits
import EvmAsm.Codegen.Programs.BlockVerdictTransactions
import EvmAsm.Codegen.Programs.MptEncodeLeafBranch
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.SszWithdrawal
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.WithdrawalsRootIndexed
import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
import EvmAsm.Codegen.Programs.SenderBalanceDebit
import EvmAsm.Codegen.Programs.TxGasBalPostVerifyRuntime
import EvmAsm.Codegen.Programs.SenderPostNonceConsistent
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.SlotTupleSequencesMatch
import EvmAsm.Codegen.Programs.AccountTupleSequencesConsistent
import EvmAsm.Codegen.Programs.BalAllAccountsTupleSequences
import EvmAsm.Codegen.Programs.SimpleTransferRecipient
import EvmAsm.Codegen.Programs.SimpleTransferFeeRecipient
import EvmAsm.Codegen.Programs.BlockVerdictSysChange
import EvmAsm.Codegen.Programs.BlockVerdictSystemStorageCapture
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
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  sd s6, 48(sp); sd s7, 56(sp)\n" ++
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
  -- v0.6.0: process_unchecked_system_transaction runs the CONTRACT's code
  -- (fork.py:890-905); an absent or codeless history/beacon-roots contract
  -- executes nothing and writes nothing. Gate each modeled startup write on
  -- the pre-state account existing with a non-empty code hash; skipping a
  -- contract zeroes its descriptor value lengths so the modeled tuple-row
  -- append becomes a no-op for it as well.
  "  la t0, bsr_sys_has_2935; li t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, bsr_sys_has_4788; li t1, 1; sd t1, 0(t0)\n" ++
  "  la a0, bsr_addr_2935; li a1, 20\n" ++
  "  la t0, bsr_root_p; ld a2, 0(t0); la t0, bsr_wit_p; ld a3, 0(t0); la t0, bsr_wl_v; ld a4, 0(t0)\n" ++
  "  la a5, bsr_sys_acct\n" ++
  "  jal ra, account_at_address\n" ++
  "  li t0, 1; beq a0, t0, .Lbsr_2935_absent\n" ++
  "  bnez a0, .Lbsr_cons_sys2935\n" ++
  "  la t0, bsr_sys_acct; addi t0, t0, 72; la t1, cd_empty_code_hash; li t2, 32\n" ++
  ".Lbsr_2935_ch_cmp:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbsr_2935_gated\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbsr_2935_ch_cmp\n" ++
  ".Lbsr_2935_absent:\n" ++
  "  la t0, bsr_sys_has_2935; sd zero, 0(t0)\n" ++
  "  la t0, swd_2935_vlen; sd zero, 0(t0)\n" ++
  ".Lbsr_2935_gated:\n" ++
  "  la a0, bsr_addr_4788; li a1, 20\n" ++
  "  la t0, bsr_root_p; ld a2, 0(t0); la t0, bsr_wit_p; ld a3, 0(t0); la t0, bsr_wl_v; ld a4, 0(t0)\n" ++
  "  la a5, bsr_sys_acct\n" ++
  "  jal ra, account_at_address\n" ++
  "  li t0, 1; beq a0, t0, .Lbsr_4788_absent\n" ++
  "  bnez a0, .Lbsr_cons_sys4788\n" ++
  "  la t0, bsr_sys_acct; addi t0, t0, 72; la t1, cd_empty_code_hash; li t2, 32\n" ++
  ".Lbsr_4788_ch_cmp:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbsr_4788_gated\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbsr_4788_ch_cmp\n" ++
  ".Lbsr_4788_absent:\n" ++
  "  la t0, bsr_sys_has_4788; sd zero, 0(t0)\n" ++
  "  la t0, swd_4788_vlen; sd zero, 0(t0)\n" ++
  "  la t0, swd_4788_root_vlen; sd zero, 0(t0)\n" ++
  ".Lbsr_4788_gated:\n" ++
  "  jal ra, append_modeled_system_storage_tuple_rows; bnez a0, .Lbsr_cons_change_cap\n" ++
  "  li s1, 0                     # change counter\n" ++
  "  la t0, bsr_sys_has_2935; ld t0, 0(t0); beqz t0, .Lbsr_skip_2935\n" ++
  "  # system change = EIP-2935\n" ++
  "  la a0, bsr_addr_2935; la a1, swd_2935_slot; la a2, swd_2935_val\n" ++
  "  la t0, swd_2935_vlen; ld a3, 0(t0); mv a4, s1\n" ++
  "  la t0, bsr_sys_slot_2935; sd s1, 0(t0)\n" ++
  "  jal ra, bsr_sys_change; bnez a0, .Lbsr_cons_sys2935\n" ++
  "  addi s1, s1, 1\n" ++
  ".Lbsr_skip_2935:\n" ++
  "  la t0, bsr_sys_has_4788; ld t0, 0(t0); beqz t0, .Lbsr_skip_4788\n" ++
  "  # system change = EIP-4788 (timestamp + parent-root slots in one account)\n" ++
  "  mv a4, s1\n" ++
  "  la t0, bsr_sys_slot_4788; sd s1, 0(t0)\n" ++
  "  jal ra, bsr_beacon_change; bnez a0, .Lbsr_cons_sys4788\n" ++
  "  addi s1, s1, 1\n" ++
  ".Lbsr_skip_4788:\n" ++
  "  # BAL account changes are tx-execution account post-values.\n" ++
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
  "  la t0, bsr_bal_start; ld a0, 0(t0); la t0, bsr_bal_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_walk_init; bnez a2, .Lbsr_cons_bal_desc\n" ++
  "  mv s6, a0; mv s7, a1       # BAL cursor/end for sequential row copy\n" ++
  "  li s0, 0                     # scan BAL records; append only changed accounts\n" ++
  ".Lbsr_bal_copy:\n" ++
  "  la t6, bsr_bal_count; ld t6, 0(t6); beq s0, t6, .Lbsr_bal_copied\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n" ++
  "  ld t4, 16(t3); li t5, 3; beq t4, t5, .Lbsr_bal_copy_load_item\n" ++
  ".Lbsr_bal_copy_load_item:\n" ++
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbsr_cons_bal_desc\n" ++
  "  mv s6, a0\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n" ++
  "  ld a0, 0(t3); ld a1, 8(t3); mv a3, a2; sub a2, s6, a3; ld a4, 16(t3)\n" ++
  "  la t0, bsr_bal_item_ptr; sd a2, 0(t0); la t0, bsr_bal_item_len; sd a3, 0(t0)\n" ++
  "  mv a0, a2; mv a1, a3; jal ra, bal_account_is_modeled_system\n" ++
  "  li t0, 1; beq a0, t0, .Lbsr_bal_copy_system2935\n  li t0, 2; beq a0, t0, .Lbsr_bal_copy_system4788\n  bnez a0, .Lbsr_cons_bal_desc\n" ++
  ".Lbsr_bal_copy_normal:\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n  ld t4, 16(t3); li t5, 3; beq t4, t5, .Lbsr_bal_copy_next\n" ++
  "  slli t3, s0, 4; slli t4, s0, 3; add t3, t3, t4; la t4, basr_records; add t3, t4, t3\n" ++
  "  ld a0, 0(t3); ld a1, 8(t3); la t0, bsr_bal_item_ptr; ld a2, 0(t0); la t0, bsr_bal_item_len; ld a3, 0(t0); ld a4, 16(t3)\n" ++
  "  slli t2, s1, 5; slli t3, s1, 3; add t2, t2, t3; la t3, bsr_changes; add a5, t3, t2\n" ++
  "  slli t2, s1, 6; la t3, basr_paths; add a6, t3, t2\n" ++
  "  slli t2, s1, 8; la t3, basr_values; add a7, t3, t2\n" ++
  "  jal ra, bal_account_change_descriptor; bnez a0, .Lbsr_cons_bal_desc\n" ++
  "  la t0, bsr_changed_account_count; ld t1, 0(t0); li t2, " ++ toString bsrMaxAccessAccounts ++ "; bgeu t1, t2, .Lbsr_changed_addr_record_skip\n" ++
  "  slli t2, t1, 5; la t3, bsr_changed_accounts; add t3, t3, t2\n" ++
  "  la t4, bsr_bal_item_ptr; ld a0, 0(t4); la t4, bsr_bal_item_len; ld a1, 0(t4)\n" ++
  "  jal ra, rlp_walk_init; bnez a2, .Lbsr_cons_bal_desc\n" ++
  "  jal ra, rlp_walk_next; bnez a1, .Lbsr_cons_bal_desc\n" ++
  "  li t5, 20; bne a2, t5, .Lbsr_cons_bal_desc\n" ++
  "  sub t4, a0, a2\n" ++
  "  la t0, bsr_changed_account_count; ld t1, 0(t0)\n" ++
  "  slli t2, t1, 5; la t3, bsr_changed_accounts; add t3, t3, t2\n" ++
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
  ".Lbsr_bal_copy_system2935:\n  la t0, bsr_sys_has_2935; ld t0, 0(t0); beqz t0, .Lbsr_bal_copy_normal\n  la t0, bsr_bal_item_ptr; ld a0, 0(t0); la t0, bsr_bal_item_len; ld a1, 0(t0); la t0, bsr_sys_slot_2935; ld a2, 0(t0)\n  jal ra, bsr_apply_modeled_system_post_fields; bnez a0, .Lbsr_cons_bal_desc\n  j .Lbsr_bal_copy_next\n" ++
  ".Lbsr_bal_copy_system4788:\n  la t0, bsr_sys_has_4788; ld t0, 0(t0); beqz t0, .Lbsr_bal_copy_normal\n  la t0, bsr_bal_item_ptr; ld a0, 0(t0); la t0, bsr_bal_item_len; ld a1, 0(t0); la t0, bsr_sys_slot_4788; ld a2, 0(t0)\n  jal ra, bsr_apply_modeled_system_post_fields; bnez a0, .Lbsr_cons_bal_desc\n  j .Lbsr_bal_copy_next\n" ++
  ".Lbsr_bal_copied:\n" ++
  ".Lbsr_bal_done:\n" ++
  "  # NORMALIZATION BOUNDARY: bsr_changes contains committed, value-bearing\n" ++
  "  # mutations only (BAL final post-fields plus modeled system/withdrawals).\n" ++
  "  # Runtime account/storage access outcomes are mode=3 no-ops: they provide\n" ++
  "  # access evidence but never a state-root value, so do not materialize them\n" ++
  "  # in this C-sized builder input. In particular, reverted storage windows\n" ++
  "  # have zero committed entries and cannot become a last-write-wins value.\n" ++
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
  "  li t6, 0                     # compose with every earlier committed mutation [0, s1)\n" ++
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
  "  jal ra, mpt_bounded_state_root\n" ++
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
  "  ld s6, 48(sp); ld s7, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
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
  "  # ExecutionWitness.state is SSZ List[ByteList[1024]]: validate the\n" ++
  "  # per-element cap after the state-only index has checked its offset table.\n" ++
  "  # Do not put this rule in the generic index: witness.headers/codes differ.\n" ++
  "  la t0, widx_count; ld t0, 0(t0); la t1, widx_records; li t2, 1024\n" ++
  ".Lv2_state_node_cap_loop:\n" ++
  "  beqz t0, .Lv2_state_node_cap_ok\n" ++
  "  ld t3, 40(t1); bgtu t3, t2, .Lv2_witness_index_fail\n" ++
  "  addi t1, t1, 48; addi t0, t0, -1; j .Lv2_state_node_cap_loop\n" ++
  ".Lv2_state_node_cap_ok:\n" ++
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
  "  mv a0, t2; mv a1, t4; jal ra, witness_codes_index_build\n" ++
  "  bnez a0, .Lv2_witness_codes_index_fail\n" ++
  "  la t1, svf_witness_section; ld t0, 0(t1); addi a0, t0, 8; jal ra, bgv_u32le # headers offset\n" ++
  "  mv t6, a0\n" ++
  "  la t1, svf_witness_section; ld t0, 0(t1); add t2, t0, t6\n" ++
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
  -- 3zxnu: ExecutionPayload.withdrawals is SszList[Withdrawal, MAX_WITHDRAWALS_PER_PAYLOAD=16]
  -- (stateless_ssz.py:46,108); a payload with >16 withdrawals fails to deserialize and is
  -- rejected. The .Lv2_wl loop below writes svf_descriptors (256B=16) + svf_rlp_arena
  -- (1152B=16), so an uncapped count would overflow into adjacent .data. Cap at 16 and
  -- reject beyond (mirrors the transactions cap `bgeu s4, 2049, .Lv2_tx_root_fail`).
  "  li t0, 17; bgeu s1, t0, .Lv2_withdrawals_root_fail\n" ++
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
  -- 8uld3.2.3.3.1 Fix3 / fhsxz.2.4.2.66: the system-call derives below run runtime_dispatcher_call,
  -- which clobbers ALL s-registers (SystemCallStaging:96-99 — resets sp to lp64_sp_top and the
  -- predeploy EVM execution overwrites the s-regs) AND, on an OUT-OF-GAS predeploy, writes far
  -- enough into memory to clobber guest data globals too. s0(SSZ_BASE)/s3(er offset) are needed
  -- AFTER the derives (deposit extraction, block_access_list_hash,
  -- block_verdict). Saving them to data globals (c1_saved_s0/s3) was unsafe — the OOG predeploy
  -- clobbered those globals with 0xb6 (.66 crash) — so they are RE-DERIVED from the stable input
  -- region after the last derive (see below); no save needed.
  -- 8uld3.2.3.3.1 (C.1): hash the EXECUTION-DERIVED withdrawal(EIP-7002)+consolidation(EIP-7251)
  -- request bodies instead of trusting the SSZ-input ones. Deposits remain SSZ-backed for
  -- tx-bearing prelude setup until the receipt tail derives them from logs; no-tx blocks use
  -- the empty derived deposit body before header rebuild, since no transaction can emit a
  -- deposit-contract log.
  -- Snapshot/restore the exec-log count (evm_env+448) around the system calls so their SSTORE
  -- effects stay OUT of the storage comparator (preserving its current passing behavior; the
  -- 7002/7251 predeploy writes are EIP-7928 index-0 system writes the comparator already
  -- tolerates). s0=NPR base, s3=er offset survive (callees preserve s-regs). The predeploy code
  -- is resolved at the PRE-state (parent header). witness.state = svf_witness_section+off0 ..
  -- svf_codes_ptr; witness.codes = svf_codes_ptr/len.
  "  la t0, evm_env; ld t1, 448(t0); la t2, c1_saved_logcount; sd t1, 0(t2)\n" ++
  "  la t2, c1_system_log_cursor; sd t1, 0(t2)\n" ++
  "  la t2, bv_system_storage_log_count; sd zero, 0(t2)\n" ++
  -- 8uld3.2.3.3.1 Fix1: parse the block BAL at the requests_hash point (bsr_bal_start is the
  -- block_state_root context's, 0 here). s0 is the BAL input (block_access_list_hash uses it @484).
  "  mv a0, s0; la a1, c1_bal_start; la a2, c1_bal_len; la a3, c1_bal_count; jal ra, bal_section_info\n" ++
  -- == WITHDRAWAL (EIP-7002): code_at -> BAL preload -> system call -> copy body ==
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, withdrawal_request_predeploy_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3\n" ++
  "  la t0, c1_wcode_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_wcode_len; sd t3, 0(t0)\n" ++
  "  la t0, c1_bal_start; ld a0, 0(t0); la t0, c1_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, withdrawal_request_predeploy_addr; la a3, c1_bal_acct_ptr; la a4, c1_bal_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lc1_w_nopreload\n" ++
  "  la t0, svf_parent_rlp; ld t1, 0(t0); la t2, sps_header; sd t1, 0(t2)\n" ++
  "  la t0, svf_parent_rlp_len; ld t1, 0(t0); la t2, sps_header_len; sd t1, 0(t2)\n" ++
  "  la t0, svf_witness; ld t1, 0(t0); la t2, sps_state; sd t1, 0(t2); la t2, sps_storage; sd t1, 0(t2)\n" ++
  "  la t0, svf_witness_len; ld t1, 0(t0); la t2, sps_state_len; sd t1, 0(t2); la t2, sps_storage_len; sd t1, 0(t2)\n" ++
  "  la t1, withdrawal_request_predeploy_addr; la t2, sps_addr; li t3, 20\n" ++
  ".Lc1_w_addr:\n" ++
  "  beqz t3, .Lc1_w_addrd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_w_addr\n" ++
  ".Lc1_w_addrd:\n" ++
  "  la t0, c1_bal_acct_ptr; ld a0, 0(t0); la t0, c1_bal_acct_len; ld a1, 0(t0); la a2, c1_preload\n" ++
  "  jal ra, stage_predeploy_storage_preload\n" ++
  -- fhsxz.2.4.2.66.1/.66.1.2: a count above the gas-derived bsrAccountSlotCap means
  -- NOTHING was staged (the preload bails write-nothing — including the per-slot
  -- tuple-overflow case); storing it would make stage_runtime_payload_code copy count*64
  -- garbage bytes from past c1_preload into the payload -> wrong execution. Conservative
  -- reject instead (sound: only blocks beyond the 200M BAL budget can trip this).
  "  li t1, " ++ toString bsrAccountSlotCap ++ "; bgtu a0, t1, .Lv2_requests_hash_fail\n" ++
  "  la t0, scc_preload_count; sd a0, 0(t0); la t1, c1_preload; la t0, scc_preload_ptr; sd t1, 0(t0)\n" ++
  "  j .Lc1_w_derive\n" ++
  ".Lc1_w_nopreload:\n" ++
  "  la t0, scc_preload_count; sd zero, 0(t0)\n" ++
  ".Lc1_w_derive:\n" ++
  "  la t0, c1_wcode_ptr; ld a0, 0(t0); la t0, c1_wcode_len; ld a1, 0(t0)\n" ++
  "  la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging\n" ++
  "  jal ra, derive_withdrawal_requests\n" ++
  "  bnez a2, .Lv2_requests_hash_fail\n" ++
  "  la t0, dbsr_wlen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_wbody; mv t3, a1\n" ++
  ".Lc1_w_copy:\n" ++
  "  beqz t3, .Lc1_w_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_w_copy\n" ++
  ".Lc1_w_copyd:\n" ++
  "  la t0, c1_system_log_cursor; ld a0, 0(t0); la t1, evm_env; ld a1, 448(t1); li a2, 0xa0630000; la a3, bv_system_storage_log; la a4, bv_system_storage_txindex; la a5, bv_system_storage_log_count\n" ++
  -- lv44p.2.2: end-of-block system calls run at block_access_index N+1 (= svf_tx_count+1).
  "  la t2, svf_tx_count; ld a6, 0(t2); addi a6, a6, 1\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  # side capture failure is non-fatal for verdict parity; request bodies were already copied\n" ++
  "  la t0, evm_env; ld t1, 448(t0); la t2, c1_system_log_cursor; sd t1, 0(t2)\n" ++
  -- == CONSOLIDATION (EIP-7251) ==
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, consolidation_request_predeploy_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3\n" ++
  "  la t0, c1_ccode_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_ccode_len; sd t3, 0(t0)\n" ++
  "  la t0, c1_bal_start; ld a0, 0(t0); la t0, c1_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, consolidation_request_predeploy_addr; la a3, c1_bal_acct_ptr; la a4, c1_bal_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lc1_c_nopreload\n" ++
  "  la t0, svf_parent_rlp; ld t1, 0(t0); la t2, sps_header; sd t1, 0(t2)\n" ++
  "  la t0, svf_parent_rlp_len; ld t1, 0(t0); la t2, sps_header_len; sd t1, 0(t2)\n" ++
  "  la t0, svf_witness; ld t1, 0(t0); la t2, sps_state; sd t1, 0(t2); la t2, sps_storage; sd t1, 0(t2)\n" ++
  "  la t0, svf_witness_len; ld t1, 0(t0); la t2, sps_state_len; sd t1, 0(t2); la t2, sps_storage_len; sd t1, 0(t2)\n" ++
  "  la t1, consolidation_request_predeploy_addr; la t2, sps_addr; li t3, 20\n" ++
  ".Lc1_c_addr:\n" ++
  "  beqz t3, .Lc1_c_addrd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_c_addr\n" ++
  ".Lc1_c_addrd:\n" ++
  "  la t0, c1_bal_acct_ptr; ld a0, 0(t0); la t0, c1_bal_acct_len; ld a1, 0(t0); la a2, c1_preload\n" ++
  "  jal ra, stage_predeploy_storage_preload\n" ++
  -- fhsxz.2.4.2.66.1/.66.1.2: same gas-derived >cap conservative reject as the
  -- withdrawal site above.
  "  li t1, " ++ toString bsrAccountSlotCap ++ "; bgtu a0, t1, .Lv2_requests_hash_fail\n" ++
  "  la t0, scc_preload_count; sd a0, 0(t0); la t1, c1_preload; la t0, scc_preload_ptr; sd t1, 0(t0)\n" ++
  "  j .Lc1_c_derive\n" ++
  ".Lc1_c_nopreload:\n" ++
  "  la t0, scc_preload_count; sd zero, 0(t0)\n" ++
  ".Lc1_c_derive:\n" ++
  "  la t0, c1_ccode_ptr; ld a0, 0(t0); la t0, c1_ccode_len; ld a1, 0(t0)\n" ++
  "  la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging\n" ++
  "  jal ra, derive_consolidation_requests\n" ++
  "  bnez a2, .Lv2_requests_hash_fail\n" ++
  "  la t0, dbsr_clen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_cbody; mv t3, a1\n" ++
  ".Lc1_c_copy:\n" ++
  "  beqz t3, .Lc1_c_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_c_copy\n" ++
  ".Lc1_c_copyd:\n" ++
  "  la t0, c1_system_log_cursor; ld a0, 0(t0); la t1, evm_env; ld a1, 448(t1); li a2, 0xa0630000; la a3, bv_system_storage_log; la a4, bv_system_storage_txindex; la a5, bv_system_storage_log_count\n" ++
  -- lv44p.2.2: end-of-block system calls run at block_access_index N+1 (= svf_tx_count+1).
  "  la t2, svf_tx_count; ld a6, 0(t2); addi a6, a6, 1\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  # side capture failure is non-fatal for verdict parity; request bodies were already copied\n" ++
  "  la t0, evm_env; ld t1, 448(t0); la t2, c1_system_log_cursor; sd t1, 0(t2)\n" ++
  "  la t0, evm_env; la t2, c1_saved_logcount; ld t1, 0(t2); sd t1, 448(t0)\n" ++
  "  la t0, scc_preload_count; sd zero, 0(t0)\n" ++
  -- v0.6.0 (EIP-8282/C12): process_checked_system_transaction pre-checks that
  -- each BUILDER predeploy holds code (fork.py:985-1005 via :755-765) and
  -- raises InvalidBlock when it does not -- even though an absent contract's
  -- (empty) output would not change requests_hash. The spec reads through a
  -- TransactionState so a contract deployed EARLIER IN THIS BLOCK counts; the
  -- exec code-effect log carries that same-block case for the guest.
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_deposit_contract_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lc1_bd_same_block\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); bnez t0, .Lc1_bd_code_ok\n" ++
  ".Lc1_bd_same_block:\n" ++
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, builder_deposit_contract_addr\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  bnez a0, .Lc1_bd_code_ok\n" ++
  -- The BAL's declared code final for the builder address is the remaining
  -- same-block deployment signal (a deploy the guest's runtime did not replay,
  -- e.g. an unsupported top-level creation): the code comparators validate the
  -- BAL's code claims wherever execution is available, so a declared non-empty
  -- final mirrors the spec's TransactionState read of the just-deployed code.
  "  la t0, c1_bal_start; ld a0, 0(t0); la t0, c1_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_deposit_contract_addr; la a3, c1_bal_acct_ptr; la a4, c1_bal_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  la t0, c1_bal_acct_ptr; ld a0, 0(t0); la t0, c1_bal_acct_len; ld a1, 0(t0); la a2, bacc_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  la t0, bacc_finals; ld t1, 56(t0); beqz t1, .Lv2_requests_hash_fail\n" ++
  "  la t0, bacc_finals; ld t1, 72(t0); beqz t1, .Lv2_requests_hash_fail\n" ++
  ".Lc1_bd_code_ok:\n" ++
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_exit_contract_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lc1_be_same_block\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); bnez t0, .Lc1_be_code_ok\n" ++
  ".Lc1_be_same_block:\n" ++
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, builder_exit_contract_addr\n" ++
  "  jal ra, find_code_effect_by_address\n" ++
  "  bnez a0, .Lc1_be_code_ok\n" ++
  -- The BAL's declared code final for the builder address is the remaining
  -- same-block deployment signal (a deploy the guest's runtime did not replay,
  -- e.g. an unsupported top-level creation): the code comparators validate the
  -- BAL's code claims wherever execution is available, so a declared non-empty
  -- final mirrors the spec's TransactionState read of the just-deployed code.
  "  la t0, c1_bal_start; ld a0, 0(t0); la t0, c1_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_exit_contract_addr; la a3, c1_bal_acct_ptr; la a4, c1_bal_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  la t0, c1_bal_acct_ptr; ld a0, 0(t0); la t0, c1_bal_acct_len; ld a1, 0(t0); la a2, bacc_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  la t0, bacc_finals; ld t1, 56(t0); beqz t1, .Lv2_requests_hash_fail\n" ++
  "  la t0, bacc_finals; ld t1, 72(t0); beqz t1, .Lv2_requests_hash_fail\n" ++
  ".Lc1_be_code_ok:\n" ++
  -- EIP-8282: derive the builder deposit and builder exit request bodies through
  -- the same checked system-call path. Their queues are preloaded from the BAL
  -- exactly like the EIP-7002/7251 queues; empty return data is represented by
  -- a zero body length and is therefore omitted by the five-field assembler.
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_deposit_contract_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lc1_bd_derive_ready\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Lv2_requests_hash_fail\n" ++
  ".Lc1_bd_derive_ready:\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3; la t0, c1_bd_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_bd_code_len; sd t3, 0(t0)\n" ++
  "  la t0, c1_bal_start; ld a0, 0(t0); la t0, c1_bal_len; ld a1, 0(t0); la a2, builder_deposit_contract_addr; la a3, c1_bal_acct_ptr; la a4, c1_bal_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lc1_bd_no_preload\n" ++
  "  la t0, svf_parent_rlp; ld t1, 0(t0); la t2, sps_header; sd t1, 0(t2); la t0, svf_parent_rlp_len; ld t1, 0(t0); la t2, sps_header_len; sd t1, 0(t2)\n" ++
  "  la t0, svf_witness; ld t1, 0(t0); la t2, sps_state; sd t1, 0(t2); la t2, sps_storage; sd t1, 0(t2); la t0, svf_witness_len; ld t1, 0(t0); la t2, sps_state_len; sd t1, 0(t2); la t2, sps_storage_len; sd t1, 0(t2)\n" ++
  "  la t1, builder_deposit_contract_addr; la t2, sps_addr; li t3, 20\n" ++
  ".Lc1_bd_addr:\n  beqz t3, .Lc1_bd_addrd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_bd_addr\n" ++
  ".Lc1_bd_addrd:\n  la t0, c1_bal_acct_ptr; ld a0, 0(t0); la t0, c1_bal_acct_len; ld a1, 0(t0); la a2, c1_preload; jal ra, stage_predeploy_storage_preload\n" ++
  "  li t1, " ++ toString bsrAccountSlotCap ++ "; bgtu a0, t1, .Lv2_requests_hash_fail; la t0, scc_preload_count; sd a0, 0(t0); la t0, c1_preload; la t1, scc_preload_ptr; sd t0, 0(t1); j .Lc1_bd_call\n" ++
  ".Lc1_bd_no_preload:\n  la t0, scc_preload_count; sd zero, 0(t0)\n" ++
  ".Lc1_bd_call:\n  la t0, c1_bd_code_ptr; ld a0, 0(t0); la t0, c1_bd_code_len; ld a1, 0(t0); la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging; jal ra, derive_builder_deposit_requests\n" ++
  "  bnez a2, .Lv2_requests_hash_fail; la t0, dbsr_bdlen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_bdbody; mv t3, a1\n" ++
  ".Lc1_bd_copy:\n  beqz t3, .Lc1_bd_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_bd_copy\n" ++
  ".Lc1_bd_copyd:\n  la t0, scc_preload_count; sd zero, 0(t0)\n" ++
  -- Builder exit.
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0); la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0); la a2, builder_exit_contract_addr; la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0); jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Lc1_be_derive_ready\n  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Lv2_requests_hash_fail\n" ++
  ".Lc1_be_derive_ready:\n  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3; la t0, c1_be_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_be_code_len; sd t3, 0(t0)\n" ++
  "  la t0, c1_bal_start; ld a0, 0(t0); la t0, c1_bal_len; ld a1, 0(t0); la a2, builder_exit_contract_addr; la a3, c1_bal_acct_ptr; la a4, c1_bal_acct_len; jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lc1_be_no_preload\n  la t0, svf_parent_rlp; ld t1, 0(t0); la t2, sps_header; sd t1, 0(t2); la t0, svf_parent_rlp_len; ld t1, 0(t0); la t2, sps_header_len; sd t1, 0(t2); la t0, svf_witness; ld t1, 0(t0); la t2, sps_state; sd t1, 0(t2); la t2, sps_storage; sd t1, 0(t2); la t0, svf_witness_len; ld t1, 0(t0); la t2, sps_state_len; sd t1, 0(t2); la t2, sps_storage_len; sd t1, 0(t2)\n" ++
  "  la t1, builder_exit_contract_addr; la t2, sps_addr; li t3, 20\n  .Lc1_be_addr:\n  beqz t3, .Lc1_be_addrd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_be_addr\n  .Lc1_be_addrd:\n  la t0, c1_bal_acct_ptr; ld a0, 0(t0); la t0, c1_bal_acct_len; ld a1, 0(t0); la a2, c1_preload; jal ra, stage_predeploy_storage_preload\n" ++
  "  li t1, " ++ toString bsrAccountSlotCap ++ "; bgtu a0, t1, .Lv2_requests_hash_fail; la t0, scc_preload_count; sd a0, 0(t0); la t0, c1_preload; la t1, scc_preload_ptr; sd t0, 0(t1); j .Lc1_be_call\n" ++
  "  .Lc1_be_no_preload:\n  la t0, scc_preload_count; sd zero, 0(t0)\n" ++
  "  .Lc1_be_call:\n  la t0, c1_be_code_ptr; ld a0, 0(t0); la t0, c1_be_code_len; ld a1, 0(t0); la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging; jal ra, derive_builder_exit_requests\n" ++
  "  bnez a2, .Lv2_requests_hash_fail; la t0, dbsr_belen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_bebody; mv t3, a1\n" ++
  "  .Lc1_be_copy:\n  beqz t3, .Lc1_be_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_be_copy\n  .Lc1_be_copyd:\n  la t0, scc_preload_count; sd zero, 0(t0)\n" ++
  "  la t0, aer_bd_ptr; la t1, dbsr_bdbody; sd t1, 0(t0); la t0, aer_bd_len; la t1, dbsr_bdlen; ld t1, 0(t1); sd t1, 0(t0); la t0, aer_be_ptr; la t1, dbsr_bebody; sd t1, 0(t0); la t0, aer_be_len; la t1, dbsr_belen; ld t1, 0(t1); sd t1, 0(t0)\n" ++
  -- 8uld3.2.3.3.1 Fix3: reload s0/s3 clobbered by the derives' dispatcher runs (see save above).
  -- fhsxz.2.4.2.66: RE-DERIVE s0/s3 instead of reloading c1_saved_s0/s3. The system-call
  -- derives above run the predeploy through the dispatcher; when the (modified) predeploy
  -- runs OUT OF GAS / reaches the gas limit (eip7002/eip7251 system_contract_errors fixtures)
  -- its EVM execution writes far enough into memory to CLOBBER the c1_saved_s0/s3 data globals
  -- with 0xb6, so reloading them gave a poison s0 (0xb6b6..) -> bgv_u32le OOB read at the next
  -- line -> ERROR(exit) guest crash. (revert/throw short-circuit before reaching those globals,
  -- hence they passed.) s0 is the fixed SSZ_BASE constant (= 0x40000012, set at fn entry) and
  -- s3 = u32le(s0+56) = execution_requests offset re-read from the STABLE input region -- the
  -- same derivation as the original (fn-entry `li s0` + line ~423). Robust against the clobber.
  "  li s0, 0x40000000\n" ++
  "  addi s0, s0, 18\n" ++
  "  addi a0, s0, 56; jal ra, bgv_u32le; mv s3, a0\n" ++
  "  addi t0, s0, 16; add t0, t0, s3; la t1, c1_er_input; sd t0, 0(t1)\n" ++
  -- For no-tx blocks, execution-derived deposits are necessarily empty: no transaction
  -- can call the deposit contract or emit a deposit log. Use the empty derived body in
  -- the header rebuild so a forged SSZ deposits body mismatches requests_hash through
  -- the general requests_hash failure path. Tx-bearing paths keep the existing SSZ
  -- deposit prelude until the receipt tail derives deposits from materialized logs.
  "  la t0, svf_tx_count; ld t0, 0(t0); beqz t0, .Lv2_er_empty_deposits\n" ++
  -- The v0.6.2 container has five u32 offsets (fixed part = 20 bytes).
  -- Use the first two offsets for the deposit body; the old four-field
  -- extraction (`input + 12`, `off1 - 12`) leaves an 8-byte phantom body
  -- when deposits are empty and makes execution_requests_hash reject every
  -- transaction-bearing builder fixture with bv_fail=24.
  "  addi t1, s0, 16; add t1, t1, s3; mv s2, t1; mv a0, t1; jal ra, bgv_u32le; mv t2, a0\n" ++
  "  addi a0, s2, 4; jal ra, bgv_u32le; sub a1, a0, t2; add a0, s2, t2\n" ++
  "  j .Lv2_er_deposits_ready\n" ++
  ".Lv2_er_empty_deposits:\n" ++
  "  la a0, c1_dbody; li a1, 0\n" ++
  "  la t0, c1_dlen; sd zero, 0(t0)\n" ++
  "  la t0, c1_dstatus; sd zero, 0(t0)\n" ++
  "  la t0, c1_notx_deposit_body_len; sd zero, 0(t0)\n" ++
  ".Lv2_er_deposits_ready:\n" ++
  "  la t0, dbsr_wbody; mv a2, t0; la t0, dbsr_wlen; ld a3, 0(t0)\n" ++
  "  la t0, dbsr_cbody; mv a4, t0; la t0, dbsr_clen; ld a5, 0(t0)\n" ++
  "  mv t0, a1; add t0, t0, a3; add t0, t0, a5; la t1, dbsr_bdlen; ld t1, 0(t1); add t0, t0, t1; la t1, dbsr_belen; ld t1, 0(t1); add t0, t0, t1; addi t0, t0, 20\n" ++
  "  li t1, " ++ toString bvMaxExecutionRequestSectionBytes ++ "; bgtu t0, t1, .Lv2_requests_hash_fail\n" ++
  "  la a6, c1_er_assembled\n" ++
  "  jal ra, assemble_execution_requests\n" ++
  "  la t0, c1_er_assembled_len; sd a0, 0(t0)\n" ++
  "  mv a1, a0; la a0, c1_er_assembled; la a2, erh_requests_hash\n" ++
  "  jal ra, execution_requests_hash\n" ++
  "  la t0, c1_erh_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
  "  mv a0, s0; la a1, svf_bal_hash\n" ++
  "  jal ra, block_access_list_hash\n" ++
  "  bnez a0, .Lv2_bal_hash_fail\n" ++
  "  # General transaction and withdrawal trie roots have already been computed above.\n" ++
  "  la t1, sv_params\n" ++
  -- System-call dispatch may overwrite the svf_* scratch globals.  Re-derive
  -- the payload pointer from the stable SSZ input before handing the frame to
  -- block_verdict; the NPR payload offset is the first u32 at NPR+0.
  "  addi a0, s0, 16; jal ra, bgv_u32le; add t0, s0, a0; addi t0, t0, 16; la t2, svf_payload; sd t0, 0(t2); la t1, sv_params; sd t0, 0(t1)\n" ++
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
  ".Lv2_witness_codes_index_fail:\n" ++
  "  li t0, 25; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
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

end EvmAsm.Codegen
