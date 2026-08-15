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
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptDeleteAcc
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Stateless.MemoryLayout
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.AccountFieldGetters
import EvmAsm.Codegen.Programs.BalCodePreimages
import EvmAsm.Codegen.Programs.BalAccountAccessDescriptors
import EvmAsm.Codegen.Programs.BalStorageAccessDescriptors
import EvmAsm.Codegen.Programs.BlockRlpSize
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.Address
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
import EvmAsm.Codegen.Programs.SimpleTransferRecipient
import EvmAsm.Codegen.Programs.SimpleTransferFeeRecipient
import EvmAsm.Codegen.Programs.BlockVerdictChainConfig
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictDataSection
import EvmAsm.Codegen.Programs.BlockVerdictRuntimePayload

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_state_root_pre_accounts -- pre-MTx pointer stash only.

    #11833 / #11797 M1: no longer locates or counts the supplied BAL body.
    Spec (`fork.py`) has no pre-body BAL-presence test; the built BAL is hashed
    after `apply_body`. The old `bal_section_info` fill existed only to feed
    guest-invented `bv_fail 4` (`.Lbv_no_bal_for_tx`). Keep this prefix narrow:
    stash root/wit/ssz pointers + witness-cap check.
    #11838 M6: dropped dead bsr_bal_count zero + bsr_exec_p write (no readers). -/
def blockStateRootPreAccountsFunction : String :=
  "block_state_root_pre_accounts:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  la t0, bsr_root_p; sd a0, 0(t0)\n" ++
  "  la t0, bsr_wit_p; sd a1, 0(t0)\n" ++
  "  la t0, bsr_wl_v; sd a2, 0(t0)\n" ++
  "  la t0, bsr_wds_p; sd a3, 0(t0)\n" ++
  "  la t0, bsr_wds_n; sd a4, 0(t0)\n" ++
  "  la t0, bsr_ssz_p; sd a6, 0(t0)\n" ++
  "  la t0, bsr_fail_code; sd zero, 0(t0)\n" ++
  "  la t0, bsr_storage_from_map; sd zero, 0(t0)\n" ++
  "  li t1, " ++ toString bsrMaxWitnessBytes ++ "; bgtu a2, t1, .Lbsr_pre_cons_cap\n" ++
  "  la t0, bsr_changed_account_count; sd zero, 0(t0)\n" ++
  ".Lbsr_pre_ok:\n" ++
  "  li a0, 0; j .Lbsr_pre_ret\n" ++
  ".Lbsr_pre_cons_cap:\n  li t0, 101; j .Lbsr_pre_cons_set\n" ++
  ".Lbsr_pre_cons_set:\n" ++
  "  la t1, bsr_fail_code; sd t0, 0(t1); li a0, 1\n" ++
  ".Lbsr_pre_ret:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16; ret\n"

/-! ## execution_map_state_changes -- Step 1 of the #10651 authority switch

    Enumerate the union of the execution `account_writes` and
    `storage_writes` maps. BAL account rows remain a cross-check, but they no
    longer define the candidate set: every map-only address is visited and
    receives a descriptor. Account-map rows also provide the post-account
    fields needed by those map-only descriptors; this keeps the enumeration
    and value authority coherent in one switch. A pre-seeded modeled owner is
    promoted in place when its account-map row appears, so the map post is
    applied after the modeled system post without duplicating the owner entry.

    a0 = descriptor-count pointer
    a1/a2 = legacy BAL-derived account-address table (ignored after the
      authority switch; retained in the ABI for the caller)
    a0 (output) = 0 on success / 1 on malformed map or witness replay. -/
def executionMapStateChangesFunction : String :=
  "execution_map_state_changes:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  la t0, bsr_map_item; li t1, 0xda; sb t1, 0(t0); li t1, 0x94; sb t1, 1(t0); li t1, 0xc0; sb t1, 22(t0); sb t1, 23(t0); sb t1, 24(t0); sb t1, 25(t0); sb t1, 26(t0)\n" ++
  "  mv s0, a0                   # descriptor count pointer\n" ++
  "  mv s1, a1                   # legacy BAL address table (unused)\n" ++
  "  mv s2, a2                   # legacy BAL address count (unused)\n" ++
  -- GH #11431: system 2935/4788 posts are ordinary map owners (no pre-seed).
  "  la t0, bsr_emitted_owner_count; sd zero, 0(t0)\n" ++
  "  la t0, account_writes_count; ld s9, 0(t0); li s4, 0; li s5, " ++ toString EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat ++ "; li s6, 0\n" ++
  "  j .Lem_account_loop\n" ++
  ".Lem_owner_seen:\n" ++
  "  la t0, bsr_emitted_owner_count; ld t1, 0(t0); li t2, 0\n" ++
  ".Lem_owner_seen_loop:\n" ++
  "  bgeu t2, t1, .Lem_owner_not_seen\n" ++
  "  slli t3, t2, 5; la t4, bsr_emitted_owners; add t4, t4, t3; mv t3, t4; la t5, bsr_map_item; addi t5, t5, 2; li t6, 20\n" ++
  ".Lem_owner_seen_cmp:\n" ++
  "  beqz t6, .Lem_owner_seen_yes\n" ++
  "  lbu a1, 0(t4); lbu a2, 0(t5); bne a1, a2, .Lem_owner_seen_next\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lem_owner_seen_cmp\n" ++
  ".Lem_owner_seen_next:\n" ++
  "  addi t2, t2, 1; j .Lem_owner_seen_loop\n" ++
  ".Lem_owner_seen_yes:\n" ++
  "  lbu a0, 20(t3); ret\n" ++
  ".Lem_owner_not_seen:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lem_owner_promote_account:\n" ++
  "  la t0, bsr_emitted_owner_count; ld t1, 0(t0); li t2, 0\n" ++
  ".Lem_owner_promote_loop:\n" ++
  "  bgeu t2, t1, .Lem_owner_promote_miss\n" ++
  "  slli t3, t2, 5; la t4, bsr_emitted_owners; add t3, t4, t3; mv t4, t3; la t5, bsr_map_item; addi t5, t5, 2; li t6, 20\n" ++
  ".Lem_owner_promote_cmp:\n" ++
  "  beqz t6, .Lem_owner_promote_hit\n" ++
  "  lbu a1, 0(t4); lbu a2, 0(t5); bne a1, a2, .Lem_owner_promote_next\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lem_owner_promote_cmp\n" ++
  ".Lem_owner_promote_next:\n" ++
  "  addi t2, t2, 1; j .Lem_owner_promote_loop\n" ++
  ".Lem_owner_promote_hit:\n" ++
  "  li t0, 2; sb t0, 20(t3); li a0, 0; ret\n" ++
  ".Lem_owner_promote_miss:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lem_emit_owner:\n" ++
  "  mv t6, a0; la t0, bsr_emitted_owner_count; ld t1, 0(t0); li t2, " ++ toString bsrMapOwnerCapacity ++ "; bgeu t1, t2, .Lem_owner_capacity_fail\n" ++
  "  slli t2, t1, 5; la t3, bsr_emitted_owners; add t3, t3, t2; la t4, bsr_map_item; addi t4, t4, 2; li t5, 20\n" ++
  ".Lem_emit_owner_copy:\n" ++
  "  beqz t5, .Lem_emit_owner_done\n" ++
  "  lbu t2, 0(t4); sb t2, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .Lem_emit_owner_copy\n" ++
  ".Lem_emit_owner_done:\n" ++
  "  addi t3, t3, -20; sb t6, 20(t3); addi t1, t1, 1; sd t1, 0(t0); ret\n" ++
  ".Lem_account_loop:\n" ++
  "  bgeu s4, s9, .Lem_storage_init\n" ++
  "  slli t0, s4, 7; add s3, s5, t0\n" ++
  "  la t0, bsr_map_item; addi t0, t0, 2; mv t1, s3; li t2, 20\n" ++
  ".Lem_account_addr_copy:\n" ++
  "  beqz t2, .Lem_account_seen_check\n" ++
  "  lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t2, t2, -1; j .Lem_account_addr_copy\n" ++
  ".Lem_account_seen_check:\n" ++
  "  jal ra, .Lem_owner_seen; beqz a0, .Lem_account_process\n" ++
  "  li t0, 1; bne a0, t0, .Lem_account_next\n" ++
  "  jal ra, .Lem_owner_promote_account; bnez a0, .Lem_owner_capacity_fail\n" ++
  ".Lem_account_process_seeded:\n" ++
  "  li s6, 2; li t0, 1; la t1, bsr_account_from_map; sd t0, 0(t1); la t1, bsr_account_row; sd s3, 0(t1); la t1, bsr_storage_from_map; sd t0, 0(t1); j .Lem_process_address\n" ++
  ".Lem_account_process:\n" ++
  "  li s6, 2; li t0, 1; la t1, bsr_account_from_map; sd t0, 0(t1); la t1, bsr_account_row; sd s3, 0(t1); la t1, bsr_storage_from_map; sd t0, 0(t1); li a0, 2; jal ra, .Lem_emit_owner; j .Lem_process_address\n" ++
  ".Lem_storage_init:\n" ++
  "  la t0, storage_writes_count; ld s9, 0(t0); li s4, 0; li s5, " ++ toString storageWritesBlockBase ++ "; li s6, 1\n" ++
  ".Lem_storage_loop:\n" ++
  "  bgeu s4, s9, .Lem_done\n" ++
  "  slli t0, s4, 7; add s3, s5, t0\n" ++
  -- `storage_writes` retains the transaction-start baseline in the spare
  -- 32-byte field at +96.  Match `bal_emit_storage_changes`: unchanged
  -- writes are execution facts, but are not BAL storage changes.
  "  ld t0, 64(s3); ld t1, 96(s3); bne t0, t1, .Lem_storage_delta\n" ++
  "  ld t0, 72(s3); ld t1, 104(s3); bne t0, t1, .Lem_storage_delta\n" ++
  "  ld t0, 80(s3); ld t1, 112(s3); bne t0, t1, .Lem_storage_delta\n" ++
  "  ld t0, 88(s3); ld t1, 120(s3); beq t0, t1, .Lem_storage_next\n" ++
  ".Lem_storage_delta:\n" ++
  "  la t0, bsr_map_item; addi t0, t0, 2; addi t1, s3, 19; li t2, 20\n" ++
  ".Lem_storage_addr_copy:\n" ++
  "  beqz t2, .Lem_storage_seen_check\n" ++
  "  lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; j .Lem_storage_addr_copy\n" ++
  ".Lem_storage_seen_check:\n" ++
  "  jal ra, .Lem_owner_seen; bnez a0, .Lem_storage_next\n" ++
  ".Lem_storage_process:\n" ++
  "  li s6, 1; li t0, 1; la t1, bsr_storage_from_map; sd t0, 0(t1); la t0, bsr_account_from_map; sd zero, 0(t0); la t0, bsr_account_row; sd zero, 0(t0); li a0, 3; jal ra, .Lem_emit_owner\n" ++
  ".Lem_process_address:\n" ++
  "  ld t0, 0(s0); li t1, " ++ toString bsrMaxStateChanges ++ "; bgeu t0, t1, .Lem_fail\n" ++
  "  la a0, bsr_map_item; li a1, 27; la a2, bsr_map_path; jal ra, bal_account_path\n" ++
  "  bnez a0, .Lem_fail\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0); la a3, bsr_map_path; li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk; mv s8, a0; beqz a0, .Lem_pre_found; li t0, 1; bne a0, t0, .Lem_fail\n" ++
  "  la s7, bsr_empty_account; li s10, 70; j .Lem_pre_ready\n" ++
  ".Lem_pre_found:\n" ++
  "  la s7, bsr_acct; la t0, bsr_acct_len; ld s10, 0(t0)\n" ++
  ".Lem_pre_ready:\n" ++
  -- Present-None tombstone (`optionalState@72=0` with STATE valid) AND
  -- EIP-161 empty (bal=0, nonce=0, no code): spec `destroy_account` →
  -- absence in the account trie, NOT an empty-account RLP leaf.
  -- map_account_apply_post_fields has no delete arm and would emit
  -- f8448080…; on 01114 CREATE+SD that left chg mode=0 vlen=70 for the
  -- destroyed CREATE addr → state-root mismatch (bv_fail=1).
  -- Require EIP-161 empty: multi-tx CREATE2 collision (11619) can leave a
  -- stale opt=0 after a later balance/code overlay that never re-stamped
  -- STATE=Some; deleting those wrongly P→F'd a passing fixture. Fall
  -- through to the field overlay when the row is non-empty.
  -- Pre absent → already gone (skip).  Pre present → MPT DELETE (mode=2).
  "  la t0, bsr_account_from_map; ld t0, 0(t0); beqz t0, .Lem_pre_build\n" ++
  "  la t1, bsr_account_row; ld t1, 0(t1); beqz t1, .Lem_pre_build\n" ++
  "  ld t2, 112(t1); andi t2, t2, 8; beqz t2, .Lem_pre_build\n" ++
  "  ld t2, 72(t1); bnez t2, .Lem_pre_build\n" ++
  "  ld t2, 32(t1); ld t3, 40(t1); or t2, t2, t3; ld t3, 48(t1); or t2, t2, t3; ld t3, 56(t1); or t2, t2, t3; bnez t2, .Lem_pre_build\n" ++
  "  ld t2, 64(t1); bnez t2, .Lem_pre_build\n" ++
  "  ld t2, 88(t1); bnez t2, .Lem_pre_build\n" ++
  "  bnez s8, .Lem_map_value_unchanged\n" ++
  "  li s8, 2; la t0, bsr_tmplen; sd zero, 0(t0); j .Lem_map_value_changed\n" ++
  ".Lem_pre_build:\n" ++
  "  ld t0, 0(s0); slli t1, t0, 6; la t2, basr_paths; add a4, t2, t1; slli t1, t0, 8; la t2, basr_values; add a5, t2, t1\n" ++
  "  la t1, bsr_prev_acct; sd s7, 0(t1); la t1, bsr_acct_len; sd s10, 0(t1); la t1, bsr_prev_desc; sd a5, 0(t1)\n" ++
  "  mv a0, s7; mv a1, s10; la a2, bsr_map_item; li a3, 27; la a6, bsr_tmplen; jal ra, map_account_change_value\n" ++
  "  bnez a0, .Lem_fail\n" ++
  "  # Map rows are execution facts too; retain only complete account-leaf mutations.\n" ++
  "  # Compare the complete pre/post RLP values, covering nonce, balance,\n" ++
  "  # storage root, and code hash without making long-list decoding a hard gate.\n" ++
  "  la t0, bsr_acct_len; ld t1, 0(t0); la t0, bsr_tmplen; ld t2, 0(t0); bne t1, t2, .Lem_map_value_changed\n" ++
  "  la t0, bsr_prev_acct; ld t1, 0(t0); la t0, bsr_prev_desc; ld t2, 0(t0); la t0, bsr_acct_len; ld t3, 0(t0)\n" ++
  ".Lem_map_value_compare:\n" ++
  "  beqz t3, .Lem_map_value_unchanged\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lem_map_value_changed\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lem_map_value_compare\n" ++
  ".Lem_map_value_changed:\n" ++
  "  # BAL may have already emitted this owner.  Replace that one record with\n" ++
  "  # the grouped map post-value instead of appending a second descriptor.\n" ++
  "  ld t0, 0(s0); li t6, 0\n" ++
  ".Lem_map_existing_scan:\n" ++
  "  bgeu t6, t0, .Lem_map_append\n" ++
  "  slli t1, t6, 5; slli t2, t6, 3; add t1, t1, t2; la t2, bsr_changes; add t1, t2, t1\n" ++
  "  ld t3, 0(t1); la t4, bsr_map_path; li t5, 64\n" ++
  ".Lem_map_existing_cmp:\n" ++
  "  beqz t5, .Lem_map_existing_found\n" ++
  "  lbu a0, 0(t3); lbu a1, 0(t4); bne a0, a1, .Lem_map_existing_next\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lem_map_existing_cmp\n" ++
  ".Lem_map_existing_next:\n" ++
  "  addi t6, t6, 1; j .Lem_map_existing_scan\n" ++
  ".Lem_map_existing_found:\n" ++
  "  # Keep the existing stable path and value slot.  The freshly computed\n" ++
  "  # map value is in the next free scratch slot; copy it over the BAL value\n" ++
  "  # so repeated replacements do not alias one another.\n" ++
  "  la t2, bsr_prev_desc; sd t1, 0(t2); ld a0, 16(t1); slli t2, t0, 8; la t3, basr_values; add a1, t3, t2; la t2, bsr_tmplen; ld a2, 0(t2)\n" ++
  "  jal ra, mset_memcpy; la t1, bsr_prev_desc; ld t1, 0(t1); la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1); sd s8, 32(t1)\n" ++
  "  j .Lem_map_value_done\n" ++
  ".Lem_map_append:\n" ++
  "  slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, bsr_changes; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, basr_paths; add t2, t3, t2; mv t3, t2; la t4, bsr_map_path; li t5, 64\n" ++
  ".Lem_map_path_copy:\n" ++
  "  beqz t5, .Lem_map_path_copied\n" ++
  "  lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .Lem_map_path_copy\n" ++
  ".Lem_map_path_copied:\n" ++
  "  sd t2, 0(t1); li t2, 64; sd t2, 8(t1)\n" ++
  "  slli t2, t0, 8; la t3, basr_values; add t2, t3, t2; sd t2, 16(t1); la t3, bsr_tmplen; ld t3, 0(t3); sd t3, 24(t1); sd s8, 32(t1)\n" ++
  "  addi t0, t0, 1; sd t0, 0(s0)\n" ++
  "  j .Lem_map_value_done\n" ++
  ".Lem_map_value_unchanged:\n" ++
  "  li t0, 2; bgeu s6, t0, .Lem_account_next\n" ++
  "  j .Lem_storage_next\n" ++
  ".Lem_map_value_done:\n" ++
  "  li t0, 2; bgeu s6, t0, .Lem_account_next\n" ++
  ".Lem_storage_next:\n" ++
  "  addi s4, s4, 1; j .Lem_storage_loop\n" ++
  ".Lem_account_next:\n" ++
  "  addi s4, s4, 1; j .Lem_account_loop\n" ++
  ".Lem_fail:\n" ++
  "  li a0, 1; j .Lem_ret\n" ++
  ".Lem_owner_capacity_fail:\n" ++
  "  # Owner-set overflow is fail-closed and distinct from ordinary map/path failures.\n" ++
  "  li t0, 126; la t1, bsr_fail_code; sd t0, 0(t1); li a0, 1; j .Lem_ret\n" ++
  ".Lem_done:\n" ++
  "  li a0, 0\n" ++
  ".Lem_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp); addi sp, sp, 112; ret\n"

/-! ## block_state_root -- post-state root after system writes + withdrawals.
    a0 = pre-state root ptr   a1 = witness   a2 = witness_len
    a3 = wds descriptors   a4 = n_wds   a5 = out_root   a6 = SSZ_BASE
    a0 (output) = 0 ok / 1 conservative (any miss / unsupported case).

    #11836 / #11797 M4: no longer locates or capacity-checks the supplied BAL
    body here. Spec builds+hashes BAL after apply_body; map is sole root
    authority. Witness globals for `account_apply_storage` are always set. -/
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
  -- EIP-2935/4788 already ran at block start via
  -- process_block_start_system_transactions. Map is sole authority; no formula
  -- descriptors or synthetic modeled-system rows are consumed here.
  "  la t0, evm_oldest_ancestor_offset; ld t1, 0(t0); bnez t1, .Lbsr_oao_2935_done\n" ++
  "  li t1, 1; sd t1, 0(t0)\n" ++
  ".Lbsr_oao_2935_done:\n" ++
  "  li s1, 0                     # change counter (map is sole authority)\n" ++
  "  la t0, bsr_changed_account_count; sd zero, 0(t0)\n" ++
  -- #11836 M4: drop supplied BAL section_info + count/gas/cap gates.
  -- #11838 M6: drop redundant bsr_bal_count zero (BSS 0; dump-only cell).
  -- Always wire witness globals for later account_apply_storage (map path).
  "  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)\n" ++
  "  # execution_map_state_changes is the SOLE root authority for user-tx account\n" ++
  "  # leaves (plus true execution system/withdrawal effects). s1 is 0 here unless\n" ++
  "  # a prior path left residues.\n" ++
  "  la t0, bsr_change_count; sd s1, 0(t0); mv a0, t0; la a1, bsr_changed_accounts; la t0, bsr_changed_account_count; ld a2, 0(t0)\n" ++
  "  jal ra, execution_map_state_changes; bnez a0, .Lbsr_cons_map\n" ++
  "  la t0, bsr_change_count; ld s1, 0(t0)\n" ++
  "  # NORMALIZATION BOUNDARY: bsr_changes contains committed, value-bearing\n" ++
  "  # mutations from the execution maps (and modeled system/withdrawals).\n" ++
  "  # Runtime account/storage access outcomes are mode=3 no-ops: they provide\n" ++
  "  # access evidence but never a state-root value, so do not materialize them\n" ++
  "  # in this C-sized builder input. In particular, reverted storage windows\n" ++
  "  # have zero committed entries and cannot become a last-write-wins value.\n" ++
  ".Lbsr_withdrawals:\n" ++
  "  # The map authority records addresses already owned by either execution map.\n" ++
  "  # Match the address, not the account-map flag: a storage-only owner can\n" ++
  "  # still have the recipient's final balance in the committed BAL record,\n" ++
  "  # and flagging it as a miss would append a duplicate withdrawal change.\n" ++
  "  # BAL count is only an execution statistic and is not a sound proxy here.\n" ++
  "  # withdrawal changes: change counter s1 starts after system/BAL changes.\n" ++
  "  # Zero-amount withdrawals are no-ops and do not advance the change counter.\n" ++
  "  li s0, 0                     # withdrawal index\n" ++
  ".Lbsr_wl:\n" ++
  "  beq s0, s4, .Lbsr_apply\n" ++
  "  slli t0, s0, 4; add t0, s3, t0; ld a0, 0(t0); ld a1, 8(t0)   # wd[i] rlp ptr/len\n" ++
  "  # s1 is the next committed record slot, including system/BAL/map changes.\n" ++
  "  slli t1, s1, 6; la t2, bsr_paths; add a2, t2, t1; la a3, bsr_delta\n" ++
  "  jal ra, withdrawal_to_path_delta; bnez a0, .Lbsr_cons_wd_decode\n" ++
  "  # zero-amount withdrawal (delta == 0) -> no state change -> skip.\n" ++
  "  la t0, bsr_delta; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2\n" ++
  "  ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbsr_wl_next\n" ++
  "  la t0, bsr_emitted_owner_count; ld t1, 0(t0); li t2, 0\n" ++
  ".Lbsr_wd_map_scan:\n" ++
  "  bgeu t2, t1, .Lbsr_wd_map_miss\n" ++
  "  # Every emitted owner participates, including flag==0 storage-only rows.\n" ++
  "  slli t3, t2, 5; la t4, bsr_emitted_owners; add t3, t4, t3\n" ++
  "  mv t4, t3; la t5, wtpd_struct; addi t5, t5, 16; li t6, 20\n" ++
  ".Lbsr_wd_map_cmp:\n" ++
  "  beqz t6, .Lbsr_wd_map_hit\n" ++
  "  lbu a1, 0(t4); lbu a2, 0(t5); bne a1, a2, .Lbsr_wd_map_next\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lbsr_wd_map_cmp\n" ++
  ".Lbsr_wd_map_next:\n" ++
  "  addi t2, t2, 1; j .Lbsr_wd_map_scan\n" ++
  ".Lbsr_wd_map_hit:\n" ++
  "  j .Lbsr_wl_next\n" ++
  ".Lbsr_wd_map_miss:\n" ++
  "  li t0, " ++ toString bsrMaxWithdrawalChanges ++ "; bgeu s0, t0, .Lbsr_cons_change_cap\n" ++
  "  # Repeated withdrawals to the same recipient accumulate into one state change.\n" ++
  "  li t6, 0                     # compose with every earlier committed mutation [0, s1)\n" ++
  ".Lbsr_dup_scan:\n" ++
  "  beq t6, s1, .Lbsr_no_dup\n" ++
  "  slli t0, t6, 5; slli t1, t6, 3; add t0, t0, t1; la t1, bsr_changes; add t0, t1, t0\n" ++
  "  ld t0, 0(t0)                  # prev path from descriptor (bsr_paths or basr_paths)\n" ++
  "  slli t2, s1, 6; la t1, bsr_paths; add t1, t1, t2 # current withdrawal path\n" ++
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
  "  slli t1, s1, 6; la t2, bsr_paths; add a3, t2, t1; li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbsr_wl_found\n" ++
  "  li t0, 1; bne a0, t0, .Lbsr_cons_wd_walk   # parse-fail (2) -> conservative\n" ++
  "  # NOT-FOUND: create the account. fresh = empty_account + delta (balance 0 -> delta).\n" ++
  "  la a0, bsr_empty_account; li a1, 70; la a2, bsr_delta\n" ++
  "  slli t1, s1, 7; la t2, bsr_newaccts; add a3, t2, t1; la a4, bsr_tmplen\n" ++
  "  jal ra, account_add_balance; bnez a0, .Lbsr_cons_new_add\n" ++
  "  li t5, 1; j .Lbsr_wl_record   # is_insert = 1\n" ++
  ".Lbsr_wl_found:\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); la a2, bsr_delta\n" ++
  "  slli t1, s1, 7; la t2, bsr_newaccts; add a3, t2, t1; la a4, bsr_tmplen\n" ++
  "  jal ra, account_add_balance; bnez a0, .Lbsr_cons_found_add\n" ++
  "  li t5, 0                      # is_insert = 0 (MODIFY existing)\n" ++
  ".Lbsr_wl_record:\n" ++
  "  slli t0, s1, 5; slli t6, s1, 3; add t0, t0, t6; la t1, bsr_changes; add t1, t1, t0   # *40\n" ++
  "  slli t2, s1, 6; la t3, bsr_paths; add t3, t3, t2; sd t3, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  slli t2, s1, 7; la t3, bsr_newaccts; add t3, t3, t2; sd t3, 16(t1)\n" ++
  "  la t3, bsr_tmplen; ld t3, 0(t3); sd t3, 24(t1)\n" ++
  "  sd t5, 32(t1)               # is_insert\n" ++
  "  addi s1, s1, 1               # advance change counter (only on a recorded change)\n" ++
  ".Lbsr_wl_next:\n" ++
  "  addi s0, s0, 1; j .Lbsr_wl\n" ++
  ".Lbsr_apply:\n" ++
  "  la t0, bsr_change_count; sd s1, 0(t0)\n" ++
  "  # Committed state changes must have pairwise-distinct canonical trie paths.\n" ++
  "  # Keep this check in the guest: a dedup guard that is never executable is\n" ++
  "  # not evidence that the authority switch preserves the MPT precondition.\n" ++
  "  li t0, 0\n" ++
  ".Lbsr_path_i:\n" ++
  "  bgeu t0, s1, .Lbsr_path_unique\n" ++
  "  slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, bsr_changes; add t1, t2, t1\n" ++
  "  ld t3, 0(t1); ld t4, 8(t1); li t5, " ++ toString bsrPathBytes ++ "; bgtu t4, t5, .Lbsr_cons_duplicate_path\n" ++
  "  addi t6, t0, 1\n" ++
  ".Lbsr_path_j:\n" ++
  "  bgeu t6, s1, .Lbsr_path_i_next\n" ++
  "  slli a0, t6, 5; slli a1, t6, 3; add a0, a0, a1; la a1, bsr_changes; add a0, a1, a0\n" ++
  "  ld a1, 0(a0); ld a2, 8(a0); li a3, " ++ toString bsrPathBytes ++ "; bgtu a2, a3, .Lbsr_cons_duplicate_path\n" ++
  "  bne t4, a2, .Lbsr_path_j_next\n" ++
  "  mv a2, t3; mv a3, a1; mv a4, t4\n" ++
  ".Lbsr_path_bytes:\n" ++
  "  beqz a4, .Lbsr_cons_duplicate_path\n" ++
  "  lbu a5, 0(a2); lbu a6, 0(a3); bne a5, a6, .Lbsr_path_j_next\n" ++
  "  addi a2, a2, 1; addi a3, a3, 1; addi a4, a4, -1; j .Lbsr_path_bytes\n" ++
  ".Lbsr_path_j_next:\n" ++
  "  addi t6, t6, 1; j .Lbsr_path_j\n" ++
  ".Lbsr_path_i_next:\n" ++
  "  addi t0, t0, 1; j .Lbsr_path_i\n" ++
  ".Lbsr_path_unique:\n" ++
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
  -- #11836: `.Lbsr_cons_bal_section` / bsr_fail 110 retired with the supplied
  -- BAL section_info gate.
  ".Lbsr_cons_change_cap:\n" ++
  "  li t0, 111; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
  ".Lbsr_cons_map:\n" ++
  "  la t1, bsr_fail_code; ld t2, 0(t1); bnez t2, .Lbsr_cons; li t0, 116; sd t0, 0(t1); j .Lbsr_cons\n" ++
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
  ".Lbsr_cons_duplicate_path:\n" ++
  "  li t0, 125; la t1, bsr_fail_code; sd t0, 0(t1); j .Lbsr_cons\n" ++
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
  "  # ExecutionWitness.codes is SSZ List[ByteList[65536]].  The generic\n" ++
  "  # code index checks the offset table, then records each element length.\n" ++
  "  # Enforce the SSZ envelope before any code-hash lookup can consume it.\n" ++
  "  la t0, wcidx_count; ld t0, 0(t0); la t1, wcidx_records; li t2, 65536\n" ++
  ".Lv2_code_cap_loop:\n" ++
  "  beqz t0, .Lv2_code_cap_ok\n" ++
  "  ld t3, 40(t1); bgtu t3, t2, .Lv2_codes_cap_fail\n" ++
  "  addi t1, t1, 48; addi t0, t0, -1; j .Lv2_code_cap_loop\n" ++
  ".Lv2_code_cap_ok:\n" ++
  "  la t1, svf_witness_section; ld t0, 0(t1); addi a0, t0, 8; jal ra, bgv_u32le # headers offset\n" ++
  "  mv t6, a0\n" ++
  "  la t1, svf_witness_section; ld t0, 0(t1); add t2, t0, t6\n" ++
  "  la t3, svf_headers_ptr; sd t2, 0(t3)\n" ++
  "  la t1, svf_witness_end; ld t1, 0(t1); bltu t1, t2, .Lv2_headers_bounds_fail\n" ++
  "  sub a1, t1, t2; la t3, svf_headers_len; sd a1, 0(t3)\n" ++
  "  # ExecutionWitness.headers is SSZ List[ByteList[1024]].  Validate the\n" ++
  "  # offset table and each element length before header parsing or keccak.\n" ++
  "  mv s1, t2; mv s2, a1; beqz s2, .Lv2_header_cap_ok\n" ++
  "  li t0, 4; bltu s2, t0, .Lv2_headers_cap_fail\n" ++
  "  mv a0, s1; jal ra, bgv_u32le; mv s3, a0\n" ++
  "  andi t0, s3, 3; bnez t0, .Lv2_headers_cap_fail\n" ++
  "  bgtu s3, s2, .Lv2_headers_cap_fail; srli s3, s3, 2\n" ++
  "  li t0, 256; bgtu s3, t0, .Lv2_headers_cap_fail\n" ++
  "  li s4, 0\n" ++
  ".Lv2_header_cap_loop:\n" ++
  "  beq s4, s3, .Lv2_header_cap_ok\n" ++
  "  slli t0, s4, 2; add a0, s1, t0; jal ra, bgv_u32le; mv s5, a0\n" ++
  "  bltu s5, s3, .Lv2_headers_cap_fail; bgtu s5, s2, .Lv2_headers_cap_fail\n" ++
  "  addi t0, s4, 1; beq t0, s3, .Lv2_header_cap_last\n" ++
  "  slli t0, t0, 2; add a0, s1, t0; jal ra, bgv_u32le; j .Lv2_header_cap_end\n" ++
  ".Lv2_header_cap_last:\n" ++
  "  mv a0, s2\n" ++
  ".Lv2_header_cap_end:\n" ++
  "  bltu a0, s5, .Lv2_headers_cap_fail; bgtu a0, s2, .Lv2_headers_cap_fail\n" ++
  "  sub t0, a0, s5; li t1, 1024; bgtu t0, t1, .Lv2_headers_cap_fail\n" ++
  "  addi s4, s4, 1; j .Lv2_header_cap_loop\n" ++
  ".Lv2_header_cap_ok:\n" ++
  "  la t0, svf_headers_ptr; ld a0, 0(t0); la t0, svf_headers_len; ld a1, 0(t0)\n" ++
  "  la a2, svf_headers_count; jal ra, headers_validate_chain\n" ++
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
  -- reject beyond the gas-derived transaction cap (mirrors the transactions
  -- cap below).
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
  "  li t0, " ++ toString (bvMtxFullTxCap + 1) ++ "; bgeu s4, t0, .Lv2_tx_root_fail\n" ++
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
  "  jal ra, mpt_indexed_trie_root_bounded_from_values\n" ++
  "  la t0, bv_tx_root_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lv2_tx_root_fail\n" ++
  "  la a0, svf_descriptors; la t0, svf_wds_count; ld a1, 0(t0); la a2, svf_withdrawals_root\n" ++
  "  jal ra, mpt_indexed_trie_root_bounded_from_values\n" ++
  "  bnez a0, .Lv2_withdrawals_root_fail\n" ++
  "  addi a0, s0, 56; jal ra, bgv_u32le; mv s3, a0     # execution_requests offset\n" ++
  "  addi a0, s0, 4;  jal ra, bgv_u32le; mv s4, a0     # witness offset = NPR end\n" ++
  -- The four checked request calls are a post-user-loop phase. Keep the
  -- implementation below in this closure so the guest has one callable body,
  -- but jump over it on the entry path: the header needs the input
  -- requests_hash before block_verdict, while the derived bodies must not be
  -- produced until the user transaction boundary has completed.
  "  j .Lv2_input_hash\n" ++
  "block_verdict_deferred_system_requests:\n" ++
  "  la t0, dbsr_saved_ra; sd ra, 0(t0)\n" ++
  -- fork.py:917-919: all four checked request calls run at N+1, after the
  -- user transaction loop. The caller also sets this value for the account
  -- postlude; setting it here makes the storage and side-capture producers
  -- share one source of truth at both mutually-exclusive post-loop sites.
  "  la t0, bv_tx_count; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0)\n" ++
  -- 8uld3.2.3.3.1 Fix3 / fhsxz.2.4.2.66: the system-call derives below run runtime_dispatcher_call,
  -- which clobbers ALL s-registers (SystemCallStaging:96-99 — resets sp to lp64_sp_top and the
  -- predeploy EVM execution overwrites the s-regs) AND, on an OUT-OF-GAS predeploy, writes far
  -- enough into memory to clobber guest data globals too. s0(SSZ_BASE)/s3(er offset) are needed
  -- AFTER the derives (deposit extraction, block_access_list_hash,
  -- block_verdict). Saving them to data globals (c1_saved_s0/s3) was unsafe — the OOG predeploy
  -- clobbered those globals with 0xb6 (.66 crash) — so they are RE-DERIVED from the stable input
  -- region after the last derive (see below); no save needed.
  -- 8uld3.2.3.3.1 (C.1): derive the withdrawal(EIP-7002)+consolidation(EIP-7251)
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
  -- GH #11105: `bv_witness_state_ptr` / `_len` read ZERO here. Their only writer is
  -- `block_verdict` (`BlockVerdictFunction.lean`, from `params+80`), and the four request
  -- predeploys below run through the EVM dispatcher BEFORE that has happened -- so every
  -- consumer of those cells reached from an opcode handler sees a null witness.
  --
  -- Measured: `slot_at_header_state_root` called from `h_SLOAD`'s cold path returned status 4
  -- (header parse / state_root size fail) on 16 of 16 calls, because a null witness makes
  -- `witness_lookup_by_hash` yield nothing and the following RLP walk run on a non-list buffer.
  -- With these two stores the same 16 calls return ABSENT (status 1/5) and zero errors.
  --
  -- ⚠️ The source is `svf_witness`, which THIS STAGE ALREADY USES SUCCESSFULLY: its own
  -- `code_at_header_state_root` calls below pass exactly these two globals and resolve the
  -- predeploy code. The witness was always here; the cells the STORAGE path reads were simply
  -- never populated from it.
  "  la t0, svf_witness; ld t1, 0(t0); la t2, bv_witness_state_ptr; sd t1, 0(t2)\n" ++
  "  la t0, svf_witness_len; ld t1, 0(t0); la t2, bv_witness_state_len; sd t1, 0(t2)\n" ++
  "  la t0, evm_env; ld t1, 448(t0); la t2, c1_saved_logcount; sd t1, 0(t2)\n" ++
  -- #11835 / #11797 M3: c1_bal_* no longer filled at v2 entry (and M2 removed
  -- the last deferred consumer). Builder deposit/exit use header+exec only.
  -- == WITHDRAWAL (EIP-7002): code_at -> system call -> copy body ==
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, withdrawal_request_predeploy_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Ldsr_fail\n" ++  -- STATUS_VOCAB: cahsr — # unresolved(6) rejects via bnez
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3\n" ++
  "  la t0, c1_wcode_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_wcode_len; sd t3, 0(t0)\n" ++
  -- GH #11176: do not construct BAL-sourced storage rows before the checked
  -- system call. The callee receives empty preload arguments and resolves
  -- request-queue storage through its authenticated state path.
  ".Lc1_w_derive:\n" ++
  "  la t0, c1_wcode_ptr; ld a0, 0(t0); la t0, c1_wcode_len; ld a1, 0(t0)\n" ++
  "  la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging\n" ++
  "  jal ra, derive_withdrawal_requests\n" ++
  "  bnez a2, .Ldsr_fail\n" ++
  "  la t0, dbsr_wlen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_wbody; mv t3, a1\n" ++
  ".Lc1_w_copy:\n" ++
  "  beqz t3, .Lc1_w_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_w_copy\n" ++
   ".Lc1_w_copyd:\n" ++
   "  jal ra, read_sets_incorporate_tx\n" ++
   "  jal ra, write_sets_incorporate_tx\n" ++
   -- == CONSOLIDATION (EIP-7251) ==

  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, consolidation_request_predeploy_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Ldsr_fail\n" ++  -- STATUS_VOCAB: cahsr — # unresolved(6) rejects via bnez
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3\n" ++
  "  la t0, c1_ccode_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_ccode_len; sd t3, 0(t0)\n" ++
  ".Lc1_c_derive:\n" ++
  "  la t0, c1_ccode_ptr; ld a0, 0(t0); la t0, c1_ccode_len; ld a1, 0(t0)\n" ++
  "  la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging\n" ++
  "  jal ra, derive_consolidation_requests\n" ++
  "  bnez a2, .Ldsr_fail\n" ++
  "  la t0, dbsr_clen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_cbody; mv t3, a1\n" ++
  ".Lc1_c_copy:\n" ++
  "  beqz t3, .Lc1_c_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_c_copy\n" ++
  ".Lc1_c_copyd:\n" ++
   "  jal ra, read_sets_incorporate_tx\n" ++
   "  jal ra, write_sets_incorporate_tx\n" ++
  "  la t0, evm_env; la t2, c1_saved_logcount; ld t1, 0(t2); sd t1, 448(t0)\n" ++
  -- v0.6.0 (EIP-8282/C12): process_checked_system_transaction pre-checks that
  -- each BUILDER predeploy holds code (fork.py:985-1005 via :755-765) and
  -- raises InvalidBlock when it does not -- even though an absent contract's
  -- (empty) output would not change requests_hash. The spec reads through a
  -- TransactionState so a contract deployed EARLIER IN THIS BLOCK counts; the
  -- exec code-effect log carries that same-block case for the guest.
  --
  -- GH #11693 / #12234: split cahsr status classes. Status 1 (absent) is genuine
  -- NO CODE → same-block ladder. `code_read_fetch` returns status 5 when the
  -- code preimage is absent; an authenticated EMPTY_CODE_HASH has no witness
  -- preimage by construction, so compare the account hash before treating
  -- status 5 as CANNOT KNOW. True parse (2) and unresolved (6) fail closed;
  -- only a non-empty missing preimage (and status 3/4) also reaches `.Ldsr_fail`.
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_deposit_contract_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  -- STATUS_VOCAB: cahsr — absent(1) and qualified codeMiss(5) → same-block;
  -- true parse(2) and unresolved(6) → fail (GH #12234 / #12235).
  "  beqz a0, .Lc1_bd_check_len\n" ++
  "  li t0, 1; beq a0, t0, .Lc1_bd_same_block\n" ++
  "  li t0, 2; beq a0, t0, .Ldsr_fail\n" ++
  "  li t0, 6; beq a0, t0, .Ldsr_fail\n" ++
  "  li t0, 5; bne a0, t0, .Ldsr_fail\n" ++
  "  la t0, cahsr_acct_struct; addi t0, t0, 72; la t1, chahsr_empty_code_hash\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  j .Lc1_bd_same_block\n" ++
  ".Lc1_bd_check_len:\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); bnez t0, .Lc1_bd_code_ok\n" ++
   -- M2 (#11834 / #11797): same-block code is header + `exec_code_effect` only.
   -- A supplied-BAL non-empty code final must not steer past InvalidBlock when
   -- neither header nor same-block effect exposes live code (FA-ward #11806).
   ".Lc1_bd_same_block:\n" ++
   "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, builder_deposit_contract_addr\n" ++
   "  jal ra, find_code_effect_by_address\n" ++
   "  beqz a0, .Ldsr_fail\n" ++
   -- A same-block code-effect record lives in exec_code_effect_log, not in
   -- witness.codes.  Rebase its +48 code bytes against svf_codes_ptr so the
   -- existing derive-ready path can consume the same cahsr window for both
   -- authenticated and same-block code.  Without this, the successful gate
   -- leaves cahsr pointing at the previous status-0 lookup.
   "  addi t0, a0, 48; la t1, svf_codes_ptr; ld t1, 0(t1); sub t0, t0, t1; la t1, cahsr_code_offset; sd t0, 0(t1); ld t0, 40(a0); la t1, cahsr_code_length; sd t0, 0(t1)\n" ++
   ".Lc1_bd_code_ok:\n" ++

  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_exit_contract_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  -- STATUS_VOCAB: cahsr — absent(1) and qualified codeMiss(5) → same-block;
  -- true parse(2) and unresolved(6) → fail (GH #12234 / #12235).
  "  beqz a0, .Lc1_be_check_len\n" ++
  "  li t0, 1; beq a0, t0, .Lc1_be_same_block\n" ++
  "  li t0, 2; beq a0, t0, .Ldsr_fail\n" ++
  "  li t0, 6; beq a0, t0, .Ldsr_fail\n" ++
  "  li t0, 5; bne a0, t0, .Ldsr_fail\n" ++
  "  la t0, cahsr_acct_struct; addi t0, t0, 72; la t1, chahsr_empty_code_hash\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  j .Lc1_be_same_block\n" ++
  ".Lc1_be_check_len:\n" ++
  "  la t0, cahsr_code_length; ld t0, 0(t0); bnez t0, .Lc1_be_code_ok\n" ++
   -- M2 (#11834): same-block exit predeploy — header + exec_code_effect only.
   ".Lc1_be_same_block:\n" ++
   "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, builder_exit_contract_addr\n" ++
   "  jal ra, find_code_effect_by_address\n" ++
   "  beqz a0, .Ldsr_fail\n" ++
   "  addi t0, a0, 48; la t1, svf_codes_ptr; ld t1, 0(t1); sub t0, t0, t1; la t1, cahsr_code_offset; sd t0, 0(t1); ld t0, 40(a0); la t1, cahsr_code_length; sd t0, 0(t1)\n" ++
   ".Lc1_be_code_ok:\n" ++

  -- EIP-8282: derive the builder deposit and builder exit request bodies through
  -- the same checked system-call path. Request-queue storage is resolved by the
  -- authenticated state path; empty return data is represented by a zero body
  -- length and is therefore omitted by the five-field assembler.
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, builder_deposit_contract_addr\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  -- STATUS_VOCAB: cahsr — # unresolved(6) rejects via bne≠5; absent(1)/qualified 5 → same-block
  "  beqz a0, .Lc1_bd_derive_fresh\n" ++
  "  li t0, 1; beq a0, t0, .Lc1_bd_derive_same_block\n" ++
  "  li t0, 5; bne a0, t0, .Ldsr_fail\n" ++
  "  la t0, cahsr_acct_struct; la t1, chahsr_empty_code_hash\n" ++
  "  ld t2, 72(t0); ld t3, 0(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 80(t0); ld t3, 8(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 88(t0); ld t3, 16(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 96(t0); ld t3, 24(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  j .Lc1_bd_derive_same_block\n" ++
  ".Lc1_bd_derive_fresh:\n  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Ldsr_fail; j .Lc1_bd_derive_ready\n" ++
  -- Re-run the same-block effect lookup at the derive site.  This call is
  -- separate from the earlier check: code_at_header_state_root writes cahsr
  -- only on status 0, so accepting a nonzero status without refreshing would
  -- execute the stale window left by the prior builder check.
  ".Lc1_bd_derive_same_block:\n" ++
  "  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, builder_deposit_contract_addr; jal ra, find_code_effect_by_address; beqz a0, .Ldsr_fail\n" ++
  "  addi t0, a0, 48; la t1, svf_codes_ptr; ld t1, 0(t1); sub t0, t0, t1; la t1, cahsr_code_offset; sd t0, 0(t1); ld t0, 40(a0); la t1, cahsr_code_length; sd t0, 0(t1)\n" ++
  ".Lc1_bd_derive_ready:\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3; la t0, c1_bd_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_bd_code_len; sd t3, 0(t0)\n" ++
  -- `process_checked_system_transaction` first reads this account through a
  -- throwaway TransactionState, so the earlier code check intentionally remains raw.
  -- `stage_system_call` records the matching real-state read at the actual dispatch
  -- seam below, shared by all four request predeploys.
  ".Lc1_bd_call:\n" ++
  "  la t0, c1_bd_code_ptr; ld a0, 0(t0); la t0, c1_bd_code_len; ld a1, 0(t0); la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging; jal ra, derive_builder_deposit_requests\n" ++
  "  bnez a2, .Ldsr_fail; la t0, dbsr_bdlen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_bdbody; mv t3, a1\n" ++
  ".Lc1_bd_copy:\n  beqz t3, .Lc1_bd_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_bd_copy\n" ++
  ".Lc1_bd_copyd:\n" ++
  -- The checked-system transaction's real state is incorporated after execution in
  -- the spec.  Emit balance/nonce/code effects before merging and clearing the
  -- transaction account map, then merge this synthetic transaction's read and
  -- storage sets before beginning the independent builder-exit transaction.
  "  jal ra, account_writes_emit_builder_tx\n" ++
  "  jal ra, account_writes_incorporate_tx\n" ++
  "  jal ra, read_sets_incorporate_tx\n" ++
  "  jal ra, write_sets_incorporate_tx\n" ++
  -- Builder exit.
  "  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0); la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0); la a2, builder_exit_contract_addr; la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0); jal ra, code_at_header_state_root\n" ++
  -- STATUS_VOCAB: cahsr — # unresolved(6) rejects via bne≠5; absent(1)/qualified 5 → same-block
  "  beqz a0, .Lc1_be_derive_fresh\n" ++
  "  li t0, 1; beq a0, t0, .Lc1_be_derive_same_block\n" ++
  "  li t0, 5; bne a0, t0, .Ldsr_fail\n" ++
  "  la t0, cahsr_acct_struct; la t1, chahsr_empty_code_hash\n" ++
  "  ld t2, 72(t0); ld t3, 0(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 80(t0); ld t3, 8(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 88(t0); ld t3, 16(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  ld t2, 96(t0); ld t3, 24(t1); bne t2, t3, .Ldsr_fail\n" ++
  "  j .Lc1_be_derive_same_block\n" ++
  ".Lc1_be_derive_fresh:\n  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Ldsr_fail; j .Lc1_be_derive_ready\n" ++
  ".Lc1_be_derive_same_block:\n  la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, builder_exit_contract_addr; jal ra, find_code_effect_by_address; beqz a0, .Ldsr_fail\n" ++
  "  addi t0, a0, 48; la t1, svf_codes_ptr; ld t1, 0(t1); sub t0, t0, t1; la t1, cahsr_code_offset; sd t0, 0(t1); ld t0, 40(a0); la t1, cahsr_code_length; sd t0, 0(t1)\n" ++
  ".Lc1_be_derive_ready:\n  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3; la t0, c1_be_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, c1_be_code_len; sd t3, 0(t0)\n" ++
  "  .Lc1_be_call:\n  la t0, c1_be_code_ptr; ld a0, 0(t0); la t0, c1_be_code_len; ld a1, 0(t0); la t0, svf_payload; ld a2, 0(t0); la a3, c1_staging; jal ra, derive_builder_exit_requests\n" ++
  "  bnez a2, .Ldsr_fail; la t0, dbsr_belen; sd a1, 0(t0); mv t1, a0; la t2, dbsr_bebody; mv t3, a1\n" ++
  "  .Lc1_be_copy:\n  beqz t3, .Lc1_be_copyd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lc1_be_copy\n  .Lc1_be_copyd:\n" ++
  "  jal ra, account_writes_emit_builder_tx\n" ++
  "  jal ra, account_writes_incorporate_tx\n" ++
  "  jal ra, read_sets_incorporate_tx\n" ++
  "  jal ra, write_sets_incorporate_tx\n" ++
  -- The four checked request calls each finish their own synthetic transaction
  -- at the common N+1 boundary.  Their execution rows remain in the side arena;
  -- their account effects are emitted before the account map is cleared, and
  -- their read/write maps are incorporated directly here.
  "  la t0, evm_env; la t2, c1_saved_logcount; ld t1, 0(t2); sd t1, 448(t0)\n" ++
  "  la t0, aer_bd_ptr; la t1, dbsr_bdbody; sd t1, 0(t0); la t0, aer_bd_len; la t1, dbsr_bdlen; ld t1, 0(t1); sd t1, 0(t0); la t0, aer_be_ptr; la t1, dbsr_bebody; sd t1, 0(t0); la t0, aer_be_len; la t1, dbsr_belen; ld t1, 0(t1); sd t1, 0(t0)\n" ++
  "  la t0, dbsr_saved_ra; ld ra, 0(t0); li a0, 0; ret\n" ++
  ".Ldsr_fail:\n" ++
  "  la t0, evm_env; la t2, c1_saved_logcount; ld t1, 0(t2); sd t1, 448(t0)\n" ++
  "  la t0, dbsr_saved_ra; ld ra, 0(t0); li a0, 1; ret\n" ++
  ".Lv2_input_hash:\n" ++
  -- The entry path reaches this label before block_verdict, so s0/s3/s4 still
  -- describe the stable SSZ input. M3 (#11835): do not parse supplied BAL into
  -- c1_bal_* here — no remaining guest consumer (M2 dropped deferred BAL
  -- finals). Header `block_access_list_hash` still hashes the SSZ BAL body via
  -- `block_access_list_hash` below; post-body rebuild compare is 60/61.
  "  addi t2, s0, 16; add t2, t2, s3; la t1, c1_er_input; sd t2, 0(t1)\n" ++
  "  bltu s4, s3, .Lv2_requests_hash_fail\n" ++
  "  sub t0, s4, s3; li t1, 16; bltu t0, t1, .Lv2_requests_hash_fail\n" ++
  "  addi a1, t0, -16; mv a0, t2; la a2, erh_requests_hash; jal ra, execution_requests_hash\n" ++
  "  la t1, c1_erh_status; sd a0, 0(t1)\n" ++
  "  bnez a0, .Lv2_requests_hash_fail\n" ++
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
  ".Lv2_codes_cap_fail:\n" ++
  "  li t0, 33; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
  "  j .Lv2_zero\n" ++
  ".Lv2_headers_cap_fail:\n" ++
  "  li t0, 34; la t1, bv_fail_code; sd t0, 0(t1)\n" ++
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

-- GH #10866: NEGATIVE guard -- this phase must NOT emit storage changes here.  The
-- placement was tried, measured at 1-of-3 and 0-of-8, and reverted; see the
-- comment at the discard.  Pinned so the obvious-looking home cannot be reoccupied
-- silently.
#guard (statelessVerdictV2Function.splitOn "jal ra, bal_emit_storage_changes").length == 1

-- GH #11390: an account-map row for a modeled system owner must take the
-- promotion path so its post is applied after the modeled system post.
#guard (executionMapStateChangesFunction.splitOn "jal ra, .Lem_owner_promote_account").length == 2
#guard (executionMapStateChangesFunction.splitOn ".Lem_account_process_seeded:").length == 2

end EvmAsm.Codegen
