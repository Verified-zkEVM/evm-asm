/-
  EvmAsm.Codegen.Programs.BalAccountApplyPostFields

  Compose BAL AccountChanges post-value extraction with account RLP rewriting.

  This is the account-value half of BAL replay for post-state-root recompute:
  given the pre-state account RLP and one BAL AccountChanges item, apply the
  final nonce and/or balance post-values reported by the BAL entry. Storage and
  code changes are handled by separate trie/account-root machinery.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.MptBoundedSort
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.RlpWalk

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch
import EvmAsm.Codegen.Programs.CommittedStorageLookup
import EvmAsm.Codegen.Programs.StorageWriteMap

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## baap_delete_single_leaf_storage

    Conservative storage-delete helper for BAL post-state replay. It handles
    only the common one-slot trie case: if the account's prior storageRoot is
    exactly a leaf at the cleared slot, deleting that slot makes the storage
    root the empty trie root. Other trie shapes stay conservative.

    a0 = account RLP ptr        a1 = account RLP length
    a2 = slot key ptr (32 B)    a3 = output account ptr
    a4 = u64 out account length ptr
    a0 (output) = 0 ok / 1 conservative or parse failure. -/
def baapDeleteSingleLeafStorage_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.baap_delete_single_leaf_storage + 60)),
    .BNE .x12 .x0 (444 : BitVec 13),
    .MV .x21 .x11,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.baap_delete_single_leaf_storage + 76)),
    .BNE .x11 .x0 (428 : BitVec 13),
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.baap_delete_single_leaf_storage + 88)),
    .BNE .x11 .x0 (416 : BitVec 13),
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.baap_delete_single_leaf_storage + 100)),
    .BNE .x11 .x0 (404 : BitVec 13),
    .LI .x7 (32 : Word),
    .BNE .x12 .x7 (396 : BitVec 13),
    .SUB .x6 .x10 .x12,
    .AUIPC .x5 (laHi GuestAddrs.baap_storage_root_ptr (GuestAddrs.baap_delete_single_leaf_storage + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_storage_root_ptr (GuestAddrs.baap_delete_single_leaf_storage + 120)),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x7 .x6,
    .AUIPC .x28 (laHi GuestAddrs.aps_empty_root (GuestAddrs.baap_delete_single_leaf_storage + 136)),
    .ADDI .x28 .x28 (laLo GuestAddrs.aps_empty_root (GuestAddrs.baap_delete_single_leaf_storage + 136)),
    .LI .x29 (32 : Word),
    .BEQ .x29 .x0 (332 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.srss_key (GuestAddrs.baap_delete_single_leaf_storage + 188)),
    .ADDI .x12 .x12 (laLo GuestAddrs.srss_key (GuestAddrs.baap_delete_single_leaf_storage + 188)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.baap_delete_single_leaf_storage + 196)),
    .AUIPC .x10 (laHi GuestAddrs.srss_key (GuestAddrs.baap_delete_single_leaf_storage + 200)),
    .ADDI .x10 .x10 (laLo GuestAddrs.srss_key (GuestAddrs.baap_delete_single_leaf_storage + 200)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.baap_storage_paths (GuestAddrs.baap_delete_single_leaf_storage + 212)),
    .ADDI .x12 .x12 (laLo GuestAddrs.baap_storage_paths (GuestAddrs.baap_delete_single_leaf_storage + 212)),
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.baap_delete_single_leaf_storage + 220)),
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_ptr (GuestAddrs.baap_delete_single_leaf_storage + 224)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_ptr (GuestAddrs.baap_delete_single_leaf_storage + 224)),
    .LD .x10 .x5 (0 : BitVec 12),
    .BEQ .x10 .x0 (272 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_len (GuestAddrs.baap_delete_single_leaf_storage + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_len (GuestAddrs.baap_delete_single_leaf_storage + 240)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.baap_storage_root_ptr (GuestAddrs.baap_delete_single_leaf_storage + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_storage_root_ptr (GuestAddrs.baap_delete_single_leaf_storage + 252)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.baap_item_off (GuestAddrs.baap_delete_single_leaf_storage + 264)),
    .ADDI .x13 .x13 (laLo GuestAddrs.baap_item_off (GuestAddrs.baap_delete_single_leaf_storage + 264)),
    .AUIPC .x14 (laHi GuestAddrs.baap_item_len (GuestAddrs.baap_delete_single_leaf_storage + 272)),
    .ADDI .x14 .x14 (laLo GuestAddrs.baap_item_len (GuestAddrs.baap_delete_single_leaf_storage + 272)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.baap_delete_single_leaf_storage + 280)),
    .BNE .x10 .x0 (224 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_ptr (GuestAddrs.baap_delete_single_leaf_storage + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_ptr (GuestAddrs.baap_delete_single_leaf_storage + 288)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.baap_item_off (GuestAddrs.baap_delete_single_leaf_storage + 300)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_item_off (GuestAddrs.baap_delete_single_leaf_storage + 300)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x10 .x6 .x7,
    .AUIPC .x5 (laHi GuestAddrs.baap_item_len (GuestAddrs.baap_delete_single_leaf_storage + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_item_len (GuestAddrs.baap_delete_single_leaf_storage + 316)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.baap_walk_val (GuestAddrs.baap_delete_single_leaf_storage + 328)),
    .ADDI .x12 .x12 (laLo GuestAddrs.baap_walk_val (GuestAddrs.baap_delete_single_leaf_storage + 328)),
    .AUIPC .x13 (laHi GuestAddrs.baap_walk_val_len (GuestAddrs.baap_delete_single_leaf_storage + 336)),
    .ADDI .x13 .x13 (laLo GuestAddrs.baap_walk_val_len (GuestAddrs.baap_delete_single_leaf_storage + 336)),
    .AUIPC .x14 (laHi GuestAddrs.baap_code_item_ptr (GuestAddrs.baap_delete_single_leaf_storage + 344)),
    .ADDI .x14 .x14 (laLo GuestAddrs.baap_code_item_ptr (GuestAddrs.baap_delete_single_leaf_storage + 344)),
    .AUIPC .x15 (laHi GuestAddrs.baap_val_len (GuestAddrs.baap_delete_single_leaf_storage + 352)),
    .ADDI .x15 .x15 (laLo GuestAddrs.baap_val_len (GuestAddrs.baap_delete_single_leaf_storage + 352)),
    .JAL .x1 (jalOff GuestAddrs.mpt_leaf_extract (GuestAddrs.baap_delete_single_leaf_storage + 360)),
    .BNE .x10 .x0 (144 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.baap_walk_val_len (GuestAddrs.baap_delete_single_leaf_storage + 368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_walk_val_len (GuestAddrs.baap_delete_single_leaf_storage + 368)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (64 : Word),
    .BNE .x5 .x6 (124 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.baap_walk_val (GuestAddrs.baap_delete_single_leaf_storage + 388)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_walk_val (GuestAddrs.baap_delete_single_leaf_storage + 388)),
    .AUIPC .x6 (laHi GuestAddrs.baap_storage_paths (GuestAddrs.baap_delete_single_leaf_storage + 396)),
    .ADDI .x6 .x6 (laLo GuestAddrs.baap_storage_paths (GuestAddrs.baap_delete_single_leaf_storage + 396)),
    .LI .x7 (64 : Word),
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (88 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.aps_empty_root (GuestAddrs.baap_delete_single_leaf_storage + 448)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aps_empty_root (GuestAddrs.baap_delete_single_leaf_storage + 448)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .JAL .x1 (jalOff GuestAddrs.account_set_storage_root (GuestAddrs.baap_delete_single_leaf_storage + 464)),
    .BNE .x10 .x0 (40 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .MV .x10 .x19,
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.baap_delete_single_leaf_storage + 492)),
    .SD .x20 .x9 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `baapDeleteSingleLeafStorage_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def baapDeleteSingleLeafStorage_relocs : RelocTable :=
  [ (15, .jal .x1 "rlp_walk_init"),
    (19, .jal .x1 "rlp_walk_next"),
    (22, .jal .x1 "rlp_walk_next"),
    (25, .jal .x1 "rlp_walk_next"),
    (30, .la .x5 "baap_storage_root_ptr"),
    (34, .la .x28 "aps_empty_root"),
    (47, .la .x12 "srss_key"),
    (49, .jal .x1 "zkvm_keccak256"),
    (50, .la .x10 "srss_key"),
    (53, .la .x12 "baap_storage_paths"),
    (55, .jal .x1 "bytes_to_nibbles"),
    (56, .la .x5 "aps_witness_ptr"),
    (60, .la .x5 "aps_witness_len"),
    (63, .la .x5 "baap_storage_root_ptr"),
    (66, .la .x13 "baap_item_off"),
    (68, .la .x14 "baap_item_len"),
    (70, .jal .x1 "witness_lookup_by_hash"),
    (72, .la .x5 "aps_witness_ptr"),
    (75, .la .x5 "baap_item_off"),
    (79, .la .x5 "baap_item_len"),
    (82, .la .x12 "baap_walk_val"),
    (84, .la .x13 "baap_walk_val_len"),
    (86, .la .x14 "baap_code_item_ptr"),
    (88, .la .x15 "baap_val_len"),
    (90, .jal .x1 "mpt_leaf_extract"),
    (92, .la .x5 "baap_walk_val_len"),
    (97, .la .x5 "baap_walk_val"),
    (99, .la .x6 "baap_storage_paths"),
    (112, .la .x12 "aps_empty_root"),
    (116, .jal .x1 "account_set_storage_root"),
    (123, .jal .x1 "mset_memcpy") ]

def baapDeleteSingleLeafStorageFunction : String :=
  "baap_delete_single_leaf_storage:\n" ++ emitProgramR baapDeleteSingleLeafStorage_prog baapDeleteSingleLeafStorage_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `baapDeleteSingleLeafStorage_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem baapDeleteSingleLeafStorageFunction_eq_prog :
    baapDeleteSingleLeafStorageFunction = "baap_delete_single_leaf_storage:\n" ++ emitProgramR baapDeleteSingleLeafStorage_prog baapDeleteSingleLeafStorage_relocs := rfl

#guard baapDeleteSingleLeafStorageFunction.startsWith "baap_delete_single_leaf_storage:\n"
#guard baapDeleteSingleLeafStorage_prog.length = 137
/-! ## map_account_apply_post_fields -- account RLP + changes shell -> post account RLP

    #11384: on the map-authoritative path (`bsr_account_from_map=1`), nonce/
    balance/code/storage come from `account_writes` / `storage_writes`, not from
    BAL AccountChanges field lists. a2/a3 may be the synthetic empty shell.

    a0 = account RLP ptr        a1 = account RLP length
    a2 = AccountChanges ptr     a3 = AccountChanges length
    a4 = output buffer ptr      a5 = u64 out length ptr
    a0 (output) = 0 ok / 1 parse fail or value length > 32.

    A missing BAL nonce/balance change list leaves that account field unchanged.
    A zero post-value is represented by length 0 from `bal_account_post_fields`
    and is spliced as the canonical RLP integer zero.

    Storage replay starts from the account's current storage root and applies
    only explicit BAL storage_changes, matching execution-specs witness_state
    post-state-root computation. -/
-- The value arena is a fixed, build-unit-local buffer.  Keep the end marker
-- adjacent to each unit's allocation and check the complete 40-byte envelope
-- (32-byte payload rounded up to an 8-byte boundary) before encoding or
-- advancing the cursor; the map/count guards alone do not prove this bound.
def mapAccountApplyPostFieldsFunction : String :=
  "map_account_apply_post_fields:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # original account ptr\n" ++
  "  mv s1, a1                   # original account len\n" ++
  "  mv s2, a2                   # AccountChanges ptr\n" ++
  "  mv s3, a3                   # AccountChanges len\n" ++
  "  mv s4, a4                   # out ptr\n" ++
  "  mv s5, a5                   # out len ptr\n" ++
  "  mv s6, s0                   # current account ptr\n" ++
  "  mv s7, s1                   # current account len\n" ++
  "  la t0, baap_fail_code; sd zero, 0(t0)\n" ++
  "  la t0, baap_storage_empty_flag; sd zero, 0(t0)\n" ++
  "  la t0, baap_sc_out_count; sd zero, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, baap_bal; la a3, baap_bal_len; la a4, baap_nonce; la a5, baap_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  # Apply the final BAL code change first, when present. CodeChanges items are\n" ++
  "  # [blockAccessIndex, newCode]; the account field stores keccak256(newCode).\n" ++
  "  mv a0, s2; mv a1, s3; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s8, a0; mv s9, a1; li s10, 5\n" ++
  ".Lbaap_code_field_skip:\n" ++
  "  beqz s10, .Lbaap_code_field_ready\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv s8, a0; addi s10, s10, -1; j .Lbaap_code_field_skip\n" ++
  ".Lbaap_code_field_ready:\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  sub t0, a0, a2; la t1, baap_code_list_ptr; sd t0, 0(t1); la t1, baap_code_list_len; sd a2, 0(t1)\n" ++
  "  mv a0, t0; mv a1, a2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s8, a0; mv s9, a1; li s10, 0\n" ++
  ".Lbaap_code_last_loop:\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  li t0, 2; beq a1, t0, .Lbaap_code_last_done\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv s8, a0; sub t0, a0, a2; la t1, baap_code_item_ptr; sd t0, 0(t1); la t1, baap_item_len; sd a2, 0(t1); li s10, 1\n" ++
  "  j .Lbaap_code_last_loop\n" ++
  ".Lbaap_code_last_done:\n" ++
  "  beqz s10, .Lbaap_storage_gate\n" ++
  "  la t0, bsr_account_from_map; ld t0, 0(t0); bnez t0, .Lbaap_storage_gate\n" ++
  "  la t0, baap_code_item_ptr; ld a0, 0(t0); la t0, baap_item_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s8, a0; mv s9, a1\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv s8, a0\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; la a2, baap_code_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, baap_code_hash; li a1, 32; la a2, aab_enc; la a3, aab_enc_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 3; la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0)\n" ++
  "  la a5, baap_tmp3; la a6, baap_tmp3_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp3; la t0, baap_tmp3_len; ld s7, 0(t0)\n" ++
  ".Lbaap_storage_gate:\n" ++
  "  # Apply one BAL storage change first when present. Storage-only user-tx\n" ++
  "  # writes still affect the post-state account even without balance/nonce\n" ++
  "  # changes; an empty storage_changes list falls through unchanged.\n" ++
  "  la t0, bsr_account_from_map; ld t0, 0(t0); beqz t0, .Lbaap_try_storage\n" ++
  "  la t1, bsr_account_row; ld t1, 0(t1); lbu t2, 112(t1); andi t2, t2, 4; beqz t2, .Lbaap_try_storage\n" ++
  "  ld a0, 80(t1); ld a1, 88(t1); la a2, baap_code_hash; jal ra, zkvm_keccak256\n" ++
  "  la a0, baap_code_hash; li a1, 32; la a2, aab_enc; la a3, aab_enc_len; jal ra, rlp_encode_bytes\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 3; la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0); la a5, baap_tmp3; la a6, baap_tmp3_len\n" ++
  "  jal ra, mpt_splice_slot; bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp3; la t0, baap_tmp3_len; ld s7, 0(t0)\n" ++
  ".Lbaap_try_storage:\n" ++
  "  mv a0, s2; mv a1, s3; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s8, a0; mv s9, a1\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv s8, a0\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  sub t0, a0, a2; la t1, baap_sc_ptr; sd t0, 0(t1); la t1, baap_sc_len; sd a2, 0(t1)\n" ++
  "  mv a0, t0; mv a1, a2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s8, a0; mv s9, a1; li s10, 0\n" ++
  ".Lbaap_sc_count_loop:\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  li t0, 2; beq a1, t0, .Lbaap_sc_count_done\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv s8, a0; addi s10, s10, 1; j .Lbaap_sc_count_loop\n" ++
  ".Lbaap_sc_count_done:\n" ++
  "  la t0, baap_sc_count; sd s10, 0(t0); la t0, bsr_storage_from_map; ld t0, 0(t0); li t1, 1; beq t0, t1, .Lbaap_map_storage; beqz s10, .Lbaap_nonce\n" ++
  "  la t0, baap_sc_ptr; ld a0, 0(t0); la t0, baap_sc_len; ld a1, 0(t0); jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s8, a0; mv s9, a1\n" ++
  "  # Storage changes share one bounded descriptor stream regardless of count.\n" ++
  "  la t0, bsr_storage_from_map; ld t0, 0(t0); li t1, 1; beq t0, t1, .Lbaap_map_storage\n" ++
  "  j .Lbaap_multi_storage\n" ++
  -- Terminal block-state replay path: replace BAL's final storage values with
  -- the canonical execution-specs block map.  The mode is set only by the
  -- post-incorporation block_state_root caller; a zero map count therefore
  -- means no committed rows, not an early read of an unpopulated map.
  ".Lbaap_map_storage:\n" ++
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s10, a1; mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail; li t2, 32; bne a2, t2, .Lbaap_fail\n" ++
  "  sub t1, a0, a2; la t0, baap_storage_root_ptr; sd t1, 0(t0)\n" ++
  "  la t2, aps_empty_root; li t3, 32\n" ++
  ".Lbaap_map_empty_cmp:\n" ++
  "  beqz t3, .Lbaap_map_empty_ok\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbaap_map_nonempty\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbaap_map_empty_cmp\n" ++
  ".Lbaap_map_empty_ok:\n" ++
  "  li t0, 1; la t1, baap_storage_empty_flag; sd t0, 0(t1); j .Lbaap_map_init\n" ++
  ".Lbaap_map_nonempty:\n" ++
  "  la t0, baap_storage_empty_flag; sd zero, 0(t0)\n" ++
  ".Lbaap_map_init:\n" ++
  "  la t0, baap_map_addr; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  mv a0, s2; mv a1, s3; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s10, a1; mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail; li t0, 20; bne a2, t0, .Lbaap_fail\n" ++
  "  sub t0, a0, a2; addi t1, t0, 19; la t2, baap_map_addr; li t3, 0\n" ++
  ".Lbaap_map_addr_rev:\n" ++
  "  li t4, 20; beq t3, t4, .Lbaap_map_addr_done\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, 1; j .Lbaap_map_addr_rev\n" ++
  ".Lbaap_map_addr_done:\n" ++
  "  la t0, baap_storage_values; la t1, baap_storage_value_cursor; sd t0, 0(t1)\n" ++
  -- Step 1 of #10651: the execution map is the candidate-set authority.  The
  -- BAL item still supplies the account identity for this invocation, but the
  -- slot loop below walks every canonical block-map row and filters by that
  -- account.  A storage_writes row omitted from BAL is therefore visited by
  -- the same post-state replay path once the root driver enumerates its owner.
  "  la t0, storage_writes_count; ld t1, 0(t0); la t0, baap_sc_count; sd t1, 0(t0)\n" ++
  "  la t0, baap_sc_index; sd zero, 0(t0); la t0, baap_sc_out_count; sd zero, 0(t0)\n" ++
  ".Lbaap_map_loop:\n" ++
  "  la t0, baap_sc_index; ld t0, 0(t0); la t1, baap_sc_count; ld t1, 0(t1); beq t0, t1, .Lbaap_map_apply\n" ++
  "  li t2, " ++ toString storageWritesCapacity ++ "; bgeu t0, t2, .Lbaap_fail\n" ++
  "  slli t2, t0, 7; li t3, 0xa1fa0000; add t2, t2, t3\n" ++
  "  la t3, baap_map_addr; li t4, 0\n" ++
  ".Lbaap_map_addr_cmp:\n" ++
  "  li t5, 20; beq t4, t5, .Lbaap_map_row_hit\n" ++
  "  add t5, t2, t4; lbu t5, 0(t5); add t6, t3, t4; lbu t6, 0(t6); bne t5, t6, .Lbaap_map_next\n" ++
  "  addi t4, t4, 1; j .Lbaap_map_addr_cmp\n" ++
  ".Lbaap_map_row_hit:\n" ++
  "  la t3, baap_slot; addi t4, t2, 63; li t5, 32\n" ++
  ".Lbaap_map_slot_copy:\n" ++
  "  beqz t5, .Lbaap_map_slot_done; lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, -1; addi t3, t3, 1; addi t5, t5, -1; j .Lbaap_map_slot_copy\n" ++
  ".Lbaap_map_slot_done:\n" ++
  "  la t3, baap_map_value; ld t4, 64(t2); sd t4, 0(t3); ld t4, 72(t2); sd t4, 8(t3); ld t4, 80(t2); sd t4, 16(t3); ld t4, 88(t2); sd t4, 24(t3)\n" ++
  "  la a0, baap_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); li t1, " ++ toString bsrMaxBalItems ++ "; bgeu t0, t1, .Lbaap_fail; slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1\n" ++
  "  la a0, srss_key; li a1, 32; jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_map_value; addi t1, t0, 31; la t2, baap_map_value_be; li t3, 0\n" ++
  ".Lbaap_map_value_rev:\n" ++
  "  li t4, 32; beq t3, t4, .Lbaap_map_value_strip\n" ++
  "  lbu t5, 0(t1); sb t5, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, 1; j .Lbaap_map_value_rev\n" ++
  ".Lbaap_map_value_strip:\n" ++
  "  la t1, baap_map_value_be; li t2, 0\n" ++
  ".Lbaap_map_value_strip_loop:\n" ++
  "  li t3, 32; beq t2, t3, .Lbaap_map_zero\n" ++
  "  lbu t4, 0(t1); bnez t4, .Lbaap_map_value_nonzero\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; j .Lbaap_map_value_strip_loop\n" ++
  ".Lbaap_map_zero:\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_map_next\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); li t1, " ++ toString bsrMaxBalItems ++ "; bgeu t0, t1, .Lbaap_fail\n" ++
  "  slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1); sd zero, 16(t1); sd zero, 24(t1); li t2, 2; sd t2, 32(t1)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1); j .Lbaap_map_next\n" ++
  ".Lbaap_map_value_nonzero:\n" ++
  "  sub t3, t3, t2; add a0, t1, zero; mv a1, t3; la t4, baap_storage_value_cursor; ld a2, 0(t4); la t0, baap_storage_values_end; li t1, 40; add t2, a2, t1; bgtu t2, t0, .Lbaap_fail_storage_bounds; la a3, aab_enc_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_map_insert\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0); la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a3, t2, t1; li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len\n" ++
  "  jal ra, mpt_walk; beqz a0, .Lbaap_map_modify; li t0, 1; bne a0, t0, .Lbaap_fail; li t5, 1; j .Lbaap_map_desc\n" ++
  ".Lbaap_map_insert:\n  li t5, 1; j .Lbaap_map_desc\n" ++
  ".Lbaap_map_modify:\n  li t5, 0\n" ++
  ".Lbaap_map_desc:\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1); la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1); la t4, aab_enc_len; ld t4, 0(t4); sd t4, 24(t1); sd t5, 32(t1)\n" ++
  "  add t6, t3, t4; addi t6, t6, 7; andi t6, t6, -8; la t1, baap_storage_values_end; bgtu t6, t1, .Lbaap_fail_storage_bounds; sd t6, 0(t2); addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)\n" ++
  ".Lbaap_map_next:\n" ++
  "  la t0, baap_sc_index; ld t0, 0(t0); addi t0, t0, 1; la t1, baap_sc_index; sd t0, 0(t1); j .Lbaap_map_loop\n" ++
  ".Lbaap_map_apply:\n" ++
  "  la t0, baap_sc_out_count; ld a4, 0(t0); beqz a4, .Lbaap_nonce\n" ++
  "  j .Lbaap_multi_apply\n" ++
  ".Lbaap_multi_storage:\n" ++
  "  # Multi-slot BAL storage replay is supported when the account's prior\n" ++
  "  # storage trie is empty: build all storage insert descriptors and apply\n" ++
  "  # them together so the intermediate trie root need not be in the witness.\n" ++
  "  # Final zero slot values are trie-default no-ops for an empty storage trie.\n" ++
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s10, a1\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  li t2, 32; bne a2, t2, .Lbaap_fail\n" ++
  "  sub t1, a0, a2; la t0, baap_storage_root_ptr; sd t1, 0(t0)\n" ++
  "  la t2, aps_empty_root; li t3, 32\n" ++
  ".Lbaap_empty_cmp:\n" ++
  "  beqz t3, .Lbaap_empty_ok\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbaap_nonempty_ok\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbaap_empty_cmp\n" ++
  ".Lbaap_empty_ok:\n" ++
  "  li t0, 1; la t1, baap_storage_empty_flag; sd t0, 0(t1)\n" ++
  "  j .Lbaap_multi_init\n" ++
  ".Lbaap_nonempty_ok:\n" ++
  "  la t0, baap_storage_empty_flag; sd zero, 0(t0)\n" ++
  ".Lbaap_multi_init:\n" ++
  "  la t0, baap_storage_values; la t1, baap_storage_value_cursor; sd t0, 0(t1)\n" ++
  "  la t0, baap_sc_index; sd zero, 0(t0)\n" ++
  "  la t0, baap_sc_out_count; sd zero, 0(t0)\n" ++
  ".Lbaap_multi_loop:\n" ++
  "  la t0, baap_sc_index; ld t0, 0(t0); la t1, baap_sc_count; ld t1, 0(t1)\n" ++
  "  beq t0, t1, .Lbaap_multi_apply\n" ++
  "  li t2, " ++ toString bsrMaxBalItems ++ "; bgeu t0, t2, .Lbaap_fail\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv s8, a0; sub t0, a0, a2; la t1, baap_code_item_ptr; sd t0, 0(t1); la t1, baap_item_len; sd a2, 0(t1)\n" ++
  "  mv a0, t0; mv a1, a2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s10, a1\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  sub t0, a0, a2; la t1, baap_val_ptr; sd t0, 0(t1); la t1, baap_val_len; sd a2, 0(t1)\n" ++
  "  la t0, baap_val_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  la t0, baap_slot; li t1, 0\n" ++
  ".Lbaap_mslot_zero:\n" ++
  "  li t2, 32; beq t1, t2, .Lbaap_mslot_zero_done\n" ++
  "  add t3, t0, t1; sb zero, 0(t3); addi t1, t1, 1; j .Lbaap_mslot_zero\n" ++
  ".Lbaap_mslot_zero_done:\n" ++
  "  la t0, baap_val_len; ld t1, 0(t0); li t2, 32; sub t2, t2, t1; la t3, baap_slot; add t3, t3, t2\n" ++
  "  la t0, baap_val_ptr; ld t0, 0(t0)\n" ++
  ".Lbaap_mslot_cp:\n" ++
  "  beqz t1, .Lbaap_mslot_done\n" ++
  "  lbu t2, 0(t0); sb t2, 0(t3); addi t0, t0, 1; addi t3, t3, 1; addi t1, t1, -1; j .Lbaap_mslot_cp\n" ++
  ".Lbaap_mslot_done:\n" ++
  "  la t0, baap_code_item_ptr; ld a0, 0(t0); la t0, baap_item_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s10, a1\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  sub t0, a0, a2; la t1, baap_slot_changes_ptr; sd t0, 0(t1); la t1, baap_slot_changes_len; sd a2, 0(t1)\n" ++
  "  mv a0, t0; mv a1, a2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s10, a1; la t0, baap_slot_changes_count; sd zero, 0(t0)\n" ++
  ".Lbaap_multi_slot_change_last_loop:\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  li t0, 2; beq a1, t0, .Lbaap_multi_slot_change_last_done\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  sub t0, a0, a2; la t1, baap_code_item_ptr; sd t0, 0(t1); la t1, baap_item_len; sd a2, 0(t1); li t0, 1; la t1, baap_slot_changes_count; sd t0, 0(t1)\n" ++
  "  j .Lbaap_multi_slot_change_last_loop\n" ++
  ".Lbaap_multi_slot_change_last_done:\n" ++
  "  la t0, baap_slot_changes_count; ld t0, 0(t0); beqz t0, .Lbaap_fail\n" ++
  "  la t0, baap_code_item_ptr; ld a0, 0(t0); la t0, baap_item_len; ld a1, 0(t0)\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaap_fail\n" ++
  "  mv s10, a1\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaap_fail\n" ++
  "  sub t0, a0, a2; la t1, baap_val_ptr; sd t0, 0(t1); la t1, baap_val_len; sd a2, 0(t1)\n" ++
  "  la t0, baap_val_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  la t1, baap_val_ptr; ld a0, 0(t1)\n" ++
  "  mv a1, t0; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, aab_enc_len\n" ++
  ".Lbaap_multi_value_strip_zero:\n" ++
  "  beqz a1, .Lbaap_multi_zero_value\n" ++
  "  lbu t0, 0(a0); bnez t0, .Lbaap_multi_encode_value\n" ++
  "  addi a0, a0, 1; addi a1, a1, -1; j .Lbaap_multi_value_strip_zero\n" ++
  ".Lbaap_multi_zero_value:\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_multi_skip_zero\n" ++
  "  # A final zero is one committed delete descriptor; empty-root zeroes\n" ++
  "  # remain no-ops.\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); li t1, " ++ toString bsrMaxBalItems ++ "; bgeu t0, t1, .Lbaap_fail\n" ++
  "  la a0, baap_slot; li a1, 32; la a2, srss_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1\n" ++
  "  la a0, srss_key; li a1, 32\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1); sd zero, 16(t1); sd zero, 24(t1); li t2, 2; sd t2, 32(t1)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)\n" ++
  "  j .Lbaap_multi_skip_zero\n" ++
  ".Lbaap_multi_encode_value:\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_multi_encode_nonzero\n" ++
  ".Lbaap_multi_encode_nonzero:\n" ++
  "  la t0, baap_storage_values_end; li t1, 40; add t2, a2, t1; bgtu t2, t0, .Lbaap_fail_storage_bounds\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la a0, baap_slot; li a1, 32; la a2, srss_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1\n" ++
  "  la a0, srss_key; li a1, 32\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_mslot_insert\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0)\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0)\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a3, t2, t1\n" ++
  "  li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbaap_mslot_modify\n" ++
  "  li t0, 1; bne a0, t0, .Lbaap_fail\n" ++
  ".Lbaap_mslot_insert:\n" ++
  "  li t5, 1; j .Lbaap_mslot_have_mode\n" ++
  ".Lbaap_mslot_modify:\n" ++
  "  li t5, 0\n" ++
  ".Lbaap_mslot_have_mode:\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2\n" ++
  "  la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1)\n" ++
  "  li t2, 64; sd t2, 8(t1)\n" ++
  "  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1)\n" ++
  "  la t4, aab_enc_len; ld t4, 0(t4); sd t4, 24(t1)\n" ++
  "  sd t5, 32(t1)\n" ++
  "  add t6, t3, t4; addi t6, t6, 7; andi t6, t6, -8; la t1, baap_storage_values_end; bgtu t6, t1, .Lbaap_fail_storage_bounds; sd t6, 0(t2)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)\n" ++
  ".Lbaap_multi_skip_zero:\n" ++
  "  la t0, baap_sc_index; ld t0, 0(t0)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_index; sd t0, 0(t1); j .Lbaap_multi_loop\n" ++
  -- #11385: `storage_root` is derived from the storage_writes rows at this
  -- use via `mpt_bounded_storage_root`; it is not a map field or mask bit.
  -- The explicit legacy call below is only the conservative builder-failure
  -- fallback and does not introduce a stored storage-root representation.
  ".Lbaap_multi_apply:\n" ++
  "  la t0, baap_sc_out_count; ld a4, 0(t0); beqz a4, .Lbaap_nonce\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_multi_apply_empty\n" ++
  "  j .Lbaap_multi_apply_nonempty\n" ++
  ".Lbaap_multi_apply_empty:\n" ++
  "  la a0, aps_empty_root; mv a1, zero; mv a2, zero; la a3, baap_storage_desc\n" ++
  "  j .Lbaap_multi_apply_call\n" ++
  ".Lbaap_multi_apply_nonempty:\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0)\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0); la a3, baap_storage_desc\n" ++
  ".Lbaap_multi_apply_call:\n" ++
  "  la a5, aps_newsroot\n" ++
  "  jal ra, mpt_bounded_storage_root\n" ++
  "  bnez a0, .Lbaap_multi_apply_legacy\n" ++
  "  j .Lbaap_multi_set_account\n" ++
  "# Conservative bounded-builder bailout fallback: preserve the legacy exact\n" ++
  "# storage replay instead of rejecting a valid BAL row. This is intentionally\n" ++
  "# isolated so the normal route remains bounded and the unmasked behavior can\n" ++
  "# be measured independently.\n" ++
  ".Lbaap_multi_apply_legacy:\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_multi_legacy_empty\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0); j .Lbaap_multi_legacy_args\n" ++
  ".Lbaap_multi_legacy_empty:\n" ++
  "  la a0, aps_empty_root; mv a1, zero; mv a2, zero\n" ++
  ".Lbaap_multi_legacy_args:\n" ++
  "  la a3, baap_storage_desc; la t0, baap_sc_out_count; ld a4, 0(t0); la a5, aps_newsroot\n" ++
  "  jal ra, mpt_state_root_ins\n" ++
  "  bnez a0, .Lbaap_fail_storage_apply\n" ++
  ".Lbaap_multi_set_account:\n" ++
  "  mv a0, s6; mv a1, s7; la a2, aps_newsroot; la a3, baap_tmp2; la a4, baap_tmp2_len\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Lbaap_fail_storage_root\n" ++
  "  la s6, baap_tmp2; la t0, baap_tmp2_len; ld s7, 0(t0)\n" ++
  "  # Apply nonce first if present.\n" ++
  "  j .Lbaap_nonce\n" ++
  ".Lbaap_nonce:\n" ++
  "  la t0, bsr_account_from_map; ld t0, 0(t0); bnez t0, .Lbaap_map_nonce\n" ++
  "  la t0, baap_nonce_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbaap_balance\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 0\n" ++
  "  la a3, baap_nonce; mv a4, t0; la a5, baap_tmp; la a6, baap_tmp_len\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbaap_fail_nonce\n" ++
  "  la s6, baap_tmp; la t0, baap_tmp_len; ld s7, 0(t0)\n" ++
  "  j .Lbaap_balance\n" ++
  ".Lbaap_map_nonce:\n" ++
  "  la t1, bsr_account_row; ld t1, 0(t1); lbu t2, 112(t1); andi t2, t2, 2; beqz t2, .Lbaap_balance\n" ++
  "  ld t0, 64(t1); la t2, baap_map_value_be; addi t3, t2, 8; li t4, 8\n" ++
  ".Lbaap_map_nonce_bytes:\n" ++
  "  beqz t4, .Lbaap_map_nonce_strip; addi t3, t3, -1; andi t5, t0, 255; sb t5, 0(t3); srli t0, t0, 8; addi t4, t4, -1; j .Lbaap_map_nonce_bytes\n" ++
  ".Lbaap_map_nonce_strip:\n" ++
  "  la t1, baap_map_value_be; li t2, 0\n" ++
  ".Lbaap_map_nonce_strip_loop:\n" ++
  "  li t3, 8; beq t2, t3, .Lbaap_map_nonce_zero; lbu t4, 0(t1); bnez t4, .Lbaap_map_nonce_nonzero; addi t1, t1, 1; addi t2, t2, 1; j .Lbaap_map_nonce_strip_loop\n" ++
  ".Lbaap_map_nonce_zero:\n" ++
  "  la a3, baap_map_value_be; li a4, 0; j .Lbaap_map_nonce_apply\n" ++
  ".Lbaap_map_nonce_nonzero:\n" ++
  "  li t3, 8; sub a4, t3, t2; mv a3, t1\n" ++
  ".Lbaap_map_nonce_apply:\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 0; la a5, baap_tmp; la a6, baap_tmp_len; jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbaap_fail_nonce; la s6, baap_tmp; la t0, baap_tmp_len; ld s7, 0(t0)\n" ++
  ".Lbaap_balance:\n" ++
  "  la t0, bsr_account_from_map; ld t0, 0(t0); beqz t0, .Lbaap_legacy_balance\n" ++
  "  la t1, bsr_account_row; ld t1, 0(t1); lbu t2, 112(t1); andi t2, t2, 1; beqz t2, .Lbaap_copy_current\n" ++
  "  la t2, baap_map_value_be; ld t3, 32(t1); sd t3, 0(t2); ld t3, 40(t1); sd t3, 8(t2); ld t3, 48(t1); sd t3, 16(t2); ld t3, 56(t1); sd t3, 24(t2)\n" ++
  "  la t1, baap_map_value_be; li t2, 0\n" ++
  ".Lbaap_map_balance_strip_loop:\n" ++
  "  li t3, 32; beq t2, t3, .Lbaap_map_balance_zero; lbu t4, 0(t1); bnez t4, .Lbaap_map_balance_nonzero; addi t1, t1, 1; addi t2, t2, 1; j .Lbaap_map_balance_strip_loop\n" ++
  ".Lbaap_map_balance_zero:\n" ++
  "  la a3, baap_map_value_be; li a4, 0; j .Lbaap_map_balance_apply\n" ++
  ".Lbaap_map_balance_nonzero:\n" ++
  "  li t3, 32; sub a4, t3, t2; mv a3, t1\n" ++
  ".Lbaap_map_balance_apply:\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 1; mv a5, s4; mv a6, s5; jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbaap_fail_balance; j .Lbaap_ret\n" ++
  ".Lbaap_legacy_balance:\n" ++
  "  # Apply balance if present; otherwise copy the current account to the final output.\n" ++
  "  la t0, baap_bal_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbaap_copy_current\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 1\n" ++
  "  la a3, baap_bal; mv a4, t0; mv a5, s4; mv a6, s5\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbaap_fail_balance\n" ++
  "  j .Lbaap_ret\n" ++
  ".Lbaap_copy_current:\n" ++
  "  mv a0, s4; mv a1, s6; mv a2, s7\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  sd s7, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbaap_ret\n" ++
  ".Lbaap_fail_storage_apply:\n" ++
  "  li t0, 501; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_storage_delete:\n" ++
  "  li t0, 502; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_storage_root:\n" ++
  "  li t0, 503; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_storage_delete_only:\n" ++
  "  li t0, 504; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_nonce:\n" ++
  "  li t0, 505; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_balance:\n" ++
  "  li t0, 506; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_storage_bounds:\n" ++
  "  li t0, 599; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail:\n" ++
  "  la t1, baap_fail_code; ld t0, 0(t1); bnez t0, .Lbaap_fail_have_code\n" ++
  "  li t0, 599; sd t0, 0(t1)\n" ++
  ".Lbaap_fail_have_code:\n" ++
  "  li a0, 1\n" ++
  ".Lbaap_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_map_account_apply_post_fields`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account RLP length (u64)
      +16 AccountChanges RLP length (u64)
      +24 account RLP bytes, padded to 8 bytes
      then AccountChanges RLP bytes
    Output layout:
      OUTPUT+0   : new account RLP length
      OUTPUT+8   : new account RLP bytes
      OUTPUT+240 : internal fail code (0 on success)
      OUTPUT+248 : status -/
def ziskMapAccountApplyPostFieldsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a3, 16(t0)               # AccountChanges len\n" ++
  "  addi a0, t0, 24             # account ptr\n" ++
  "  add a2, a0, a1              # AccountChanges ptr after padded account\n" ++
  "  addi a2, a2, 7; andi a2, a2, -8\n" ++
  "  li a4, 0xa0010008           # out account bytes at OUTPUT+8\n" ++
  "  li a5, 0xa0010000           # out account length at OUTPUT+0\n" ++
  "  jal ra, map_account_apply_post_fields\n" ++
  "  la t1, baap_fail_code; ld t2, 0(t1); li t0, 0xa00100f0; sd t2, 0(t0)   # fail_code at OUTPUT+240\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)   # status at OUTPUT+248\n" ++
  "  j .Lbaap_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  mptBoundedBuilderFrontEndFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  accountApplyStorageSlotAccFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  storageWritesBlockLatestValueFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  mapAccountApplyPostFieldsFunction ++ "\n" ++
  ".Lbaap_pdone:"

def ziskMapAccountApplyPostFieldsDataSection : String :=
  storageWriteMapDataSection ++ "\n" ++
  ziskMptStateRootInsDataSection ++ "\n" ++
  -- The bounded storage-root fallback closure reopens constructed children by
  -- Patricia depth; standalone BAAP probes need the same fixed cache as the
  -- production guest.
  mptBoundedConstructedCacheDataSection ++ "\n" ++
  ziskBalAccountPostFieldsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "aab_bal_off:\n  .zero 8\n" ++
  "aab_bal_len:\n  .zero 8\n" ++
  "aab_enc_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aab_bal32:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_enc:\n  .zero 64\n" ++
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
  ".balign 8\n" ++
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
  "bsr_storage_from_map:\n  .zero 8\n" ++
  "bsr_account_from_map:\n  .zero 8\n" ++
  "bsr_account_row:\n  .zero 8\n" ++
  "baap_storage_root_ptr:\n  .zero 8\n" ++
  "baap_walk_val_len:\n  .zero 8\n" ++
  "baap_item_off:\n  .zero 8\n" ++
  "baap_item_len:\n  .zero 8\n" ++
  "baap_slot_changes_off:\n  .zero 8\n" ++
  "baap_slot_changes_len:\n  .zero 8\n" ++
  "baap_slot_changes_ptr:\n  .zero 8\n" ++
  "baap_slot_changes_count:\n  .zero 8\n" ++
  "baap_val_off:\n  .zero 8\n" ++
  "baap_val_len:\n  .zero 8\n" ++
  "baap_val_ptr:\n  .zero 8\n" ++
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
  "baap_map_addr:\n  .zero 32\n" ++
  "baap_map_value:\n  .zero 32\n" ++
  "baap_map_value_be:\n  .zero 32\n" ++
  "baap_map_recip_scratch:\n  .zero 32\n" ++
  "baap_map_slot_scratch:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "baap_tmp2:\n  .zero 512\n" ++
  "baap_tmp3:\n  .zero 512\n" ++
  "baap_storage_value_cursor:\n  .zero 8\n" ++
  "baap_walk_val:\n  .zero 128\n" ++
  "bsr_sort_ranges:\n  .zero " ++ toString (bsrMptSortRangeStackCapacity * bsrMptSortRangeFrameBytes) ++ "\n" ++
  "bsr_builder_frames:\n  .zero " ++ toString (bsrMptBuilderFrameCapacity * bsrMptBuilderFrameBytes) ++ "\n" ++
  "bsr_builder_node:\n  .zero " ++ toString bsrMptBuilderNodeScratchBytes ++ "\n" ++
  "bsr_builder_result_ref:\n  .zero " ++ toString bsrMptFrameChildRefBytes ++ "\n" ++
  "bsr_builder_result_len:\n  .zero 8\n" ++
  "bsr_builder_value_max:\n  .zero 8\n" ++
  "bsr_builder_witness_value_max:\n  .zero 8\n" ++
  "baap_storage_desc:\n  .zero 2400000\n" ++
  "baap_storage_paths:\n  .zero 3840000\n" ++
  "baap_storage_values:\n  .zero 3840000\nbaap_storage_values_end:\n" ++
  "baap_out_pad:\n  .zero 8"

def ziskMapAccountApplyPostFieldsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMapAccountApplyPostFieldsPrologue
  dataAsm     := ziskMapAccountApplyPostFieldsDataSection
}

end EvmAsm.Codegen
