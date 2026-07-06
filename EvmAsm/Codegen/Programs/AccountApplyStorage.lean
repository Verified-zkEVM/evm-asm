/-
  EvmAsm.Codegen.Programs.AccountApplyStorage

  account_apply_storage_slot (bead evm-asm-fhsxz.2.4.2.5, step c): apply a single
  storage write to an account, producing the new account RLP. This is the per-
  system-contract update the EIP-2935 (history) and EIP-4788 (beacon-roots) block-
  start system calls perform, and the brick that composes the StorageWrite
  primitives into the Step-2 state recompute.

  Given an account [nonce, balance, storageRoot, codeHash] and a (slot_key, value):
    1. read field 2 (storageRoot) via rlp_list_nth_item;
    2. if it is NOT the EMPTY_TRIE_ROOT, return status 1 (conservative miss —
       a non-empty storage trie needs the general storage-trie update, out of the
       single-leaf engine's scope; the verdict then leaves x11 = 0, never a false
       positive). The genesis case both system contracts hit on the first blocks
       (empty prior storage) IS handled;
    3. else new_storage_root = storage_root_single_slot(slot_key, value);
    4. account_set_storage_root(account, new_storage_root) -> new account RLP.

  Composes storage_root_single_slot + account_set_storage_root (StorageWrite) +
  rlp_list_nth_item; all byte work byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptDeleteAcc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_apply_storage_slot
    a0 = account RLP ptr   a1 = account RLP length
    a2 = slot_key ptr (32 B)   a3 = value ptr (minimal-BE word)   a4 = value len
    a5 = out account RLP ptr   a6 = u64 out length ptr
    a0 (output) = 0 (ok) / 1 (non-empty prior storage: conservative) /
                  2 (parse fail). -/
def accountApplyStorageSlot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (2 : Word),
    .AUIPC .x13 (laHi GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot + 76)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot + 76)),
    .AUIPC .x14 (laHi GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot + 84)),
    .ADDI .x14 .x14 (laLo GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot + 84)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_apply_storage_slot + 92)),
    .BNE .x10 .x0 (156 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot + 100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (128 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot + 120)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x8 .x6,
    .AUIPC .x7 (laHi GuestAddrs.aps_empty_root (GuestAddrs.account_apply_storage_slot + 136)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aps_empty_root (GuestAddrs.account_apply_storage_slot + 136)),
    .LI .x28 (32 : Word),
    .BEQ .x28 .x0 (32 : BitVec 13),
    .LBU .x29 .x6 (0 : BitVec 12),
    .LBU .x30 .x7 (0 : BitVec 12),
    .BNE .x29 .x30 (84 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x20,
    .AUIPC .x13 (laHi GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot + 192)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot + 192)),
    .JAL .x1 (jalOff GuestAddrs.storage_root_single_slot (GuestAddrs.account_apply_storage_slot + 200)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot + 212)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot + 212)),
    .MV .x13 .x21,
    .MV .x14 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_set_storage_root (GuestAddrs.account_apply_storage_slot + 228)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountApplyStorageSlot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountApplyStorageSlot_relocs : RelocTable :=
  [ (19, .la .x13 "aps_off"),
    (21, .la .x14 "aps_len"),
    (23, .jal .x1 "rlp_list_nth_item"),
    (25, .la .x5 "aps_len"),
    (30, .la .x5 "aps_off"),
    (34, .la .x7 "aps_empty_root"),
    (48, .la .x13 "aps_newsroot"),
    (50, .jal .x1 "storage_root_single_slot"),
    (53, .la .x12 "aps_newsroot"),
    (57, .jal .x1 "account_set_storage_root") ]

def accountApplyStorageSlotFunction : String :=
  "account_apply_storage_slot:\n" ++ emitProgramR accountApplyStorageSlot_prog accountApplyStorageSlot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountApplyStorageSlot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountApplyStorageSlotFunction_eq_prog :
    accountApplyStorageSlotFunction = "account_apply_storage_slot:\n" ++ emitProgramR accountApplyStorageSlot_prog accountApplyStorageSlot_relocs := rfl

#guard accountApplyStorageSlotFunction.startsWith "account_apply_storage_slot:\n"
#guard accountApplyStorageSlot_prog.length = 74
/-! ## account_apply_storage_slot_acc
    Same external ABI as `account_apply_storage_slot`, but handles non-empty
    prior storage roots by updating the storage trie through `mpt_set_acc`.
    The caller must set `aps_witness_ptr` / `aps_witness_len` to the witness
    section containing the storage trie nodes before calling this helper. -/
def accountApplyStorageSlotAcc_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (2 : Word),
    .AUIPC .x13 (laHi GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 76)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 76)),
    .AUIPC .x14 (laHi GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot_acc + 84)),
    .ADDI .x14 .x14 (laLo GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot_acc + 84)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_apply_storage_slot_acc + 92)),
    .BNE .x10 .x0 (672 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot_acc + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_len (GuestAddrs.account_apply_storage_slot_acc + 100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (644 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 120)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x8 .x6,
    .AUIPC .x7 (laHi GuestAddrs.aps_empty_root (GuestAddrs.account_apply_storage_slot_acc + 136)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aps_empty_root (GuestAddrs.account_apply_storage_slot_acc + 136)),
    .LI .x28 (32 : Word),
    .BEQ .x28 .x0 (32 : BitVec 13),
    .LBU .x29 .x6 (0 : BitVec 12),
    .LBU .x30 .x7 (0 : BitVec 12),
    .BNE .x29 .x30 (52 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .BEQ .x20 .x0 (552 : BitVec 13),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x20,
    .AUIPC .x13 (laHi GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 196)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 196)),
    .JAL .x1 (jalOff GuestAddrs.storage_root_single_slot (GuestAddrs.account_apply_storage_slot_acc + 204)),
    .JAL .x0 (336 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 212)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (536 : BitVec 13),
    .BEQ .x20 .x0 (356 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.srss_rlpval (GuestAddrs.account_apply_storage_slot_acc + 240)),
    .ADDI .x12 .x12 (laLo GuestAddrs.srss_rlpval (GuestAddrs.account_apply_storage_slot_acc + 240)),
    .AUIPC .x13 (laHi GuestAddrs.srss_rlpval_len (GuestAddrs.account_apply_storage_slot_acc + 248)),
    .ADDI .x13 .x13 (laLo GuestAddrs.srss_rlpval_len (GuestAddrs.account_apply_storage_slot_acc + 248)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.account_apply_storage_slot_acc + 256)),
    .MV .x10 .x18,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 268)),
    .ADDI .x12 .x12 (laLo GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 268)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.account_apply_storage_slot_acc + 276)),
    .AUIPC .x10 (laHi GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 280)),
    .ADDI .x10 .x10 (laLo GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 280)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 292)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 292)),
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.account_apply_storage_slot_acc + 300)),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_count (GuestAddrs.account_apply_storage_slot_acc + 304)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_count (GuestAddrs.account_apply_storage_slot_acc + 304)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_data (GuestAddrs.account_apply_storage_slot_acc + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_data (GuestAddrs.account_apply_storage_slot_acc + 316)),
    .AUIPC .x6 (laHi GuestAddrs.mset_db_top (GuestAddrs.account_apply_storage_slot_acc + 324)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_top (GuestAddrs.account_apply_storage_slot_acc + 324)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 336)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 336)),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x5,
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 352)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 352)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_len (GuestAddrs.account_apply_storage_slot_acc + 364)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_len (GuestAddrs.account_apply_storage_slot_acc + 364)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 376)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 376)),
    .LI .x14 (64 : Word),
    .AUIPC .x15 (laHi GuestAddrs.srss_rlpval (GuestAddrs.account_apply_storage_slot_acc + 388)),
    .ADDI .x15 .x15 (laLo GuestAddrs.srss_rlpval (GuestAddrs.account_apply_storage_slot_acc + 388)),
    .AUIPC .x5 (laHi GuestAddrs.srss_rlpval_len (GuestAddrs.account_apply_storage_slot_acc + 396)),
    .ADDI .x5 .x5 (laLo GuestAddrs.srss_rlpval_len (GuestAddrs.account_apply_storage_slot_acc + 396)),
    .LD .x16 .x5 (0 : BitVec 12),
    .AUIPC .x17 (laHi GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 408)),
    .ADDI .x17 .x17 (laLo GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 408)),
    .JAL .x1 (jalOff GuestAddrs.mpt_set_acc (GuestAddrs.account_apply_storage_slot_acc + 416)),
    .BEQ .x10 .x0 (124 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_count (GuestAddrs.account_apply_storage_slot_acc + 424)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_count (GuestAddrs.account_apply_storage_slot_acc + 424)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_data (GuestAddrs.account_apply_storage_slot_acc + 436)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_data (GuestAddrs.account_apply_storage_slot_acc + 436)),
    .AUIPC .x6 (laHi GuestAddrs.mset_db_top (GuestAddrs.account_apply_storage_slot_acc + 444)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_top (GuestAddrs.account_apply_storage_slot_acc + 444)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 456)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 456)),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x5,
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 472)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 472)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_len (GuestAddrs.account_apply_storage_slot_acc + 484)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_len (GuestAddrs.account_apply_storage_slot_acc + 484)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 496)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 496)),
    .LI .x14 (64 : Word),
    .AUIPC .x15 (laHi GuestAddrs.srss_rlpval (GuestAddrs.account_apply_storage_slot_acc + 508)),
    .ADDI .x15 .x15 (laLo GuestAddrs.srss_rlpval (GuestAddrs.account_apply_storage_slot_acc + 508)),
    .AUIPC .x5 (laHi GuestAddrs.srss_rlpval_len (GuestAddrs.account_apply_storage_slot_acc + 516)),
    .ADDI .x5 .x5 (laLo GuestAddrs.srss_rlpval_len (GuestAddrs.account_apply_storage_slot_acc + 516)),
    .LD .x16 .x5 (0 : BitVec 12),
    .AUIPC .x17 (laHi GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 528)),
    .ADDI .x17 .x17 (laLo GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 528)),
    .JAL .x1 (jalOff GuestAddrs.mpt_insert_acc (GuestAddrs.account_apply_storage_slot_acc + 536)),
    .BNE .x10 .x0 (220 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 552)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 552)),
    .MV .x13 .x21,
    .MV .x14 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_set_storage_root (GuestAddrs.account_apply_storage_slot_acc + 568)),
    .BNE .x10 .x0 (196 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (192 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 592)),
    .ADDI .x12 .x12 (laLo GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 592)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.account_apply_storage_slot_acc + 600)),
    .AUIPC .x10 (laHi GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 604)),
    .ADDI .x10 .x10 (laLo GuestAddrs.srss_key (GuestAddrs.account_apply_storage_slot_acc + 604)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 616)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 616)),
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.account_apply_storage_slot_acc + 624)),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_count (GuestAddrs.account_apply_storage_slot_acc + 628)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_count (GuestAddrs.account_apply_storage_slot_acc + 628)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_data (GuestAddrs.account_apply_storage_slot_acc + 640)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_data (GuestAddrs.account_apply_storage_slot_acc + 640)),
    .AUIPC .x6 (laHi GuestAddrs.mset_db_top (GuestAddrs.account_apply_storage_slot_acc + 648)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_top (GuestAddrs.account_apply_storage_slot_acc + 648)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 660)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_off (GuestAddrs.account_apply_storage_slot_acc + 660)),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x5,
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 676)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_ptr (GuestAddrs.account_apply_storage_slot_acc + 676)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.aps_witness_len (GuestAddrs.account_apply_storage_slot_acc + 688)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aps_witness_len (GuestAddrs.account_apply_storage_slot_acc + 688)),
    .LD .x12 .x5 (0 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 700)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aps_path (GuestAddrs.account_apply_storage_slot_acc + 700)),
    .LI .x14 (64 : Word),
    .AUIPC .x17 (laHi GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 712)),
    .ADDI .x17 .x17 (laLo GuestAddrs.aps_newsroot (GuestAddrs.account_apply_storage_slot_acc + 712)),
    .JAL .x1 (jalOff GuestAddrs.mpt_delete_acc (GuestAddrs.account_apply_storage_slot_acc + 720)),
    .BEQ .x10 .x0 (-180 : BitVec 13),
    .JAL .x0 (32 : BitVec 21),
    .MV .x10 .x21,
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.account_apply_storage_slot_acc + 744)),
    .SD .x22 .x9 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountApplyStorageSlotAcc_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountApplyStorageSlotAcc_relocs : RelocTable :=
  [ (19, .la .x13 "aps_off"),
    (21, .la .x14 "aps_len"),
    (23, .jal .x1 "rlp_list_nth_item"),
    (25, .la .x5 "aps_len"),
    (30, .la .x5 "aps_off"),
    (34, .la .x7 "aps_empty_root"),
    (49, .la .x13 "aps_newsroot"),
    (51, .jal .x1 "storage_root_single_slot"),
    (53, .la .x5 "aps_witness_ptr"),
    (60, .la .x12 "srss_rlpval"),
    (62, .la .x13 "srss_rlpval_len"),
    (64, .jal .x1 "rlp_encode_bytes"),
    (67, .la .x12 "srss_key"),
    (69, .jal .x1 "zkvm_keccak256"),
    (70, .la .x10 "srss_key"),
    (73, .la .x12 "aps_path"),
    (75, .jal .x1 "bytes_to_nibbles"),
    (76, .la .x5 "mset_db_count"),
    (79, .la .x5 "mset_db_data"),
    (81, .la .x6 "mset_db_top"),
    (84, .la .x5 "aps_off"),
    (88, .la .x5 "aps_witness_ptr"),
    (91, .la .x5 "aps_witness_len"),
    (94, .la .x13 "aps_path"),
    (97, .la .x15 "srss_rlpval"),
    (99, .la .x5 "srss_rlpval_len"),
    (102, .la .x17 "aps_newsroot"),
    (104, .jal .x1 "mpt_set_acc"),
    (106, .la .x5 "mset_db_count"),
    (109, .la .x5 "mset_db_data"),
    (111, .la .x6 "mset_db_top"),
    (114, .la .x5 "aps_off"),
    (118, .la .x5 "aps_witness_ptr"),
    (121, .la .x5 "aps_witness_len"),
    (124, .la .x13 "aps_path"),
    (127, .la .x15 "srss_rlpval"),
    (129, .la .x5 "srss_rlpval_len"),
    (132, .la .x17 "aps_newsroot"),
    (134, .jal .x1 "mpt_insert_acc"),
    (138, .la .x12 "aps_newsroot"),
    (142, .jal .x1 "account_set_storage_root"),
    (148, .la .x12 "srss_key"),
    (150, .jal .x1 "zkvm_keccak256"),
    (151, .la .x10 "srss_key"),
    (154, .la .x12 "aps_path"),
    (156, .jal .x1 "bytes_to_nibbles"),
    (157, .la .x5 "mset_db_count"),
    (160, .la .x5 "mset_db_data"),
    (162, .la .x6 "mset_db_top"),
    (165, .la .x5 "aps_off"),
    (169, .la .x5 "aps_witness_ptr"),
    (172, .la .x5 "aps_witness_len"),
    (175, .la .x13 "aps_path"),
    (178, .la .x17 "aps_newsroot"),
    (180, .jal .x1 "mpt_delete_acc"),
    (186, .jal .x1 "mset_memcpy") ]

def accountApplyStorageSlotAccFunction : String :=
  "account_apply_storage_slot_acc:\n" ++ emitProgramR accountApplyStorageSlotAcc_prog accountApplyStorageSlotAcc_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountApplyStorageSlotAcc_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountApplyStorageSlotAccFunction_eq_prog :
    accountApplyStorageSlotAccFunction = "account_apply_storage_slot_acc:\n" ++ emitProgramR accountApplyStorageSlotAcc_prog accountApplyStorageSlotAcc_relocs := rfl

#guard accountApplyStorageSlotAccFunction.startsWith "account_apply_storage_slot_acc:\n"
#guard accountApplyStorageSlotAcc_prog.length = 203
/-! ### zisk_account_apply_storage_slot probe.
    Input (file -> INPUT+8): file[0:8]=account_len, file[8:16]=value_len,
      file[16:48]=slot_key(32B), file[48:80]=value(<=32B), file[128:]=account RLP.
    Output: OUTPUT+0=status, OUTPUT+8=out_len, OUTPUT+16=new account RLP. -/
def ziskAccountApplyStorageSlotPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a4, 16(t0)               # value_len\n" ++
  "  addi a2, t0, 24             # slot_key\n" ++
  "  addi a3, t0, 56             # value\n" ++
  "  addi a0, t0, 136            # account RLP\n" ++
  "  la a5, aps_out; la a6, aps_out_len\n" ++
  "  jal ra, account_apply_storage_slot\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  la t1, aps_out_len; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, aps_out; addi t0, t0, 16; li t3, 0\n" ++
  ".Lapsp_cp:\n" ++
  "  beq t3, t2, .Lapsp_done\n" ++
  "  add t4, t1, t3; lbu t5, 0(t4); add t6, t0, t3; sb t5, 0(t6)\n" ++
  "  addi t3, t3, 1; j .Lapsp_cp\n" ++
  ".Lapsp_done:\n" ++
  "  j .Laps_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  ".Laps_pdone:"

def ziskAccountApplyStorageSlotDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
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
  ".balign 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "mset_span_start:\n  .zero 8\n" ++
  "mset_span_size:\n  .zero 8\n" ++
  "mset_payload_start:\n  .zero 8\n" ++
  "mset_head_len:\n  .zero 8\n" ++
  "mset_tail_start:\n  .zero 8\n" ++
  "mset_tail_len:\n  .zero 8\n" ++
  "mset_new_payload_len:\n  .zero 8\n" ++
  "mset_prefix_len:\n  .zero 8\n" ++
  "mset_cursor:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  "aps_out_len:\n  .zero 8\n" ++
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
  "aps_out:\n  .zero 256"

def ziskAccountApplyStorageSlotProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountApplyStorageSlotPrologue
  dataAsm     := ziskAccountApplyStorageSlotDataSection
}

end EvmAsm.Codegen
