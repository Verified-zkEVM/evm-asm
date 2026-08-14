/-
  EvmAsm.Codegen.Programs.StorageWrite

  Storage-trie write primitives for modeling the per-block SYSTEM-contract state
  updates (EIP-2935 history, EIP-4788 beacon roots) that every Amsterdam block
  applies before withdrawals (bead evm-asm-fhsxz.2.4.2.5). These are the new
  capability the Step-2 state recompute needs beyond balance credits: update an
  account's STORAGE trie, then re-encode the account with the new storage_root.

  * storage_root_single_slot: the new storage_root of a storage trie that holds
    exactly one slot — key = keccak256(slot_key), value = rlp(minimal-BE word).
    Covers the genesis case (empty prior storage) the EIP-2935/4788 system calls
    hit on the first blocks (slot inserted into an empty storage trie). Multi-slot
    storage needs the general MPT build (separate work) — callers stay conservative.

  * account_set_storage_root: replace field 2 (storageRoot) of an account RLP
    ([nonce, balance, storageRoot, codeHash]) with a new 32-byte root, recomputing
    the outer list prefix. The analog of account_add_balance (which splices field
    1). storageRoot is always a 32-byte string, so the new slot ref is 0xa0 || root.

  Both compose already-verified primitives (single_leaf_trie_root, zkvm_keccak256,
  mpt_splice_slot); all byte work is byte-wise (no-misaligned invariant).
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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## storage_root_single_slot -- storage_root of a 1-slot storage trie.
    a0 = slot_key ptr (32 B)   a1 = value ptr (minimal big-endian word bytes)
    a2 = value byte length     a3 = 32-byte out root ptr
    a0 (output) = 0. -/
def storageRootSingleSlot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi GuestAddrs.srss_rlpval (GuestAddrs.storage_root_single_slot + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.srss_rlpval (GuestAddrs.storage_root_single_slot + 48)),
    .AUIPC .x13 (laHi GuestAddrs.srss_rlpval_len (GuestAddrs.storage_root_single_slot + 56)),
    .ADDI .x13 .x13 (laLo GuestAddrs.srss_rlpval_len (GuestAddrs.storage_root_single_slot + 56)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.storage_root_single_slot + 64)),
    .MV .x10 .x8,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.srss_key (GuestAddrs.storage_root_single_slot + 76)),
    .ADDI .x12 .x12 (laLo GuestAddrs.srss_key (GuestAddrs.storage_root_single_slot + 76)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.storage_root_single_slot + 84)),
    .AUIPC .x10 (laHi GuestAddrs.srss_key (GuestAddrs.storage_root_single_slot + 88)),
    .ADDI .x10 .x10 (laLo GuestAddrs.srss_key (GuestAddrs.storage_root_single_slot + 88)),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.srss_rlpval (GuestAddrs.storage_root_single_slot + 100)),
    .ADDI .x12 .x12 (laLo GuestAddrs.srss_rlpval (GuestAddrs.storage_root_single_slot + 100)),
    .AUIPC .x5 (laHi GuestAddrs.srss_rlpval_len (GuestAddrs.storage_root_single_slot + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.srss_rlpval_len (GuestAddrs.storage_root_single_slot + 108)),
    .LD .x13 .x5 (0 : BitVec 12),
    .MV .x14 .x19,
    .JAL .x1 (jalOff GuestAddrs.single_leaf_trie_root (GuestAddrs.storage_root_single_slot + 124)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `storageRootSingleSlot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def storageRootSingleSlot_relocs : RelocTable :=
  [ (12, .la .x12 "srss_rlpval"),
    (14, .la .x13 "srss_rlpval_len"),
    (16, .jal .x1 "rlp_encode_bytes"),
    (19, .la .x12 "srss_key"),
    (21, .jal .x1 "zkvm_keccak256"),
    (22, .la .x10 "srss_key"),
    (25, .la .x12 "srss_rlpval"),
    (27, .la .x5 "srss_rlpval_len"),
    (31, .jal .x1 "single_leaf_trie_root") ]

def storageRootSingleSlotFunction : String :=
  "storage_root_single_slot:\n" ++ emitProgramR storageRootSingleSlot_prog storageRootSingleSlot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `storageRootSingleSlot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem storageRootSingleSlotFunction_eq_prog :
    storageRootSingleSlotFunction = "storage_root_single_slot:\n" ++ emitProgramR storageRootSingleSlot_prog storageRootSingleSlot_relocs := rfl

#guard storageRootSingleSlotFunction.startsWith "storage_root_single_slot:\n"
/-! ## account_set_storage_root -- replace field 2 (storageRoot) of an account.
    a0 = account RLP ptr   a1 = account RLP length   a2 = new storage_root (32 B)
    a3 = out account RLP ptr   a4 = u64 out length ptr
    a0 (output) = 0 (ok) / 1 (splice parse fail). -/
def accountSetStorageRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.asr_ref (GuestAddrs.account_set_storage_root + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.asr_ref (GuestAddrs.account_set_storage_root + 48)),
    .LI .x6 (160 : Word),
    .SB .x5 .x6 (0 : BitVec 12),
    .LI .x7 (0 : Word),
    .LI .x28 (32 : Word),
    .BEQ .x7 .x28 (32 : BitVec 13),
    .ADD .x29 .x18 .x7,
    .LBU .x30 .x29 (0 : BitVec 12),
    .ADD .x31 .x5 .x7,
    .ADDI .x31 .x31 (1 : BitVec 12),
    .SB .x31 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (2 : Word),
    .AUIPC .x13 (laHi GuestAddrs.asr_ref (GuestAddrs.account_set_storage_root + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.asr_ref (GuestAddrs.account_set_storage_root + 116)),
    .LI .x14 (33 : Word),
    .MV .x15 .x19,
    .MV .x16 .x20,
    .JAL .x1 (jalOff GuestAddrs.mpt_splice_slot (GuestAddrs.account_set_storage_root + 136)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountSetStorageRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountSetStorageRoot_relocs : RelocTable :=
  [ (12, .la .x5 "asr_ref"),
    (29, .la .x13 "asr_ref"),
    (34, .jal .x1 "mpt_splice_slot") ]

def accountSetStorageRootFunction : String :=
  "account_set_storage_root:\n" ++ emitProgramR accountSetStorageRoot_prog accountSetStorageRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountSetStorageRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountSetStorageRootFunction_eq_prog :
    accountSetStorageRootFunction = "account_set_storage_root:\n" ++ emitProgramR accountSetStorageRoot_prog accountSetStorageRoot_relocs := rfl

#guard accountSetStorageRootFunction.startsWith "account_set_storage_root:\n"
/-! ### zisk_storage_root_single_slot probe.
    Input (-> INPUT+8): +8 value_len; +16 slot_key (32 B); +48 value bytes.
    Output: OUTPUT+0 = 32-byte storage root. -/
def ziskStorageRootSingleSlotPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a2, 8(a5)                # value_len\n" ++
  "  addi a0, a5, 16             # slot_key ptr\n" ++
  "  addi a1, a5, 48             # value ptr\n" ++
  "  li a3, 0xa0010000           # out root\n" ++
  "  jal ra, storage_root_single_slot\n" ++
  "  j .Lsrss_pdone\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  ".Lsrss_pdone:"

def ziskStorageRootSingleSlotDataSection : String :=
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
  "srss_rlpval_len:\n  .zero 8"


/-! ### zisk_account_set_storage_root probe.
    Input (-> INPUT+8): +8 account_len; +16 new storage_root (32 B); +48 account RLP.
    Output: OUTPUT+0 = out_len (u64); OUTPUT+8 = new account RLP. -/
def ziskAccountSetStorageRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # account_len\n" ++
  "  addi a2, a5, 16             # new storage_root ptr\n" ++
  "  addi a0, a5, 48             # account RLP ptr\n" ++
  "  la a3, asr_out; la a4, asr_out_len\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, asr_out_len; ld t2, 0(t1); sd t2, 0(t0)   # out_len at OUTPUT+0\n" ++
  "  la t1, asr_out; addi t0, t0, 8; li t3, 0\n" ++
  ".Lasrp_cp:\n" ++
  "  beq t3, t2, .Lasrp_done\n" ++
  "  add t4, t1, t3; lbu t5, 0(t4); add t6, t0, t3; sb t5, 0(t6)\n" ++
  "  addi t3, t3, 1; j .Lasrp_cp\n" ++
  ".Lasrp_done:\n" ++
  "  j .Lasr_pdone\n" ++
  msetMemcpyFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  ".Lasr_pdone:"

def ziskAccountSetStorageRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "asr_out_len:\n  .zero 8\n" ++
  "asr_out:\n  .zero 256\n" ++
  -- mpt_splice_slot scratch (mirrors the MptSet probe data section):
  ".balign 8\n" ++
  "mset_span_start:\n  .zero 8\n" ++
  "mset_span_size:\n  .zero 8\n" ++
  "mset_payload_start:\n  .zero 8\n" ++
  "mset_head_len:\n  .zero 8\n" ++
  "mset_tail_start:\n  .zero 8\n" ++
  "mset_tail_len:\n  .zero 8\n" ++
  "mset_new_payload_len:\n  .zero 8\n" ++
  "mset_prefix_len:\n  .zero 8\n" ++
  "mset_cursor:\n  .zero 8"


end EvmAsm.Codegen
