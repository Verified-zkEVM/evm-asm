/-
  EvmAsm.Codegen.Programs.BalAccountChangeDescriptor

  Package one BAL account replay item as an `mpt_state_root_ins` change
  descriptor: state-trie path, post account value, value length, and the caller
  supplied insert/modify flag.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AccountFields
import EvmAsm.Codegen.Programs.BalAccountChangeValue

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_change_descriptor -- pre account + BAL item -> MPT descriptor

    a0 = account RLP ptr        a1 = account RLP length
    a2 = AccountChanges ptr     a3 = AccountChanges length
    a4 = is_insert flag         a5 = descriptor out ptr (40 bytes)
    a6 = path out ptr (64 bytes) a7 = account value out ptr
    baacd_value_len receives the post account value length.
    a0 (output) = 0 ok / 1 failure.

    Descriptor layout matches `mpt_state_root_ins`:
      +0 path_ptr | +8 path_len | +16 value_ptr | +24 value_len | +32 mode.
    Modes are 0=modify, 1=insert, 2=delete, 3=no-op. Unknown caller modes are
    passed through so downstream state-root handling fails instead of silently
    normalizing a post-decode marker. -/
def balAccountChangeDescriptor_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x14,
    .MV .x9 .x15,
    .MV .x18 .x16,
    .MV .x19 .x17,
    .MV .x20 .x10,
    .MV .x21 .x11,
    .MV .x22 .x12,
    .MV .x23 .x13,
    .AUIPC .x5 (laHi GuestAddrs.baacd_fail_code (GuestAddrs.bal_account_change_descriptor + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baacd_fail_code (GuestAddrs.bal_account_change_descriptor + 72)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.baap_force_storage_clear (GuestAddrs.bal_account_change_descriptor + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baap_force_storage_clear (GuestAddrs.bal_account_change_descriptor + 84)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .MV .x12 .x22,
    .MV .x13 .x23,
    .MV .x14 .x18,
    .MV .x15 .x19,
    .AUIPC .x16 (laHi GuestAddrs.baacd_value_len (GuestAddrs.bal_account_change_descriptor + 120)),
    .ADDI .x16 .x16 (laLo GuestAddrs.baacd_value_len (GuestAddrs.bal_account_change_descriptor + 120)),
    .JAL .x1 (jalOff GuestAddrs.map_account_change_value (GuestAddrs.bal_account_change_descriptor + 128)),
    .BNE .x10 .x0 (112 : BitVec 13),
    .MV .x10 .x19,
    .AUIPC .x5 (laHi GuestAddrs.baacd_value_len (GuestAddrs.bal_account_change_descriptor + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baacd_value_len (GuestAddrs.bal_account_change_descriptor + 140)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.baacd_is_empty (GuestAddrs.bal_account_change_descriptor + 152)),
    .ADDI .x12 .x12 (laLo GuestAddrs.baacd_is_empty (GuestAddrs.bal_account_change_descriptor + 152)),
    .JAL .x1 (jalOff GuestAddrs.account_is_eip161_empty (GuestAddrs.bal_account_change_descriptor + 160)),
    .BNE .x10 .x0 (80 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.baacd_is_empty (GuestAddrs.bal_account_change_descriptor + 168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baacd_is_empty (GuestAddrs.bal_account_change_descriptor + 168)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (20 : BitVec 13),
    .BEQ .x8 .x0 (12 : BitVec 13),
    .LI .x8 (3 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x8 (2 : Word),
    .SD .x9 .x18 (0 : BitVec 12),
    .LI .x5 (64 : Word),
    .SD .x9 .x5 (8 : BitVec 12),
    .SD .x9 .x19 (16 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.baacd_value_len (GuestAddrs.bal_account_change_descriptor + 216)),
    .ADDI .x5 .x5 (laLo GuestAddrs.baacd_value_len (GuestAddrs.bal_account_change_descriptor + 216)),
    .LD .x5 .x5 (0 : BitVec 12),
    .SD .x9 .x5 (24 : BitVec 12),
    .SD .x9 .x8 (32 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (20 : BitVec 21),
    .LI .x5 (301 : Word),
    .AUIPC .x6 (laHi GuestAddrs.baacd_fail_code (GuestAddrs.bal_account_change_descriptor + 248)),
    .ADDI .x6 .x6 (laLo GuestAddrs.baacd_fail_code (GuestAddrs.bal_account_change_descriptor + 248)),
    .SD .x6 .x5 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountChangeDescriptor_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountChangeDescriptor_relocs : RelocTable :=
  [ (18, .la .x5 "baacd_fail_code"),
    (21, .la .x5 "baap_force_storage_clear"),
    (30, .la .x16 "baacd_value_len"),
    (32, .jal .x1 "map_account_change_value"),
    (35, .la .x5 "baacd_value_len"),
    (38, .la .x12 "baacd_is_empty"),
    (40, .jal .x1 "account_is_eip161_empty"),
    (42, .la .x5 "baacd_is_empty"),
    (54, .la .x5 "baacd_value_len"),
    (62, .la .x6 "baacd_fail_code") ]

def balAccountChangeDescriptorFunction : String :=
  "bal_account_change_descriptor:\n" ++ emitProgramR balAccountChangeDescriptor_prog balAccountChangeDescriptor_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountChangeDescriptor_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountChangeDescriptorFunction_eq_prog :
    balAccountChangeDescriptorFunction = "bal_account_change_descriptor:\n" ++ emitProgramR balAccountChangeDescriptor_prog balAccountChangeDescriptor_relocs := rfl

#guard balAccountChangeDescriptorFunction.startsWith "bal_account_change_descriptor:\n"
/-- `zisk_bal_account_change_descriptor`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account RLP length (u64)
      +16 AccountChanges RLP length (u64)
      +24 is_insert flag (u64)
      +32 account RLP bytes, padded to 8 bytes
      then AccountChanges RLP bytes
    Output layout:
      OUTPUT+0   : status
      OUTPUT+8   : descriptor (40 bytes)
      OUTPUT+48  : path bytes (64 bytes)
      OUTPUT+112 : post account RLP bytes
      OUTPUT+248 : duplicate status -/
def ziskBalAccountChangeDescriptorPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a3, 16(t0)               # AccountChanges len\n" ++
  "  ld a4, 24(t0)               # is_insert\n" ++
  "  addi a0, t0, 32             # account ptr\n" ++
  "  add a2, a0, a1              # AccountChanges ptr after padded account\n" ++
  "  addi a2, a2, 7; andi a2, a2, -8\n" ++
  "  li a5, 0xa0010008           # descriptor at OUTPUT+8\n" ++
  "  li a6, 0xa0010030           # path at OUTPUT+48\n" ++
  "  li a7, 0xa0010070           # value at OUTPUT+112\n" ++
  "  jal ra, bal_account_change_descriptor\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)\n" ++
  "  j .Lbaacd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
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
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  accountApplyStorageSlotAccFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  accountIsEip161EmptyFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  mapAccountApplyPostFieldsFunction ++ "\n" ++
  mapAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  ".Lbaacd_pdone:"

def ziskBalAccountChangeDescriptorDataSection : String :=
  ziskMapAccountChangeValueDataSection ++ "\n" ++
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
  "baacd_pad:\n  .zero 8"


end EvmAsm.Codegen
