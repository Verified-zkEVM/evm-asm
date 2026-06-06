/-
  EvmAsm.Codegen.Programs.BalAccountChangeDescriptor

  Package one BAL account replay item as an `mpt_state_root_ins` change
  descriptor: state-trie path, post account value, value length, and the caller
  supplied insert/modify flag.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
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
    Modes are 0=modify, 1=insert, 2=delete, 3=no-op. Caller flag 4 is
    normalized to mode 0 but asks `bal_account_apply_post_fields` to clear the
    account storage trie before applying this item's post-wipe storage writes. -/
def balAccountChangeDescriptorFunction : String :=
  "bal_account_change_descriptor:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a4                   # is_insert\n" ++
  "  mv s1, a5                   # descriptor out\n" ++
  "  mv s2, a6                   # path out\n" ++
  "  mv s3, a7                   # value out\n" ++
  "  mv s4, a0                   # account ptr\n" ++
  "  mv s5, a1                   # account len\n" ++
  "  mv s6, a2                   # AccountChanges ptr\n" ++
  "  mv s7, a3                   # AccountChanges len\n" ++
  "  la t0, baacd_fail_code; sd zero, 0(t0)\n" ++
  "  la t0, baap_force_storage_clear; sd zero, 0(t0)\n" ++
  "  li t1, 4; bne s0, t1, .Lbaacd_mode_ready\n" ++
  "  li t2, 1; sd t2, 0(t0); li s0, 0 # force storage clear, state-trie MODIFY\n" ++
  ".Lbaacd_mode_ready:\n" ++
  "  mv a0, s4; mv a1, s5; mv a2, s6; mv a3, s7\n" ++
  "  mv a4, s2; mv a5, s3; la a6, baacd_value_len\n" ++
  "  jal ra, bal_account_change_value\n" ++
  "  bnez a0, .Lbaacd_fail_value\n" ++
  "  mv a0, s3; la t0, baacd_value_len; ld a1, 0(t0); la a2, baacd_is_empty\n" ++
  "  jal ra, account_is_eip161_empty\n" ++
  "  bnez a0, .Lbaacd_fail_value\n" ++
  "  la t0, baacd_is_empty; ld t0, 0(t0); beqz t0, .Lbaacd_have_mode\n" ++
  "  beqz s0, .Lbaacd_delete_empty\n" ++
  "  li s0, 3                    # absent account remained empty: no-op\n" ++
  "  j .Lbaacd_have_mode\n" ++
  ".Lbaacd_delete_empty:\n" ++
  "  li s0, 2                    # existing account became empty: delete leaf\n" ++
  ".Lbaacd_have_mode:\n" ++
  "  sd s2, 0(s1)\n" ++
  "  li t0, 64; sd t0, 8(s1)\n" ++
  "  sd s3, 16(s1)\n" ++
  "  la t0, baacd_value_len; ld t0, 0(t0); sd t0, 24(s1)\n" ++
  "  sd s0, 32(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbaacd_ret\n" ++
  ".Lbaacd_fail_value:\n" ++
  "  li t0, 301; la t1, baacd_fail_code; sd t0, 0(t1)\n" ++
  ".Lbaacd_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

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
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  ".Lbaacd_pdone:"

def ziskBalAccountChangeDescriptorDataSection : String :=
  ziskBalAccountChangeValueDataSection ++ "\n" ++
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

def ziskBalAccountChangeDescriptorProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountChangeDescriptorPrologue
  dataAsm     := ziskBalAccountChangeDescriptorDataSection
}

end EvmAsm.Codegen
