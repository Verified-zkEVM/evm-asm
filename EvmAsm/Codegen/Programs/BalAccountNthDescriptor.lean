/-
  EvmAsm.Codegen.Programs.BalAccountNthDescriptor

  Adapter from a BAL AccountChanges list to one `mpt_state_root_ins` descriptor.
  The caller supplies the pre-state account RLP for the selected account and the
  insert/modify flag; this helper extracts the N-th BAL item and delegates to
  `bal_account_change_descriptor`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalAccountChangeDescriptor

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_nth_descriptor -- BAL list item -> MPT descriptor

    a0 = BAL AccountChanges list ptr   a1 = BAL AccountChanges list length
    a2 = index N                       a3 = account RLP ptr
    a4 = account RLP length            a5 = is_insert flag
    a6 = descriptor out ptr            a7 = path out ptr
    baan_value_out is the account value output buffer.
    a0 (output) = 0 ok / 1 failure.

    This helper is intentionally per-item: the replay driver can decide account
    existence and accumulation policy, then call this to build the descriptor for
    the selected BAL account change. -/
def balAccountNthDescriptorFunction : String :=
  "bal_account_nth_descriptor:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # BAL list ptr\n" ++
  "  mv s1, a1                   # BAL list len\n" ++
  "  mv s8, a2                   # target index\n" ++
  "  mv s2, a3                   # account ptr\n" ++
  "  mv s3, a4                   # account len\n" ++
  "  mv s4, a5                   # is_insert\n" ++
  "  mv s5, a6                   # descriptor out\n" ++
  "  mv s6, a7                   # path out\n" ++
  "  la s7, baan_value_out       # value out\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbaan_fail\n" ++
  "  mv s9, a0                   # cursor\n" ++
  "  mv s10, a1                  # end\n" ++
  "  li s11, 0                   # i\n" ++
  ".Lbaan_walk:\n" ++
  "  mv a0, s9; mv a1, s10; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbaan_fail\n" ++
  "  mv s9, a0\n" ++
  "  beq s11, s8, .Lbaan_found\n" ++
  "  addi s11, s11, 1\n" ++
  "  j .Lbaan_walk\n" ++
  ".Lbaan_found:\n" ++
  "  mv t0, a2; sub a2, a0, t0; mv a3, t0\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  mv a4, s4; mv a5, s5; mv a6, s6; mv a7, s7\n" ++
  "  jal ra, bal_account_change_descriptor\n" ++
  "  j .Lbaan_ret\n" ++
  ".Lbaan_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbaan_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_bal_account_nth_descriptor`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account RLP length (u64)
      +16 BAL list length (u64)
      +24 index N (u64)
      +32 is_insert flag (u64)
      +40 account RLP bytes, padded to 8 bytes
      then BAL AccountChanges list bytes
    Output layout:
      OUTPUT+0   : status
      OUTPUT+8   : descriptor (40 bytes)
      OUTPUT+48  : path bytes (64 bytes)
      OUTPUT+112 : post account RLP bytes
      OUTPUT+248 : duplicate status -/
def ziskBalAccountNthDescriptorPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a4, 8(t0)                # account_len\n" ++
  "  ld a1, 16(t0)               # BAL list len\n" ++
  "  ld a2, 24(t0)               # index\n" ++
  "  ld a5, 32(t0)               # is_insert\n" ++
  "  addi a3, t0, 40             # account ptr\n" ++
  "  add a0, a3, a4              # BAL list ptr after padded account\n" ++
  "  addi a0, a0, 7; andi a0, a0, -8\n" ++
  "  li a6, 0xa0010008           # descriptor at OUTPUT+8\n" ++
  "  li a7, 0xa0010030           # path at OUTPUT+48\n" ++
  "  jal ra, bal_account_nth_descriptor\n" ++
  "  mv t6, a0\n" ++
  "  bnez t6, .Lbaan_store_status\n" ++
  "  li t0, 0xa0010008; ld a1, 16(t0); ld a2, 24(t0)\n" ++
  "  li a0, 0xa0010070; jal ra, mset_memcpy\n" ++
  ".Lbaan_store_status:\n" ++
  "  mv a0, t6\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)\n" ++
  "  j .Lbaan_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountNthDescriptorFunction ++ "\n" ++
  ".Lbaan_pdone:"

def ziskBalAccountNthDescriptorDataSection : String :=
  ziskBalAccountChangeDescriptorDataSection ++ "\n" ++
  ".balign 8\n" ++
  "baan_value_out:\n  .zero 512\n" ++
  "baan_pad:\n  .zero 8"

def ziskBalAccountNthDescriptorProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountNthDescriptorPrologue
  dataAsm     := ziskBalAccountNthDescriptorDataSection
}

end EvmAsm.Codegen
