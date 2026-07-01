/-
  EvmAsm.Codegen.Programs.BalAccountChangeValue

  Prepare one BAL account change for state-root replay: derive the world-state
  trie path from the AccountChanges address and rewrite the account RLP with the
  final nonce/balance post-values carried by the BAL item.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalAccountPath
import EvmAsm.Codegen.Programs.BalAccountApplyPostFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_change_value -- pre account + BAL item -> path + post value

    a0 = account RLP ptr        a1 = account RLP length
    a2 = AccountChanges ptr     a3 = AccountChanges length
    a4 = out path ptr (64 bytes, one nibble each)
    a5 = out account RLP ptr    a6 = u64 out account RLP length ptr
    a0 (output) = 0 ok / 1 path/apply failure.

    The output `(path, account_value)` is the pair needed for a MODIFY change
    descriptor in `mpt_state_root_ins`; an external caller still decides whether
    the account is an insert or modify from the pre-state witness walk. -/
def balAccountChangeValueFunction : String :=
  "bal_account_change_value:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # account ptr\n" ++
  "  mv s1, a1                   # account len\n" ++
  "  mv s2, a2                   # AccountChanges ptr\n" ++
  "  mv s3, a3                   # AccountChanges len\n" ++
  "  mv s4, a4                   # out path ptr\n" ++
  "  mv s5, a5                   # out account ptr\n" ++
  "  mv s6, a6                   # out account len ptr\n" ++
  "  la t0, bacv_fail_code; sd zero, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s4\n" ++
  "  jal ra, bal_account_path\n" ++
  "  bnez a0, .Lbacv_fail_path\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s5; mv a5, s6\n" ++
  "  jal ra, bal_account_apply_post_fields\n" ++
  "  bnez a0, .Lbacv_fail_apply\n" ++
  "  j .Lbacv_ret\n" ++
  ".Lbacv_fail_path:\n" ++
  "  li t0, 401; la t1, bacv_fail_code; sd t0, 0(t1)\n" ++
  "  li a0, 1\n" ++
  "  j .Lbacv_ret\n" ++
  ".Lbacv_fail_apply:\n" ++
  "  li t0, 402; la t1, bacv_fail_code; sd t0, 0(t1)\n" ++
  "  li a0, 1\n" ++
  ".Lbacv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_bal_account_change_value`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account RLP length (u64)
      +16 AccountChanges RLP length (u64)
      +24 account RLP bytes, padded to 8 bytes
      then AccountChanges RLP bytes
    Output layout:
      OUTPUT+0   : status
      OUTPUT+8   : path (64 nibble bytes)
      OUTPUT+72  : post account RLP length
      OUTPUT+80  : post account RLP bytes
      OUTPUT+248 : duplicate status -/
def ziskBalAccountChangeValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a3, 16(t0)               # AccountChanges len\n" ++
  "  addi a0, t0, 24             # account ptr\n" ++
  "  add a2, a0, a1              # AccountChanges ptr after padded account\n" ++
  "  addi a2, a2, 7; andi a2, a2, -8\n" ++
  "  li a4, 0xa0010008           # path at OUTPUT+8\n" ++
  "  li a5, 0xa0010050           # account value at OUTPUT+80\n" ++
  "  li a6, 0xa0010048           # account value length at OUTPUT+72\n" ++
  "  jal ra, bal_account_change_value\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)\n" ++
  "  j .Lbacv_pdone\n" ++
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
  ".Lbacv_pdone:"

def ziskBalAccountChangeValueDataSection : String :=
  ziskBalAccountApplyPostFieldsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bacv_fail_code:\n  .zero 8\n" ++
  "bacv_out_pad:\n  .zero 8"
def ziskBalAccountChangeValueProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountChangeValuePrologue
  dataAsm     := ziskBalAccountChangeValueDataSection
}

end EvmAsm.Codegen
