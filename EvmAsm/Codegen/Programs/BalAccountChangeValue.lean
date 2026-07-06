/-
  EvmAsm.Codegen.Programs.BalAccountChangeValue

  Prepare one BAL account change for state-root replay: derive the world-state
  trie path from the AccountChanges address and rewrite the account RLP with the
  final nonce/balance post-values carried by the BAL item.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def balAccountChangeValue_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
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
    .AUIPC .x5 (laHi GuestAddrs.bacv_fail_code (GuestAddrs.bal_account_change_value + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bacv_fail_code (GuestAddrs.bal_account_change_value + 64)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_account_path (GuestAddrs.bal_account_change_value + 88)),
    .BNE .x10 .x0 (40 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .MV .x13 .x19,
    .MV .x14 .x21,
    .MV .x15 .x22,
    .JAL .x1 (jalOff GuestAddrs.bal_account_apply_post_fields (GuestAddrs.bal_account_change_value + 120)),
    .BNE .x10 .x0 (32 : BitVec 13),
    .JAL .x0 (48 : BitVec 21),
    .LI .x5 (401 : Word),
    .AUIPC .x6 (laHi GuestAddrs.bacv_fail_code (GuestAddrs.bal_account_change_value + 136)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bacv_fail_code (GuestAddrs.bal_account_change_value + 136)),
    .SD .x6 .x5 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x5 (402 : Word),
    .AUIPC .x6 (laHi GuestAddrs.bacv_fail_code (GuestAddrs.bal_account_change_value + 160)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bacv_fail_code (GuestAddrs.bal_account_change_value + 160)),
    .SD .x6 .x5 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountChangeValue_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountChangeValue_relocs : RelocTable :=
  [ (16, .la .x5 "bacv_fail_code"),
    (22, .jal .x1 "bal_account_path"),
    (30, .jal .x1 "bal_account_apply_post_fields"),
    (34, .la .x6 "bacv_fail_code"),
    (40, .la .x6 "bacv_fail_code") ]

def balAccountChangeValueFunction : String :=
  "bal_account_change_value:\n" ++ emitProgramR balAccountChangeValue_prog balAccountChangeValue_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountChangeValue_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountChangeValueFunction_eq_prog :
    balAccountChangeValueFunction = "bal_account_change_value:\n" ++ emitProgramR balAccountChangeValue_prog balAccountChangeValue_relocs := rfl

#guard balAccountChangeValueFunction.startsWith "bal_account_change_value:\n"
#guard balAccountChangeValue_prog.length = 54
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
