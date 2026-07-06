/-
  EvmAsm.Codegen.Programs.WithdrawalsStateRoot

  withdrawals_state_root (bead evm-asm-fhsxz.2.2): the computational heart of
  the Step-2 verdict — recompute the post-state MPT root after applying a
  block's withdrawal balance credits. This is what lets the stateless guest
  set successful_validation for withdrawal-only valid blocks.

  Pipeline (composes already-verified primitives; CHANGE-LIST design):
    for each withdrawal:
      1. withdrawal_to_path_delta  -> state-trie path (keccak(addr) nibbles)
                                      + wei delta (amount_gwei * 1e9)
      2. mpt_walk (over the PRE-state witness) -> the current account RLP
      3. account_add_balance(account, delta)  -> the new account RLP
      record (path, new_account_rlp) into a change list;
    mpt_state_root(root, witness, changes) -> post-state root.

  Reading each account from the PRE-state and applying all changes via
  mpt_state_root is SOUND: distinct recipients (the common case) are exact;
  if a block credited the SAME account twice, the second change would shadow
  the first, yielding a wrong root -> the verdict's memcmp fails -> x11 stays
  0 (a conservative MISS, never a false-positive). A withdrawal to a
  non-existent account needs an INSERT (out of the value-only engine's scope)
  -> returns status 1 so the verdict leaves x11 = 0.

  All multi-byte work is on 8-aligned scratch; node/account bytes are read
  byte-wise (no-misaligned invariant). The function/scratch bundle is the
  union of the mpt_state_root, mpt_walk, withdrawal_to_path_delta, and
  account_add_balance closures (all label-disjoint).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.Withdrawal
import EvmAsm.Codegen.Programs.WithdrawalPath

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## withdrawals_state_root -- post-state root after withdrawal credits

    a0 = pre-state root hash ptr (32 B)
    a1 = witness ptr            a2 = witness length
    a3 = withdrawals descriptor array ptr (per entry: wd_rlp_ptr:u64,
         wd_rlp_len:u64 — 16 B each)
    a4 = n_withdrawals          a5 = out_root ptr (32 B)
    a0 (output) = 0 ok / 1 a withdrawal targets a non-existent account
                  (insert needed, unsupported) / 2 parse/encode failure -/
def withdrawalsStateRoot_prog : Program :=
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
    .LI .x22 (0 : Word),
    .BEQ .x22 .x20 (256 : BitVec 13),
    .SLLI .x5 .x22 (4 : BitVec 6),
    .ADD .x5 .x19 .x5,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.ws_path (GuestAddrs.withdrawals_state_root + 84)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ws_path (GuestAddrs.withdrawals_state_root + 84)),
    .SLLI .x7 .x22 (6 : BitVec 6),
    .ADD .x12 .x6 .x7,
    .AUIPC .x13 (laHi GuestAddrs.ws_delta (GuestAddrs.withdrawals_state_root + 100)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ws_delta (GuestAddrs.withdrawals_state_root + 100)),
    .JAL .x1 (jalOff GuestAddrs.withdrawal_to_path_delta (GuestAddrs.withdrawals_state_root + 108)),
    .BNE .x10 .x0 (252 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x6 (laHi GuestAddrs.ws_path (GuestAddrs.withdrawals_state_root + 128)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ws_path (GuestAddrs.withdrawals_state_root + 128)),
    .SLLI .x7 .x22 (6 : BitVec 6),
    .ADD .x13 .x6 .x7,
    .LI .x14 (64 : Word),
    .AUIPC .x15 (laHi GuestAddrs.ws_acct (GuestAddrs.withdrawals_state_root + 148)),
    .ADDI .x15 .x15 (laLo GuestAddrs.ws_acct (GuestAddrs.withdrawals_state_root + 148)),
    .AUIPC .x16 (laHi GuestAddrs.ws_acct_len (GuestAddrs.withdrawals_state_root + 156)),
    .ADDI .x16 .x16 (laLo GuestAddrs.ws_acct_len (GuestAddrs.withdrawals_state_root + 156)),
    .JAL .x1 (jalOff GuestAddrs.mpt_walk (GuestAddrs.withdrawals_state_root + 164)),
    .BNE .x10 .x0 (188 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.ws_acct (GuestAddrs.withdrawals_state_root + 172)),
    .ADDI .x10 .x10 (laLo GuestAddrs.ws_acct (GuestAddrs.withdrawals_state_root + 172)),
    .AUIPC .x5 (laHi GuestAddrs.ws_acct_len (GuestAddrs.withdrawals_state_root + 180)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ws_acct_len (GuestAddrs.withdrawals_state_root + 180)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.ws_delta (GuestAddrs.withdrawals_state_root + 192)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ws_delta (GuestAddrs.withdrawals_state_root + 192)),
    .AUIPC .x6 (laHi GuestAddrs.ws_newacct (GuestAddrs.withdrawals_state_root + 200)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ws_newacct (GuestAddrs.withdrawals_state_root + 200)),
    .SLLI .x7 .x22 (7 : BitVec 6),
    .ADD .x13 .x6 .x7,
    .AUIPC .x14 (laHi GuestAddrs.ws_newacct_len (GuestAddrs.withdrawals_state_root + 216)),
    .ADDI .x14 .x14 (laLo GuestAddrs.ws_newacct_len (GuestAddrs.withdrawals_state_root + 216)),
    .JAL .x1 (jalOff GuestAddrs.account_add_balance (GuestAddrs.withdrawals_state_root + 224)),
    .BNE .x10 .x0 (136 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.ws_changes (GuestAddrs.withdrawals_state_root + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ws_changes (GuestAddrs.withdrawals_state_root + 232)),
    .SLLI .x6 .x22 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x6 (laHi GuestAddrs.ws_path (GuestAddrs.withdrawals_state_root + 248)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ws_path (GuestAddrs.withdrawals_state_root + 248)),
    .SLLI .x7 .x22 (6 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x6 (64 : Word),
    .SD .x5 .x6 (8 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.ws_newacct (GuestAddrs.withdrawals_state_root + 276)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ws_newacct (GuestAddrs.withdrawals_state_root + 276)),
    .SLLI .x7 .x22 (7 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .SD .x5 .x6 (16 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.ws_newacct_len (GuestAddrs.withdrawals_state_root + 296)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ws_newacct_len (GuestAddrs.withdrawals_state_root + 296)),
    .LD .x6 .x6 (0 : BitVec 12),
    .SD .x5 .x6 (24 : BitVec 12),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-252 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.ws_changes (GuestAddrs.withdrawals_state_root + 332)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ws_changes (GuestAddrs.withdrawals_state_root + 332)),
    .MV .x14 .x20,
    .MV .x15 .x21,
    .JAL .x1 (jalOff GuestAddrs.mpt_state_root (GuestAddrs.withdrawals_state_root + 348)),
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

/-- Reloc side-table for `withdrawalsStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def withdrawalsStateRoot_relocs : RelocTable :=
  [ (21, .la .x6 "ws_path"),
    (25, .la .x13 "ws_delta"),
    (27, .jal .x1 "withdrawal_to_path_delta"),
    (32, .la .x6 "ws_path"),
    (37, .la .x15 "ws_acct"),
    (39, .la .x16 "ws_acct_len"),
    (41, .jal .x1 "mpt_walk"),
    (43, .la .x10 "ws_acct"),
    (45, .la .x5 "ws_acct_len"),
    (48, .la .x12 "ws_delta"),
    (50, .la .x6 "ws_newacct"),
    (54, .la .x14 "ws_newacct_len"),
    (56, .jal .x1 "account_add_balance"),
    (58, .la .x5 "ws_changes"),
    (62, .la .x6 "ws_path"),
    (69, .la .x6 "ws_newacct"),
    (74, .la .x6 "ws_newacct_len"),
    (83, .la .x13 "ws_changes"),
    (87, .jal .x1 "mpt_state_root") ]

def withdrawalsStateRootFunction : String :=
  "withdrawals_state_root:\n" ++ emitProgramR withdrawalsStateRoot_prog withdrawalsStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `withdrawalsStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem withdrawalsStateRootFunction_eq_prog :
    withdrawalsStateRootFunction = "withdrawals_state_root:\n" ++ emitProgramR withdrawalsStateRoot_prog withdrawalsStateRoot_relocs := rfl

#guard withdrawalsStateRootFunction.startsWith "withdrawals_state_root:\n"
#guard withdrawalsStateRoot_prog.length = 102
/-- `zisk_withdrawals_state_root`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness_len (u64)       +16 n_withdrawals (u64)
      +24 pre-state root hash (32 B)
      +56 withdrawal RLP length table: N x u64
      +56+8N : withdrawal RLP blobs (each 8-aligned), then witness section.
    The prologue builds the 16-byte (ptr,len) descriptor array (ws_wds) from
    the length table + a running blob cursor, then calls withdrawals_state_root.
    Output: OUTPUT+0 = post-state root (32 B); OUTPUT+32 = status. -/
def ziskWithdrawalsStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # n_withdrawals\n" ++
  "  addi a0, t0, 24             # root hash ptr\n" ++
  "  slli t1, a4, 3              # 8 * N (length table size)\n" ++
  "  addi t2, t0, 56             # table base\n" ++
  "  add t3, t2, t1              # blob cursor\n" ++
  "  la t4, ws_wds               # descriptor dst\n" ++
  "  li t5, 0\n" ++
  ".Lwsrp_build:\n" ++
  "  beq t5, a4, .Lwsrp_done\n" ++
  "  slli t6, t5, 3; add t6, t2, t6   # &table[i]\n" ++
  "  ld a5, 0(t6)                # wd_rlp_len\n" ++
  "  sd t3, 0(t4)                # desc.ptr\n" ++
  "  sd a5, 8(t4)                # desc.len\n" ++
  "  addi a3, a5, 7; andi a3, a3, -8; add t3, t3, a3   # cursor += roundup8(len)\n" ++
  "  addi t4, t4, 16\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Lwsrp_build\n" ++
  ".Lwsrp_done:\n" ++
  "  mv a1, t3                   # witness ptr (after last blob)\n" ++
  "  la a3, ws_wds\n" ++
  "  li a5, 0xa0010000           # out_root at OUTPUT+0\n" ++
  "  jal ra, withdrawals_state_root\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)   # status at OUTPUT+32\n" ++
  "  j .Lwsr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalToPathDeltaFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptStateRootFunction ++ "\n" ++
  withdrawalsStateRootFunction ++ "\n" ++
  ".Lwsr_pdone:"

/-- Data section: the mpt_state_root scratch (`ziskMptStateRootDataSection`,
    which already covers the mpt_walk / record-walk / splice / leaf-encode /
    keccak scratch) plus the disjoint withdrawal-decode, Gwei->wei,
    account_add_balance, and withdrawals_state_root buffers. -/
def ziskWithdrawalsStateRootDataSection : String :=
  ziskMptStateRootDataSection ++ "\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "wd_offset:\n  .zero 8\n" ++
  "wd_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  ".balign 8\n" ++
  "wtpd_struct:\n  .zero 48\n" ++
  ".balign 32\n" ++
  "wtpd_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_bal_off:\n  .zero 8\n" ++
  "aab_bal_len:\n  .zero 8\n" ++
  "aab_enc_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aab_bal32:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_enc:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ws_acct_len:\n  .zero 8\n" ++
  "ws_newacct_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "ws_delta:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ws_acct:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "ws_wds:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "ws_path:\n  .zero 4096\n" ++
  ".balign 8\n" ++
  "ws_changes:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ws_newacct:\n  .zero 8192"

def ziskWithdrawalsStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalsStateRootPrologue
  dataAsm     := ziskWithdrawalsStateRootDataSection
}

end EvmAsm.Codegen
