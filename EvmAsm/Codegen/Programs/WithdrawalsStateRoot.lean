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
def withdrawalsStateRootFunction : String :=
  "withdrawals_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # pre-state root hash\n" ++
  "  mv s1, a1                   # witness\n" ++
  "  mv s2, a2                   # witness_len\n" ++
  "  mv s3, a3                   # withdrawals descriptors\n" ++
  "  mv s4, a4                   # n_withdrawals\n" ++
  "  mv s5, a5                   # out_root\n" ++
  "  li s6, 0                    # i\n" ++
  ".Lwsr_loop:\n" ++
  "  beq s6, s4, .Lwsr_apply\n" ++
  "  slli t0, s6, 4; add t0, s3, t0    # &wd[i]\n" ++
  "  ld a0, 0(t0)                # wd_rlp ptr\n" ++
  "  ld a1, 8(t0)                # wd_rlp len\n" ++
  "  la t1, ws_path; slli t2, s6, 6; add a2, t1, t2   # path dst = ws_path + 64*i\n" ++
  "  la a3, ws_delta\n" ++
  "  jal ra, withdrawal_to_path_delta\n" ++
  "  bnez a0, .Lwsr_fail\n" ++
  "  # read current account from pre-state: mpt_walk(root, witness, path, 64).\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la t1, ws_path; slli t2, s6, 6; add a3, t1, t2\n" ++
  "  li a4, 64\n" ++
  "  la a5, ws_acct; la a6, ws_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  bnez a0, .Lwsr_insert       # not found => insert needed (unsupported)\n" ++
  "  # new account = account_add_balance(account, delta).\n" ++
  "  la a0, ws_acct\n" ++
  "  la t0, ws_acct_len; ld a1, 0(t0)\n" ++
  "  la a2, ws_delta\n" ++
  "  la t1, ws_newacct; slli t2, s6, 7; add a3, t1, t2   # new acct dst = ws_newacct + 128*i\n" ++
  "  la a4, ws_newacct_len\n" ++
  "  jal ra, account_add_balance\n" ++
  "  bnez a0, .Lwsr_fail\n" ++
  "  # record change[i] = (path_ptr, 64, value_ptr, value_len).\n" ++
  "  la t0, ws_changes; slli t1, s6, 5; add t0, t0, t1\n" ++
  "  la t1, ws_path; slli t2, s6, 6; add t1, t1, t2; sd t1, 0(t0)\n" ++
  "  li t1, 64; sd t1, 8(t0)\n" ++
  "  la t1, ws_newacct; slli t2, s6, 7; add t1, t1, t2; sd t1, 16(t0)\n" ++
  "  la t1, ws_newacct_len; ld t1, 0(t1); sd t1, 24(t0)\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lwsr_loop\n" ++
  ".Lwsr_apply:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la a3, ws_changes; mv a4, s4; mv a5, s5\n" ++
  "  jal ra, mpt_state_root\n" ++
  "  j .Lwsr_ret\n" ++
  ".Lwsr_insert:\n" ++
  "  li a0, 1\n" ++
  "  j .Lwsr_ret\n" ++
  ".Lwsr_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lwsr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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
