/-
  EvmAsm.Codegen.Programs.BlockRoots

  Block-level MPT-root validators carved out of
  `EvmAsm.Codegen.Programs.Mpt` per the file-size hard cap.
  Hosts:

    K191  block_validate_withdrawals_root_one_w
    K192  block_validate_withdrawals_root_two_w
    K193  block_validate_receipts_root_one_receipt
    K194  block_validate_receipts_root_two_receipts

  Each end-to-end validator extracts the claimed root from the
  header RLP, computes the MPT root from the body payloads via
  K170 `mpt_two_leaf_root_indexed` or K185 `mpt_one_leaf_root_indexed`,
  and writes a 0/1 predicate.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.TxRoot

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_validate_withdrawals_root_one_w -- PR-K191

    End-to-end `withdrawals_root` validation for blocks with
    exactly one withdrawal. Field 16 variant of K186
    `block_validate_transactions_root_one_tx`.

      claimed_root = header.field[16]             -- via K20
      computed_root = mpt_one_leaf_root_indexed(  -- K185
                          withdrawal_rlp)
      is_valid = (claimed_root == computed_root)

    The withdrawal is supplied as its already-RLP-encoded
    payload (`rlp([index, validator_index, address, amount])`,
    typically built via K130 `withdrawal_rlp_encode`). The
    MPT-leaf wrapping is then the same single-leaf shape as
    transactions_root for N=1.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : withdrawal_rlp ptr (pre-encoded payload)
      a3 (input)  : withdrawal_rlp byte length
      a4 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header RLP parse failure / field 16 missing
        2 : header.withdrawals_root length != 32 -/
def blockValidateWithdrawalsRootOneWFunction : String :=
  "block_validate_withdrawals_root_one_w:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # withdrawal_rlp ptr\n" ++
  "  mv s3, a3                   # withdrawal_rlp len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Extract header.withdrawals_root (field 16) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, bvwr1_offset; la a4, bvwr1_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvwr1_parse_fail\n" ++
  "  la t0, bvwr1_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvwr1_size_fail\n" ++
  "  la t0, bvwr1_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, bvwr1_claimed_root\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # ---- Compute MPT root for single withdrawal ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, bvwr1_computed_root\n" ++
  "  jal ra, mpt_one_leaf_root_indexed\n" ++
  "  la t0, bvwr1_claimed_root\n" ++
  "  la t1, bvwr1_computed_root\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvwr1_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvwr1_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvwr1_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvwr1_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvwr1_ret\n" ++
  ".Lbvwr1_neq:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvwr1_ret\n" ++
  ".Lbvwr1_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvwr1_ret\n" ++
  ".Lbvwr1_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvwr1_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_withdrawals_root_one_w`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : withdrawal_rlp_len
      bytes 16..   : header_rlp || withdrawal_rlp
    Output layout:
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : is_valid -/
def ziskBlockValidateWithdrawalsRootOneWPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)               # withdrawal_rlp_len\n" ++
  "  addi a0, a7, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # withdrawal_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_withdrawals_root_one_w\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvwr1_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  blockValidateWithdrawalsRootOneWFunction ++ "\n" ++
  ".Lbvwr1_pdone:"

def ziskBlockValidateWithdrawalsRootOneWDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "mlnen_field_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_cursor:\n" ++
  "  .zero 8\n" ++
  "mlnen_total_payload:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mlnen_payload_buf:\n" ++
  "  .zero 16384\n" ++
  "mtoli_nibbles:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mtoli_leaf_len:\n" ++
  "  .zero 8\n" ++
  "mtoli_leaf_buf:\n" ++
  "  .zero 16384\n" ++
  "bvwr1_offset:\n" ++
  "  .zero 8\n" ++
  "bvwr1_length:\n" ++
  "  .zero 8\n" ++
  "bvwr1_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvwr1_computed_root:\n" ++
  "  .zero 32"

def ziskBlockValidateWithdrawalsRootOneWProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateWithdrawalsRootOneWPrologue
  dataAsm     := ziskBlockValidateWithdrawalsRootOneWDataSection
}

/-! ## block_validate_withdrawals_root_two_w -- PR-K192

    End-to-end `withdrawals_root` validation for blocks with
    exactly two withdrawals. Field 16 variant of K171
    `block_validate_transactions_root_two_tx` -- same 2-leaf
    MPT shape (slots 0 and 8) but rooted at withdrawals
    instead of transactions.

      claimed_root = header.field[16]             -- via K20
      computed_root = mpt_two_leaf_root_indexed(  -- K170
                          w0_rlp, w1_rlp)
      is_valid = (claimed_root == computed_root)

    Both withdrawals are supplied pre-RLP-encoded (typically
    via K130 `withdrawal_rlp_encode` upstream).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : w0_rlp ptr
      a3 (input)  : w0_rlp byte length
      a4 (input)  : w1_rlp ptr
      a5 (input)  : w1_rlp byte length
      a6 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header RLP parse failure / field 16 missing
        2 : header.withdrawals_root length != 32 -/
def blockValidateWithdrawalsRootTwoWFunction : String :=
  "block_validate_withdrawals_root_two_w:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2; mv s3, a3                # w0\n" ++
  "  mv s4, a4; mv s5, a5                # w1\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # ---- Extract header.withdrawals_root (field 16) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, bvwr2_offset; la a4, bvwr2_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvwr2_parse_fail\n" ++
  "  la t0, bvwr2_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvwr2_size_fail\n" ++
  "  la t0, bvwr2_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, bvwr2_claimed_root\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # ---- Compute 2-leaf MPT root ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  mv a2, s4; mv a3, s5\n" ++
  "  la a4, bvwr2_computed_root\n" ++
  "  jal ra, mpt_two_leaf_root_indexed\n" ++
  "  la t0, bvwr2_claimed_root\n" ++
  "  la t1, bvwr2_computed_root\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvwr2_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvwr2_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvwr2_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvwr2_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvwr2_ret\n" ++
  ".Lbvwr2_neq:\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvwr2_ret\n" ++
  ".Lbvwr2_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvwr2_ret\n" ++
  ".Lbvwr2_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvwr2_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_withdrawals_root_two_w`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : w0_rlp_len
      bytes 16..24 : w1_rlp_len
      bytes 24..   : header_rlp || w0_rlp || w1_rlp
    Output layout:
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : is_valid -/
def ziskBlockValidateWithdrawalsRootTwoWPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)               # w0_rlp_len\n" ++
  "  ld a5, 24(a7)               # w1_rlp_len\n" ++
  "  addi a0, a7, 32             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # w0_rlp ptr\n" ++
  "  add a4, a2, a3              # w1_rlp ptr\n" ++
  "  li a6, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_withdrawals_root_two_w\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvwr2_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  mptBranchNodeKeccakFunction ++ "\n" ++
  mptTwoLeafRootIndexedFunction ++ "\n" ++
  blockValidateWithdrawalsRootTwoWFunction ++ "\n" ++
  ".Lbvwr2_pdone:"

def ziskBlockValidateWithdrawalsRootTwoWDataSection : String :=
  ziskBlockValidateTransactionsRootTwoTxDataSection ++ "\n" ++
  "bvwr2_offset:\n" ++
  "  .zero 8\n" ++
  "bvwr2_length:\n" ++
  "  .zero 8\n" ++
  "bvwr2_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvwr2_computed_root:\n" ++
  "  .zero 32"

def ziskBlockValidateWithdrawalsRootTwoWProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateWithdrawalsRootTwoWPrologue
  dataAsm     := ziskBlockValidateWithdrawalsRootTwoWDataSection
}

/-! ## block_validate_receipts_root_one_receipt -- PR-K193

    End-to-end `receipts_root` validation for blocks with
    exactly one receipt. Field 5 variant of K186 / K191:

      claimed_root = header.field[5]              -- via K20
      computed_root = mpt_one_leaf_root_indexed(  -- K185
                          receipt_rlp)
      is_valid = (claimed_root == computed_root)

    The receipt is supplied as its already-encoded payload --
    typically the output of K156 `receipt_encode`, which yields
    `rlp([status, cum_gas, bloom, logs])` for legacy receipts
    and `tx_type || rlp([...])` for typed receipts (EIP-2718).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : receipt_rlp ptr (pre-encoded payload)
      a3 (input)  : receipt_rlp byte length
      a4 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header RLP parse failure / field 5 missing
        2 : header.receipts_root length != 32 -/
def blockValidateReceiptsRootOneReceiptFunction : String :=
  "block_validate_receipts_root_one_receipt:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2; mv s3, a3                # receipt\n" ++
  "  mv s4, a4                            # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Extract header.receipts_root (field 5) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, bvrr1_offset; la a4, bvrr1_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvrr1_parse_fail\n" ++
  "  la t0, bvrr1_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvrr1_size_fail\n" ++
  "  la t0, bvrr1_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, bvrr1_claimed_root\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, bvrr1_computed_root\n" ++
  "  jal ra, mpt_one_leaf_root_indexed\n" ++
  "  la t0, bvrr1_claimed_root\n" ++
  "  la t1, bvrr1_computed_root\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvrr1_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvrr1_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvrr1_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvrr1_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvrr1_ret\n" ++
  ".Lbvrr1_neq:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvrr1_ret\n" ++
  ".Lbvrr1_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvrr1_ret\n" ++
  ".Lbvrr1_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvrr1_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_receipts_root_one_receipt`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp_len
      bytes 8..16 : receipt_rlp_len
      bytes 16..  : header_rlp || receipt_rlp
    Output layout:
      bytes 0..8  : status
      bytes 8..16 : is_valid -/
def ziskBlockValidateReceiptsRootOneReceiptPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)               # receipt_rlp_len\n" ++
  "  addi a0, a7, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # receipt_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_receipts_root_one_receipt\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvrr1_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  blockValidateReceiptsRootOneReceiptFunction ++ "\n" ++
  ".Lbvrr1_pdone:"

def ziskBlockValidateReceiptsRootOneReceiptDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "mlnen_field_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_cursor:\n" ++
  "  .zero 8\n" ++
  "mlnen_total_payload:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mlnen_payload_buf:\n" ++
  "  .zero 16384\n" ++
  "mtoli_nibbles:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "mtoli_leaf_len:\n" ++
  "  .zero 8\n" ++
  "mtoli_leaf_buf:\n" ++
  "  .zero 16384\n" ++
  "bvrr1_offset:\n" ++
  "  .zero 8\n" ++
  "bvrr1_length:\n" ++
  "  .zero 8\n" ++
  "bvrr1_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvrr1_computed_root:\n" ++
  "  .zero 32"

def ziskBlockValidateReceiptsRootOneReceiptProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateReceiptsRootOneReceiptPrologue
  dataAsm     := ziskBlockValidateReceiptsRootOneReceiptDataSection
}

/-! ## block_validate_receipts_root_two_receipts -- PR-K194

    N=2 variant for `receipts_root`: validates `header.field[5]`
    matches the 2-leaf MPT root of two pre-encoded receipts.
    Field 5 variant of K171 / K192 -- completes the
    `{tx, receipt, withdrawal}` root-validator trinity for N=2.

    Both receipts are supplied pre-encoded (the output of K156
    `receipt_encode` upstream).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : r0_rlp ptr
      a3 (input)  : r0_rlp byte length
      a4 (input)  : r1_rlp ptr
      a5 (input)  : r1_rlp byte length
      a6 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : header parse failure / field 5 missing
        2 : header.receipts_root length != 32 -/
def blockValidateReceiptsRootTwoReceiptsFunction : String :=
  "block_validate_receipts_root_two_receipts:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2; mv s3, a3                # r0\n" ++
  "  mv s4, a4; mv s5, a5                # r1\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, bvrr2_offset; la a4, bvrr2_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvrr2_parse_fail\n" ++
  "  la t0, bvrr2_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvrr2_size_fail\n" ++
  "  la t0, bvrr2_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, bvrr2_claimed_root\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  mv a2, s4; mv a3, s5\n" ++
  "  la a4, bvrr2_computed_root\n" ++
  "  jal ra, mpt_two_leaf_root_indexed\n" ++
  "  la t0, bvrr2_claimed_root\n" ++
  "  la t1, bvrr2_computed_root\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvrr2_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvrr2_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvrr2_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvrr2_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvrr2_ret\n" ++
  ".Lbvrr2_neq:\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvrr2_ret\n" ++
  ".Lbvrr2_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvrr2_ret\n" ++
  ".Lbvrr2_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvrr2_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_receipts_root_two_receipts`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : r0_rlp_len
      bytes 16..24 : r1_rlp_len
      bytes 24..   : header_rlp || r0_rlp || r1_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskBlockValidateReceiptsRootTwoReceiptsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)               # r0_rlp_len\n" ++
  "  ld a5, 24(a7)               # r1_rlp_len\n" ++
  "  addi a0, a7, 32             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # r0_rlp ptr\n" ++
  "  add a4, a2, a3              # r1_rlp ptr\n" ++
  "  li a6, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_receipts_root_two_receipts\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvrr2_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  mptBranchNodeKeccakFunction ++ "\n" ++
  mptTwoLeafRootIndexedFunction ++ "\n" ++
  blockValidateReceiptsRootTwoReceiptsFunction ++ "\n" ++
  ".Lbvrr2_pdone:"

def ziskBlockValidateReceiptsRootTwoReceiptsDataSection : String :=
  ziskBlockValidateTransactionsRootTwoTxDataSection ++ "\n" ++
  "bvrr2_offset:\n" ++
  "  .zero 8\n" ++
  "bvrr2_length:\n" ++
  "  .zero 8\n" ++
  "bvrr2_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvrr2_computed_root:\n" ++
  "  .zero 32"

def ziskBlockValidateReceiptsRootTwoReceiptsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateReceiptsRootTwoReceiptsPrologue
  dataAsm     := ziskBlockValidateReceiptsRootTwoReceiptsDataSection
}


end EvmAsm.Codegen
