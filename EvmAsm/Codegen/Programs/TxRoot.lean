/-
  EvmAsm.Codegen.Programs.TxRoot

  Indexed MPT root computers + transactions_root validators
  carved out of `EvmAsm.Codegen.Programs.MptEncode` per the
  file-size hard cap. Hosts:

    K170  mpt_two_leaf_root_indexed
    K171  block_validate_transactions_root_two_tx
    K185  mpt_one_leaf_root_indexed
    K186  block_validate_transactions_root_one_tx

  K170/K185 compute the 1-leaf and 2-leaf indexed MPT roots used
  for the `transactions_root` header field; K171/K186 are the
  matching block-level validators. Compose K163/K165/K167/K168/
  K169 (in MptEncode.lean) + K32 hp_encode_nibbles (Mpt.lean) +
  RLP/Keccak helpers.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## mpt_two_leaf_root_indexed -- PR-K170

    Compute the MPT root for an **indexed** trie containing
    exactly two entries at keys `rlp(0) = 0x80` and
    `rlp(1) = 0x01`. This is the common case for blocks with
    exactly two transactions / receipts / withdrawals, where the
    trie is `transactions_root` / `receipts_root` /
    `withdrawals_root`.

    Why a specialised helper: for the two indexed keys the
    structure is fully determined and the same regardless of the
    values:

      * `rlp(0) = 0x80` nibbles `[8, 0]`
      * `rlp(1) = 0x01` nibbles `[0, 1]`

    The shared prefix is empty (PR-K166 would return cpl=0 here),
    so the root is a branch whose only non-empty slots are:

      * slot 0 : leaf with path `[1]` and value `value_1`
      * slot 8 : leaf with path `[0]` and value `value_0`
      * slot 16 (value) and all others : empty (`0x80`)

      root = keccak256(rlp([slot_0, slot_1, ..., slot_15, value]))

    Composes:
      - PR-K168 `mpt_leaf_node_encode_from_nibbles`  × 2
      - PR-K163 `mpt_node_slot_encode`               × 2
      - PR-K167 `mpt_branch_payload_two_slots`
      - PR-K169 `mpt_branch_node_keccak`

    Callers that need the same for tries with > 2 entries, or
    with arbitrary non-indexed keys, must use the lower-level
    primitives directly.

    Calling convention:
      a0 (input)  : value_0 ptr (for key `rlp(0) = 0x80`)
      a1 (input)  : value_0 byte length
      a2 (input)  : value_1 ptr (for key `rlp(1) = 0x01`)
      a3 (input)  : value_1 byte length
      a4 (input)  : 32-byte output root ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds). -/
def mptTwoLeafRootIndexedFunction : String :=
  "mpt_two_leaf_root_indexed:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # value_0 ptr\n" ++
  "  mv s1, a1                   # value_0 len\n" ++
  "  mv s2, a2                   # value_1 ptr\n" ++
  "  mv s3, a3                   # value_1 len\n" ++
  "  mv s4, a4                   # output root ptr\n" ++
  "  # ---- Build leaf_0 RLP from nibbles=[0], value_0 ----\n" ++
  "  la t0, mtlri_nib0; sb zero, 0(t0)\n" ++
  "  mv a0, t0; li a1, 1\n" ++
  "  mv a2, s0; mv a3, s1\n" ++
  "  la a4, mtlri_leaf_0_buf\n" ++
  "  la a5, mtlri_leaf_0_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  # ---- Build leaf_1 RLP from nibbles=[1], value_1 ----\n" ++
  "  la t0, mtlri_nib1; li t1, 1; sb t1, 0(t0)\n" ++
  "  mv a0, t0; li a1, 1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, mtlri_leaf_1_buf\n" ++
  "  la a5, mtlri_leaf_1_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  # ---- Wrap leaf_0 in parent-slot bytes (K163) ----\n" ++
  "  la a0, mtlri_leaf_0_buf\n" ++
  "  la t0, mtlri_leaf_0_len; ld a1, 0(t0)\n" ++
  "  la a2, mtlri_slot_0_buf\n" ++
  "  la a3, mtlri_slot_0_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # ---- Wrap leaf_1 in parent-slot bytes ----\n" ++
  "  la a0, mtlri_leaf_1_buf\n" ++
  "  la t0, mtlri_leaf_1_len; ld a1, 0(t0)\n" ++
  "  la a2, mtlri_slot_1_buf\n" ++
  "  la a3, mtlri_slot_1_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # ---- Assemble 17-slot payload (slot 8 = leaf_0, slot 0 = leaf_1) ----\n" ++
  "  li a0, 8\n" ++
  "  la a1, mtlri_slot_0_buf\n" ++
  "  la t0, mtlri_slot_0_len; ld a2, 0(t0)\n" ++
  "  li a3, 0\n" ++
  "  la a4, mtlri_slot_1_buf\n" ++
  "  la t0, mtlri_slot_1_len; ld a5, 0(t0)\n" ++
  "  la a6, mtlri_branch_payload\n" ++
  "  la a7, mtlri_branch_payload_len\n" ++
  "  jal ra, mpt_branch_payload_two_slots\n" ++
  "  # ---- keccak256(rlp(branch_payload)) -> root ----\n" ++
  "  la a0, mtlri_branch_payload\n" ++
  "  la t0, mtlri_branch_payload_len; ld a1, 0(t0)\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, mpt_branch_node_keccak\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_mpt_two_leaf_root_indexed`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : value_0_len
      bytes  8..16 : value_1_len
      bytes 16..16+value_0_len: value_0 bytes
      bytes (16+value_0_len)..: value_1 bytes
    Output layout:
      bytes  0..32 : 32-byte trie root -/
def ziskMptTwoLeafRootIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # value_0_len\n" ++
  "  ld a3, 16(a5)               # value_1_len\n" ++
  "  addi a0, a5, 24             # value_0 ptr\n" ++
  "  add a2, a0, a1              # value_1 ptr\n" ++
  "  li a4, 0xa0010000           # output root ptr (32 B)\n" ++
  "  jal ra, mpt_two_leaf_root_indexed\n" ++
  "  j .Lmtlri_pdone\n" ++
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
  ".Lmtlri_pdone:"

def ziskMptTwoLeafRootIndexedDataSection : String :=
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
  "mbne_field_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_nib0:\n" ++
  "  .zero 1\n" ++
  "mtlri_nib1:\n" ++
  "  .zero 1\n" ++
  ".balign 8\n" ++
  "mtlri_leaf_0_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_leaf_0_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_leaf_1_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_leaf_1_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_slot_0_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_slot_0_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_slot_1_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_slot_1_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_branch_payload_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_branch_payload:\n" ++
  "  .zero 16384"

def ziskMptTwoLeafRootIndexedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptTwoLeafRootIndexedPrologue
  dataAsm     := ziskMptTwoLeafRootIndexedDataSection
}

/-! ## block_validate_transactions_root_two_tx -- PR-K171

    End-to-end validation: given a block header RLP and the two
    transactions of a 2-tx block, recompute the expected
    `transactions_root` and check it byte-equals the header's
    claimed value.

      claimed_root = header.field[4]              -- via K20
      computed_root = mpt_two_leaf_root_indexed(  -- K170
                          tx0, tx1)
      is_valid = (claimed_root == computed_root)

    Single-call entry point. The verdict lands in the
    caller-supplied u64 (1 if matches, 0 if not); `a0` returns
    the error code (header-parse failure / size mismatch
    distinct from "predicate is false").

    Composes:
      - PR-K20  `rlp_list_nth_item` on header field 4
      - PR-K170 `mpt_two_leaf_root_indexed`
        (which in turn composes K168 / K163 / K167 / K169)

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : tx0 ptr  (wire-format -- typed envelope or
                              legacy RLP -- used as the value
                              for key rlp(0) in the trie)
      a3 (input)  : tx0 byte length
      a4 (input)  : tx1 ptr  (value for key rlp(1))
      a5 (input)  : tx1 byte length
      a6 (input)  : u64 out (is_valid: 1 if root matches, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header RLP parse failure / field 4 missing
        2 : header.transactions_root length != 32 -/
def blockValidateTransactionsRootTwoTxFunction : String :=
  "block_validate_transactions_root_two_tx:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # tx0 ptr\n" ++
  "  mv s3, a3                   # tx0 len\n" ++
  "  mv s4, a4                   # tx1 ptr\n" ++
  "  mv s5, a5                   # tx1 len\n" ++
  "  mv s6, a6                   # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # ---- Extract header.transactions_root (field 4) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, bvtr_offset; la a4, bvtr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvtr_parse_fail\n" ++
  "  la t0, bvtr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvtr_size_fail\n" ++
  "  # Copy claimed root into bvtr_claimed_root\n" ++
  "  la t0, bvtr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                              # &header[off]\n" ++
  "  la t4, bvtr_claimed_root\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # ---- Compute the 2-leaf trie root from (tx0, tx1) ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  mv a2, s4; mv a3, s5\n" ++
  "  la a4, bvtr_computed_root\n" ++
  "  jal ra, mpt_two_leaf_root_indexed\n" ++
  "  # ---- 32-byte compare (claimed vs computed) ----\n" ++
  "  la t0, bvtr_claimed_root\n" ++
  "  la t1, bvtr_computed_root\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvtr_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvtr_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvtr_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvtr_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvtr_ret\n" ++
  ".Lbvtr_neq:\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvtr_ret\n" ++
  ".Lbvtr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvtr_ret\n" ++
  ".Lbvtr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvtr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_transactions_root_two_tx`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : tx0_len
      bytes 16..24 : tx1_len
      bytes 24..   : header_rlp || tx0 || tx1
    Output layout:
      bytes  0.. 8 : status (0=ok, 1=header parse, 2=size fail)
      bytes  8..16 : is_valid (1 if root matches, else 0) -/
def ziskBlockValidateTransactionsRootTwoTxPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)               # tx0_len\n" ++
  "  ld a5, 24(a7)               # tx1_len\n" ++
  "  addi a0, a7, 32             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # tx0 ptr = header_rlp + header_len\n" ++
  "  add a4, a2, a3              # tx1 ptr = tx0 + tx0_len\n" ++
  "  li a6, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_transactions_root_two_tx\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvtr_pdone\n" ++
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
  blockValidateTransactionsRootTwoTxFunction ++ "\n" ++
  ".Lbvtr_pdone:"

def ziskBlockValidateTransactionsRootTwoTxDataSection : String :=
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
  "mbne_field_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_nib0:\n" ++
  "  .zero 1\n" ++
  "mtlri_nib1:\n" ++
  "  .zero 1\n" ++
  ".balign 8\n" ++
  "mtlri_leaf_0_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_leaf_0_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_leaf_1_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_leaf_1_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_slot_0_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_slot_0_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_slot_1_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_slot_1_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_branch_payload_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_branch_payload:\n" ++
  "  .zero 16384\n" ++
  "bvtr_offset:\n" ++
  "  .zero 8\n" ++
  "bvtr_length:\n" ++
  "  .zero 8\n" ++
  "bvtr_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvtr_computed_root:\n" ++
  "  .zero 32"

def ziskBlockValidateTransactionsRootTwoTxProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateTransactionsRootTwoTxPrologue
  dataAsm     := ziskBlockValidateTransactionsRootTwoTxDataSection
}

/-! ## mpt_one_leaf_root_indexed -- PR-K185

    MPT root for the N=1 case of `transactions_root` /
    `receipts_root` / `withdrawals_root`: the trie has one
    entry at key `rlp(0) = 0x80` (which encodes to nibbles
    `[8, 0]`). With only one entry, the entire trie collapses
    to a single leaf node:

      leaf = rlp([hp([8, 0], leaf=true), value])
      root = keccak256(leaf)               -- if len(leaf) >= 32
      root = inline leaf                    -- if len(leaf) < 32
                                              (but as a 32B root
                                               it must be hashed
                                               for header field)

    For Ethereum header roots the result is ALWAYS a 32-byte
    keccak256 hash, regardless of leaf size, because the spec
    pre-pads short trie roots: `if len < 32: keccak256(leaf)
    anyway`. So we unconditionally take the keccak.

    Composes:
      - PR-K168 `mpt_leaf_node_encode_from_nibbles`
      - keccak256 sponge (zkvm_keccak256)

    Calling convention:
      a0 (input)  : value ptr (the single tx / receipt / withdrawal)
      a1 (input)  : value byte length
      a2 (input)  : 32-byte output root ptr
      ra (input)  : return -/
def mptOneLeafRootIndexedFunction : String :=
  "mpt_one_leaf_root_indexed:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # value ptr\n" ++
  "  mv s1, a1                   # value len\n" ++
  "  mv s2, a2                   # output root ptr\n" ++
  "  # Build path = [8, 0] (rlp(0)=0x80 -> nibbles [8,0])\n" ++
  "  la t0, mtoli_nibbles\n" ++
  "  li t1, 8; sb t1, 0(t0)\n" ++
  "  li t1, 0; sb t1, 1(t0)\n" ++
  "  # ---- Encode leaf node ----\n" ++
  "  la a0, mtoli_nibbles\n" ++
  "  li a1, 2\n" ++
  "  mv a2, s0; mv a3, s1\n" ++
  "  la a4, mtoli_leaf_buf\n" ++
  "  la a5, mtoli_leaf_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  # ---- keccak256 the leaf ----\n" ++
  "  la a0, mtoli_leaf_buf\n" ++
  "  la t0, mtoli_leaf_len; ld a1, 0(t0)\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mpt_one_leaf_root_indexed`: probe BuildUnit.
    Input layout:
      bytes 0..8 : value_len
      bytes 8..  : value
    Output layout:
      bytes 0..32 : 32-byte trie root -/
def ziskMptOneLeafRootIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # value_len\n" ++
  "  addi a0, a5, 16             # value ptr\n" ++
  "  li a2, 0xa0010000           # output root ptr (32 B)\n" ++
  "  jal ra, mpt_one_leaf_root_indexed\n" ++
  "  j .Lmtoli_pdone\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  ".Lmtoli_pdone:"

def ziskMptOneLeafRootIndexedDataSection : String :=
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
  "  .zero 16384"

def ziskMptOneLeafRootIndexedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptOneLeafRootIndexedPrologue
  dataAsm     := ziskMptOneLeafRootIndexedDataSection
}

/-! ## block_validate_transactions_root_one_tx -- PR-K186

    End-to-end transactions_root validation for 1-tx blocks:
    the N=1 analogue of K171 `block_validate_transactions_root_two_tx`.

      claimed_root = header.field[4]              -- via K20
      computed_root = mpt_one_leaf_root_indexed(  -- K185
                          tx0)
      is_valid = (claimed_root == computed_root)

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : tx0 ptr
      a3 (input)  : tx0 byte length
      a4 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header RLP parse failure / field 4 missing
        2 : header.transactions_root length != 32 -/
def blockValidateTransactionsRootOneTxFunction : String :=
  "block_validate_transactions_root_one_tx:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # tx0 ptr\n" ++
  "  mv s3, a3                   # tx0 len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Extract header.transactions_root (field 4) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, bvtr1_offset; la a4, bvtr1_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvtr1_parse_fail\n" ++
  "  la t0, bvtr1_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvtr1_size_fail\n" ++
  "  # Copy claimed root\n" ++
  "  la t0, bvtr1_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, bvtr1_claimed_root\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # ---- Compute MPT root for the single tx ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, bvtr1_computed_root\n" ++
  "  jal ra, mpt_one_leaf_root_indexed\n" ++
  "  # ---- 32-byte compare ----\n" ++
  "  la t0, bvtr1_claimed_root\n" ++
  "  la t1, bvtr1_computed_root\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvtr1_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvtr1_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvtr1_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvtr1_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvtr1_ret\n" ++
  ".Lbvtr1_neq:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvtr1_ret\n" ++
  ".Lbvtr1_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvtr1_ret\n" ++
  ".Lbvtr1_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvtr1_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_transactions_root_one_tx`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : tx0_len
      bytes 16..   : header_rlp || tx0
    Output layout:
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : is_valid -/
def ziskBlockValidateTransactionsRootOneTxPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)               # tx0_len\n" ++
  "  addi a0, a7, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # tx0 ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_transactions_root_one_tx\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvtr1_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  blockValidateTransactionsRootOneTxFunction ++ "\n" ++
  ".Lbvtr1_pdone:"

def ziskBlockValidateTransactionsRootOneTxDataSection : String :=
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
  "bvtr1_offset:\n" ++
  "  .zero 8\n" ++
  "bvtr1_length:\n" ++
  "  .zero 8\n" ++
  "bvtr1_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvtr1_computed_root:\n" ++
  "  .zero 32"

def ziskBlockValidateTransactionsRootOneTxProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateTransactionsRootOneTxPrologue
  dataAsm     := ziskBlockValidateTransactionsRootOneTxDataSection
}


end EvmAsm.Codegen
