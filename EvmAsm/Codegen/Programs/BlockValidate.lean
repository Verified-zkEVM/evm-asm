/-
  EvmAsm.Codegen.Programs.BlockValidate

  Block-level full-validation predicates carved out of
  `EvmAsm.Codegen.Programs.Block` per the file-size hard cap.
  Hosts:

    K176  block_validate_2tx_full
    K177  block_body_extract_2tx
    K178  block_validate_2tx_full_with_body
    K179  block_validate_empty_ommers_hash
    K180  block_validate_no_withdrawals_pair
    K181  block_validate_empty_receipts_root
    K182  block_validate_empty_block
    K183  validate_empty_block_with_parent
    K184  validate_empty_block_chain

  These compose header validators (K172, K72), MPT root
  computers (K170/K185/K186 in MptEncode.lean), block-body
  decoders (K83 in Block.lean), and various RLP helpers.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Codegen.Programs.Block

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_validate_2tx_full -- PR-K176

    Full validation of a 2-tx Ethereum block: combines the
    per-header chain check (K174) with the
    `transactions_root` MPT match (K171) into a single
    end-to-end predicate. Calling this on `(parent_rlp,
    header_rlp, tx0, tx1)` returns `is_valid = 1` iff both:

      1. validate_header_pair(parent, header) accepts:
         child.parent_hash == keccak(parent),
         child.number == parent.number + 1,
         child.timestamp > parent.timestamp,
         check_gas_limit(child, parent) == 0
      2. block_validate_transactions_root_two_tx(header, tx0, tx1)
         accepts: header.transactions_root matches the trie
         root of the two-tx MPT.

    This composition is the per-block invariant for a 2-tx block
    in the chain (modulo the body-side checks ECRECOVER / EVM
    execution still gates).

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : header_rlp ptr  (the child header)
      a3 (input)  : header_rlp byte length
      a4 (input)  : tx0 ptr
      a5 (input)  : tx0 byte length
      a6 (input)  : tx1 ptr
      a7 (input)  : tx1 byte length
      ra (input)  : return
      (out via shadow regs)  : caller passes the is_valid u64
                                output pointer via memory; see
                                prologue for the wiring.
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status code:
          1   header-pair child parse failure
          2   header-pair child.parent_hash size mismatch
          3   header-pair parent field-extract failure
          4   header-pair child field-extract failure
          11  tx-root header parse failure
          12  tx-root header.transactions_root size mismatch

    The is_valid output pointer is read from `bv2f_out_ptr`
    (an indirection slot in `.data`) to keep the calling
    convention within the 8 a-register limit. The prologue
    initializes this slot to `0xa0010008`. -/
def blockValidate2txFullFunction : String :=
  "block_validate_2tx_full:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # header (child)\n" ++
  "  mv s4, a4; mv s5, a5                # tx0\n" ++
  "  mv s6, a6; mv s7, a7                # tx1\n" ++
  "  la t0, bv2f_out_ptr; ld s8, 0(t0)   # is_valid u64 out\n" ++
  "  sd zero, 0(s8)\n" ++
  "  # ---- (A) Header pair check ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, bv2f_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  beqz a0, .Lbv2f_pair_status_ok\n" ++
  "  # Propagate pair status (1..4) to caller; keep same numbering.\n" ++
  "  j .Lbv2f_ret\n" ++
  ".Lbv2f_pair_status_ok:\n" ++
  "  la t0, bv2f_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv2f_pred_false\n" ++
  "  # ---- (B) Transactions-root MPT check ----\n" ++
  "  mv a0, s2; mv a1, s3                # header (child)\n" ++
  "  mv a2, s4; mv a3, s5                # tx0\n" ++
  "  mv a4, s6; mv a5, s7                # tx1\n" ++
  "  la a6, bv2f_tx_root_valid\n" ++
  "  jal ra, block_validate_transactions_root_two_tx\n" ++
  "  beqz a0, .Lbv2f_tx_root_status_ok\n" ++
  "  # Remap K171 status (1=parse, 2=size) into 11/12 to keep\n" ++
  "  # distinguishable from K174 codes.\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lbv2f_ret\n" ++
  ".Lbv2f_tx_root_status_ok:\n" ++
  "  la t0, bv2f_tx_root_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv2f_pred_false\n" ++
  "  # Both invariants hold.\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s8)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbv2f_ret\n" ++
  ".Lbv2f_pred_false:\n" ++
  "  sd zero, 0(s8)\n" ++
  "  li a0, 0\n" ++
  ".Lbv2f_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_validate_2tx_full`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : header_rlp_len
      bytes 16..24 : tx0_len
      bytes 24..32 : tx1_len
      bytes 32..   : parent_rlp || header_rlp || tx0 || tx1
    Output layout:
      bytes  0.. 8 : status (0=ok, 1..4 pair, 11..12 tx-root)
      bytes  8..16 : is_valid (1 if both invariants hold) -/
def ziskBlockValidate2txFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0xa0010008\n" ++
  "  la t5, bv2f_out_ptr\n" ++
  "  sd t6, 0(t5)\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)              # parent_rlp_len\n" ++
  "  ld a3, 16(a7)              # header_rlp_len\n" ++
  "  ld a5, 24(a7)              # tx0_len\n" ++
  "  ld t0, 32(a7)              # tx1_len\n" ++
  "  la t1, bv2f_tx1_len; sd t0, 0(t1)\n" ++
  "  addi a0, a7, 40            # parent_rlp ptr\n" ++
  "  add a2, a0, a1             # header_rlp ptr\n" ++
  "  add a4, a2, a3             # tx0 ptr\n" ++
  "  add a6, a4, a5             # tx1 ptr\n" ++
  "  la t1, bv2f_tx1_len; ld t0, 0(t1)\n" ++
  "  mv a7, t0                  # tx1_len\n" ++
  "  jal ra, block_validate_2tx_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbv2f_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  mptBranchNodeKeccakFunction ++ "\n" ++
  mptTwoLeafRootIndexedFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockValidateTransactionsRootTwoTxFunction ++ "\n" ++
  blockValidate2txFullFunction ++ "\n" ++
  ".Lbv2f_pdone:"

def ziskBlockValidate2txFullDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
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
  "  .zero 32\n" ++
  "bv2f_out_ptr:\n" ++
  "  .zero 8\n" ++
  "bv2f_pair_valid:\n" ++
  "  .zero 8\n" ++
  "bv2f_tx_root_valid:\n" ++
  "  .zero 8\n" ++
  "bv2f_tx1_len:\n" ++
  "  .zero 8"

def ziskBlockValidate2txFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidate2txFullPrologue
  dataAsm     := ziskBlockValidate2txFullDataSection
}

/-! ## block_body_extract_2tx -- PR-K177

    Extract the two transactions from a block body whose
    transactions list contains exactly two items, while also
    asserting that the ommers list is the empty list (`0xc0`)
    -- the post-merge invariant.

    Body RLP layout (post-Shanghai):
      `rlp([transactions, ommers, withdrawals])`

    This helper:
      1. Decodes the body with K83 `block_body_decode`.
      2. Verifies `ommers_length == 1` and the single byte is
         `0xc0` (== `rlp([])`, the empty list).
      3. Counts the transactions list with K47
         `rlp_list_count_items`; requires count == 2.
      4. Extracts tx0 and tx1 with K20 `rlp_list_nth_item` on
         the inner transactions list, returning (offset, len)
         in the OUTER body's address space (offset relative to
         body_rlp, ready to feed into K171 etc.).

    Output struct (32 bytes):
       0..  8  tx0_offset (in body_rlp)
       8.. 16  tx0_length
      16.. 24  tx1_offset
      24.. 32  tx1_length

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 32-byte output struct ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body RLP parse failure (not a 3-item list)
        2 : ommers not the empty list
        3 : transactions list count != 2
        4 : transactions list item extraction failure -/
def blockBodyExtract2txFunction : String :=
  "block_body_extract_2tx:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_rlp len\n" ++
  "  mv s2, a2                   # output struct\n" ++
  "  # (1) Decode body into bbe_body_struct (48 B)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bbe_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbe_parse_fail\n" ++
  "  # (2) Verify ommers == 0xc0\n" ++
  "  la t0, bbe_body_struct; ld t1, 16(t0)        # ommers_offset\n" ++
  "  ld t2, 24(t0)                                # ommers_length\n" ++
  "  li t3, 1\n" ++
  "  bne t2, t3, .Lbbe_ommers_fail\n" ++
  "  add t1, s0, t1                               # &body[off]\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbbe_ommers_fail\n" ++
  "  # (3) Count transactions list\n" ++
  "  la t0, bbe_body_struct; ld s3, 0(t0)         # txs_offset (in body)\n" ++
  "  ld s4, 8(t0)                                 # txs_length\n" ++
  "  add a0, s0, s3                               # txs_list ptr\n" ++
  "  mv a1, s4\n" ++
  "  la a2, bbe_tx_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbe_txs_fail\n" ++
  "  la t0, bbe_tx_count; ld t1, 0(t0)\n" ++
  "  li t2, 2\n" ++
  "  bne t1, t2, .Lbbe_count_fail\n" ++
  "  # (4) Extract tx0\n" ++
  "  add a0, s0, s3; mv a1, s4; li a2, 0\n" ++
  "  la a3, bbe_item_off; la a4, bbe_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbe_txs_fail\n" ++
  "  la t0, bbe_item_off; ld t1, 0(t0)\n" ++
  "  add t1, t1, s3                               # offset relative to body\n" ++
  "  sd t1, 0(s2)\n" ++
  "  la t0, bbe_item_len; ld t1, 0(t0)\n" ++
  "  sd t1, 8(s2)\n" ++
  "  # Extract tx1\n" ++
  "  add a0, s0, s3; mv a1, s4; li a2, 1\n" ++
  "  la a3, bbe_item_off; la a4, bbe_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbe_txs_fail\n" ++
  "  la t0, bbe_item_off; ld t1, 0(t0)\n" ++
  "  add t1, t1, s3\n" ++
  "  sd t1, 16(s2)\n" ++
  "  la t0, bbe_item_len; ld t1, 0(t0)\n" ++
  "  sd t1, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_ommers_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_count_fail:\n" ++
  "  li a0, 3\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_txs_fail:\n" ++
  "  li a0, 4\n" ++
  ".Lbbe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_body_extract_2tx`: probe BuildUnit.
    Input layout:
      bytes 0.. 8 : body_rlp_len
      bytes 8..   : body_rlp
    Output layout:
      bytes  0.. 8 : status (0..4)
      bytes  8..40 : 32-byte struct (tx0 off+len, tx1 off+len) -/
def ziskBlockBodyExtract2txPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 16             # body_rlp ptr\n" ++
  "  li a2, 0xa0010008           # output struct ptr\n" ++
  "  jal ra, block_body_extract_2tx\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbbe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtract2txFunction ++ "\n" ++
  ".Lbbe_pdone:"

def ziskBlockBodyExtract2txDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbe_body_struct:\n" ++
  "  .zero 48\n" ++
  "bbe_tx_count:\n" ++
  "  .zero 8\n" ++
  "bbe_item_off:\n" ++
  "  .zero 8\n" ++
  "bbe_item_len:\n" ++
  "  .zero 8"

def ziskBlockBodyExtract2txProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyExtract2txPrologue
  dataAsm     := ziskBlockBodyExtract2txDataSection
}

/-! ## block_validate_2tx_full_with_body -- PR-K178

    Single-call end-to-end validator for a 2-tx Ethereum block,
    taking `(parent_rlp, header_rlp, body_rlp)` and returning
    one is_valid u64. Composes K177 + K176:

      1. K177 `block_body_extract_2tx(body_rlp)` decodes the
         body, verifies `[txs, ommers, withdrawals]` shape with
         exactly two transactions and empty ommers, and returns
         `(tx0_off, tx0_len, tx1_off, tx1_len)` in body-relative
         coordinates.
      2. K176 `block_validate_2tx_full(parent, header, tx0, tx1)`
         verifies all four header-pair invariants plus the
         transactions_root MPT match using the extracted tx
         slices.

    This is the body-aware shape of `validate_block` for 2-tx
    blocks; it is the natural endpoint of the K-series chain
    once both the header and body sides are covered.

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : header_rlp ptr
      a3 (input)  : header_rlp byte length
      a4 (input)  : body_rlp ptr
      a5 (input)  : body_rlp byte length
      a6 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0  success -- predicate written
        1..4   propagated from `block_body_extract_2tx`
              (1 parse, 2 ommers, 3 count, 4 inner extract)
        11..14 propagated from `block_validate_2tx_full`
              (11..14 == pair codes 1..4)
        21..22 propagated from K171 inside K176
              (tx-root parse / size codes 11..12 + 10) -/
def blockValidate2txFullWithBodyFunction : String :=
  "block_validate_2tx_full_with_body:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1          # parent\n" ++
  "  mv s2, a2; mv s3, a3          # header\n" ++
  "  mv s4, a4; mv s5, a5          # body\n" ++
  "  mv s6, a6                     # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # ---- (A) Extract tx0 / tx1 from body ----\n" ++
  "  mv a0, s4; mv a1, s5\n" ++
  "  la a2, bv2fb_struct\n" ++
  "  jal ra, block_body_extract_2tx\n" ++
  "  beqz a0, .Lbv2fb_body_ok\n" ++
  "  # Propagate body status (1..4) unchanged.\n" ++
  "  j .Lbv2fb_ret\n" ++
  ".Lbv2fb_body_ok:\n" ++
  "  # Resolve tx0 / tx1 pointers in body address space.\n" ++
  "  la t0, bv2fb_struct\n" ++
  "  ld t1,  0(t0)                # tx0_off (in body)\n" ++
  "  ld t2,  8(t0)                # tx0_len\n" ++
  "  ld t3, 16(t0)                # tx1_off\n" ++
  "  ld t4, 24(t0)                # tx1_len\n" ++
  "  add t1, s4, t1               # tx0 ptr\n" ++
  "  add t3, s4, t3               # tx1 ptr\n" ++
  "  la t5, bv2f_out_ptr; sd s6, 0(t5)   # wire is_valid out through indirection\n" ++
  "  # K176 takes 8 a-regs; the is_valid out is read from\n" ++
  "  # bv2f_out_ptr (already set above).\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  mv a4, t1; mv a5, t2\n" ++
  "  mv a6, t3; mv a7, t4\n" ++
  "  jal ra, block_validate_2tx_full\n" ++
  "  beqz a0, .Lbv2fb_check_pred\n" ++
  "  # K176 status: 1..4 pair, 11..12 tx-root. Remap to\n" ++
  "  # 11..14 and 21..22 so callers can distinguish from\n" ++
  "  # body-extract codes (1..4).\n" ++
  "  li t0, 5\n" ++
  "  bltu a0, t0, .Lbv2fb_remap_pair\n" ++
  "  # K176 a0 in {11, 12} -> {21, 22}\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lbv2fb_ret\n" ++
  ".Lbv2fb_remap_pair:\n" ++
  "  # K176 a0 in {1..4} -> {11..14}\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lbv2fb_ret\n" ++
  ".Lbv2fb_check_pred:\n" ++
  "  # K176 already wrote is_valid via the indirection slot.\n" ++
  "  li a0, 0\n" ++
  ".Lbv2fb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_2tx_full_with_body`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : header_rlp_len
      bytes 16..24 : body_rlp_len
      bytes 24..   : parent_rlp || header_rlp || body_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskBlockValidate2txFullWithBodyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)                # header_rlp_len\n" ++
  "  ld a5, 24(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 32              # parent_rlp ptr\n" ++
  "  add a2, a0, a1               # header_rlp ptr\n" ++
  "  add a4, a2, a3               # body_rlp ptr\n" ++
  "  li a6, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_2tx_full_with_body\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbv2fb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  mptBranchNodeKeccakFunction ++ "\n" ++
  mptTwoLeafRootIndexedFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockValidateTransactionsRootTwoTxFunction ++ "\n" ++
  blockValidate2txFullFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtract2txFunction ++ "\n" ++
  blockValidate2txFullWithBodyFunction ++ "\n" ++
  ".Lbv2fb_pdone:"

def ziskBlockValidate2txFullWithBodyDataSection : String :=
  ziskBlockValidate2txFullDataSection ++ "\n" ++
  "bv2fb_struct:\n" ++
  "  .zero 32\n" ++
  "bbe_body_struct:\n" ++
  "  .zero 48\n" ++
  "bbe_tx_count:\n" ++
  "  .zero 8\n" ++
  "bbe_item_off:\n" ++
  "  .zero 8\n" ++
  "bbe_item_len:\n" ++
  "  .zero 8"

def ziskBlockValidate2txFullWithBodyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidate2txFullWithBodyPrologue
  dataAsm     := ziskBlockValidate2txFullWithBodyDataSection
}

/-! ## block_validate_empty_ommers_hash -- PR-K179

    Extract the header's `ommers_hash` field (field 1, 32
    bytes) and verify it equals the post-merge constant
    `EMPTY_OMMERS_HASH = keccak256(rlp([]))`:

      0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347

    Post-merge, all blocks have an empty ommers list (per EIP-3675),
    so this is the canonical per-header check that complements
    K177's body-side ommers-empty assertion. Pre-merge headers
    fail this trivially.

    The 32-byte constant is materialized as a `.data` blob and
    compared 4 × `ld`/`bne` against the field-1 content.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (is_valid: 1 if matches the constant)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header parse failure
        2 : field 1 length != 32 bytes -/
def blockValidateEmptyOmmersHashFunction : String :=
  "block_validate_empty_ommers_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # is_valid out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # ---- Extract header.ommers_hash (field 1) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, bveoh_offset; la a4, bveoh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbveoh_parse_fail\n" ++
  "  la t0, bveoh_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbveoh_size_fail\n" ++
  "  # 32-byte compare against the post-merge constant.\n" ++
  "  la t0, bveoh_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                                  # &header[off]\n" ++
  "  la t4, bveoh_empty_ommers_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbveoh_ret\n" ++
  ".Lbveoh_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbveoh_ret\n" ++
  ".Lbveoh_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbveoh_ret\n" ++
  ".Lbveoh_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbveoh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_empty_ommers_hash`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp_len
      bytes 8..   : header_rlp
    Output layout:
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : is_valid (1 if matches the constant) -/
def ziskBlockValidateEmptyOmmersHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_empty_ommers_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbveoh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockValidateEmptyOmmersHashFunction ++ "\n" ++
  ".Lbveoh_pdone:"

def ziskBlockValidateEmptyOmmersHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bveoh_offset:\n" ++
  "  .zero 8\n" ++
  "bveoh_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bveoh_empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47"

def ziskBlockValidateEmptyOmmersHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateEmptyOmmersHashPrologue
  dataAsm     := ziskBlockValidateEmptyOmmersHashDataSection
}

/-! ## block_validate_no_withdrawals_pair -- PR-K180

    Pair check for blocks with no withdrawals: confirm both
    sides claim it.

      Header side: `header.withdrawals_root == EMPTY_TRIE_ROOT`
                   (= keccak256(rlp(b''))
                    = 0x56e81f17...3b421)
        via K161 `header_root_is_empty_trie` with field index 16.

      Body side: `block_body.field[2] (withdrawals) == rlp([])`
                 == `0xc0` (the empty-list RLP encoding).
        via K83 `block_body_decode` + 1-byte check.

    Both must hold; mismatch on either side fails the pair.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : body_rlp ptr
      a3 (input)  : body_rlp byte length
      a4 (input)  : u64 out (is_valid: 1 iff both predicates hold)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : body parse failure (not 3-item list)
        2 : header parse failure / field 16 missing
        3 : header field 16 length != 32 -/
def blockValidateNoWithdrawalsPairFunction : String :=
  "block_validate_no_withdrawals_pair:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2; mv s3, a3                # body\n" ++
  "  mv s4, a4                            # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Body side: withdrawals (field 2) == 0xc0 ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, bvnw_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbvnw_body_fail\n" ++
  "  la t0, bvnw_body_struct\n" ++
  "  ld t1, 32(t0)                       # withdrawals_offset\n" ++
  "  ld t2, 40(t0)                       # withdrawals_length\n" ++
  "  li t3, 1\n" ++
  "  bne t2, t3, .Lbvnw_pred_false\n" ++
  "  add t1, s2, t1\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbvnw_pred_false\n" ++
  "  # ---- Header side: withdrawals_root (field 16) == EMPTY_TRIE_ROOT ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, bvnw_field_off; la a4, bvnw_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvnw_header_parse_fail\n" ++
  "  la t0, bvnw_field_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvnw_header_size_fail\n" ++
  "  la t0, bvnw_field_off; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                              # &header.withdrawals_root\n" ++
  "  la t4, bvnw_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_body_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_header_parse_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_header_size_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lbvnw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_no_withdrawals_pair`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : body_rlp_len
      bytes 16..   : header_rlp || body_rlp
    Output layout:
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : is_valid -/
def ziskBlockValidateNoWithdrawalsPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 24              # header_rlp ptr\n" ++
  "  add a2, a0, a1               # body_rlp ptr\n" ++
  "  li a4, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_no_withdrawals_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvnw_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateNoWithdrawalsPairFunction ++ "\n" ++
  ".Lbvnw_pdone:"

def ziskBlockValidateNoWithdrawalsPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bvnw_body_struct:\n" ++
  "  .zero 48\n" ++
  "bvnw_field_off:\n" ++
  "  .zero 8\n" ++
  "bvnw_field_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bvnw_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"

def ziskBlockValidateNoWithdrawalsPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateNoWithdrawalsPairPrologue
  dataAsm     := ziskBlockValidateNoWithdrawalsPairDataSection
}

end EvmAsm.Codegen
