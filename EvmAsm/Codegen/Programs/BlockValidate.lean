/-
  EvmAsm.Codegen.Programs.BlockValidate

  Block-level full-validation predicates carved out of
  `EvmAsm.Codegen.Programs.Block` per the file-size hard cap.
  Hosts:

    K176  block_validate_2tx_full
    K179  block_validate_empty_ommers_hash
    K181  block_validate_empty_receipts_root

  These compose header validators, MPT root computers, and
  various RLP helpers.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
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

end EvmAsm.Codegen
