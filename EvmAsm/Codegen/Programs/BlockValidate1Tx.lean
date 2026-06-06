/-
  EvmAsm.Codegen.Programs.BlockValidate1Tx

  One-transaction block body extraction and validation probes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockValidate

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_body_extract_1tx -- PR-K188

    Body-side primitive for 1-tx blocks: decode a 3-field body
    (`[transactions, ommers, withdrawals]`), assert exactly one
    transaction and the empty ommers list (post-merge invariant),
    and return `(tx0 off+len)` in body-relative coordinates.

    Analogue of K177 `block_body_extract_2tx` for N=1.

    Output struct (16 bytes):
       0..  8  tx0_offset (in body_rlp)
       8.. 16  tx0_length

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 16-byte output struct ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body RLP parse failure
        2 : ommers not the empty list
        3 : transactions list count != 1
        4 : transactions list item extraction failure -/
def blockBodyExtract1txFunction : String :=
  "block_body_extract_1tx:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_rlp len\n" ++
  "  mv s2, a2                   # output struct\n" ++
  "  # (1) Decode body\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bbe1_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbe1_parse_fail\n" ++
  "  # (2) Verify ommers == 0xc0\n" ++
  "  la t0, bbe1_body_struct; ld t1, 16(t0)\n" ++
  "  ld t2, 24(t0)\n" ++
  "  li t3, 1\n" ++
  "  bne t2, t3, .Lbbe1_ommers_fail\n" ++
  "  add t1, s0, t1; lbu t4, 0(t1); li t5, 0xc0; bne t4, t5, .Lbbe1_ommers_fail\n" ++
  "  # (3) Count tx list\n" ++
  "  la t0, bbe1_body_struct; ld s3, 0(t0); ld s4, 8(t0)\n" ++
  "  add a0, s0, s3; mv a1, s4\n" ++
  "  la a2, bbe1_tx_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbe1_txs_fail\n" ++
  "  la t0, bbe1_tx_count; ld t1, 0(t0)\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbbe1_count_fail\n" ++
  "  # (4) Extract tx0\n" ++
  "  add a0, s0, s3; mv a1, s4; li a2, 0\n" ++
  "  la a3, bbe1_item_off; la a4, bbe1_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbe1_txs_fail\n" ++
  "  la t0, bbe1_item_off; ld t1, 0(t0)\n" ++
  "  add t1, t1, s3; sd t1, 0(s2)\n" ++
  "  la t0, bbe1_item_len; ld t1, 0(t0); sd t1, 8(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbe1_ret\n" ++
  ".Lbbe1_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbbe1_ret\n" ++
  ".Lbbe1_ommers_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbbe1_ret\n" ++
  ".Lbbe1_count_fail:\n" ++
  "  li a0, 3\n" ++
  "  j .Lbbe1_ret\n" ++
  ".Lbbe1_txs_fail:\n" ++
  "  li a0, 4\n" ++
  ".Lbbe1_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_body_extract_1tx`: probe BuildUnit.
    Input layout:
      bytes 0..8 : body_rlp_len
      bytes 8..  : body_rlp
    Output layout:
      bytes  0.. 8 : status (0..4)
      bytes  8..24 : 16-byte struct (tx0 off+len) -/
def ziskBlockBodyExtract1txPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 16             # body_rlp ptr\n" ++
  "  li a2, 0xa0010008           # output struct\n" ++
  "  jal ra, block_body_extract_1tx\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbbe1_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtract1txFunction ++ "\n" ++
  ".Lbbe1_pdone:"

def ziskBlockBodyExtract1txDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbe1_body_struct:\n" ++
  "  .zero 48\n" ++
  "bbe1_tx_count:\n" ++
  "  .zero 8\n" ++
  "bbe1_item_off:\n" ++
  "  .zero 8\n" ++
  "bbe1_item_len:\n" ++
  "  .zero 8"

def ziskBlockBodyExtract1txProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyExtract1txPrologue
  dataAsm     := ziskBlockBodyExtract1txDataSection
}

/-! ## block_validate_1tx_full -- PR-K189

    Full validator for a 1-tx Ethereum block: combines the
    per-pair header invariants (K174) with the
    `transactions_root` MPT match (K186) for the N=1 case.
    N=1 analogue of K176 `block_validate_2tx_full`.

    Returns `is_valid = 1` iff both:
      1. validate_header_pair(parent, header) accepts (parent_hash
         link, number+1, timestamp >, gas_limit ratio).
      2. block_validate_transactions_root_one_tx(header, tx0)
         accepts (header.transactions_root matches the
         single-leaf trie root).

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : header_rlp ptr
      a3 (input)  : header_rlp byte length
      a4 (input)  : tx0 ptr
      a5 (input)  : tx0 byte length
      a6 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0  success -- predicate written
        1..4   propagated from validate_header_pair
        11..12 propagated from
               `block_validate_transactions_root_one_tx`
               (status 1 / 2 shifted to 11 / 12) -/
def blockValidate1txFullFunction : String :=
  "block_validate_1tx_full:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # header\n" ++
  "  mv s4, a4; mv s5, a5                # tx0\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # ---- (A) Header pair check ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, bv1f_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  beqz a0, .Lbv1f_pair_status_ok\n" ++
  "  j .Lbv1f_ret                  # propagate pair status 1..4\n" ++
  ".Lbv1f_pair_status_ok:\n" ++
  "  la t0, bv1f_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv1f_pred_false\n" ++
  "  # ---- (B) 1-tx tx_root check ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  mv a2, s4; mv a3, s5\n" ++
  "  la a4, bv1f_tx_root_valid\n" ++
  "  jal ra, block_validate_transactions_root_one_tx\n" ++
  "  beqz a0, .Lbv1f_tx_root_status_ok\n" ++
  "  addi a0, a0, 10               # remap 1..2 -> 11..12\n" ++
  "  j .Lbv1f_ret\n" ++
  ".Lbv1f_tx_root_status_ok:\n" ++
  "  la t0, bv1f_tx_root_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv1f_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbv1f_ret\n" ++
  ".Lbv1f_pred_false:\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li a0, 0\n" ++
  ".Lbv1f_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_1tx_full`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : header_rlp_len
      bytes 16..24 : tx0_len
      bytes 24..   : parent_rlp || header_rlp || tx0
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskBlockValidate1txFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)                # header_rlp_len\n" ++
  "  ld a5, 24(a7)                # tx0_len\n" ++
  "  addi a0, a7, 32              # parent_rlp ptr\n" ++
  "  add a2, a0, a1               # header_rlp ptr\n" ++
  "  add a4, a2, a3               # tx0 ptr\n" ++
  "  li a6, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_1tx_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbv1f_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockValidateTransactionsRootOneTxFunction ++ "\n" ++
  blockValidate1txFullFunction ++ "\n" ++
  ".Lbv1f_pdone:"

def ziskBlockValidate1txFullDataSection : String :=
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
  "  .zero 32\n" ++
  "bv1f_pair_valid:\n" ++
  "  .zero 8\n" ++
  "bv1f_tx_root_valid:\n" ++
  "  .zero 8"

def ziskBlockValidate1txFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidate1txFullPrologue
  dataAsm     := ziskBlockValidate1txFullDataSection
}

/-! ## block_validate_1tx_full_with_body -- PR-K190

    Body-aware single-call validator for a 1-tx block: takes
    `(parent_rlp, header_rlp, body_rlp)`, returns `is_valid`.
    Composes K188 (body extract) + K189 (header pair + tx_root).

    Algorithm:
      1. K188 `block_body_extract_1tx(body)` -- assert body shape
         (3 fields, empty ommers, exactly 1 tx); return tx0 ptr+len.
      2. K189 `block_validate_1tx_full(parent, header, tx0)` --
         verify pair invariants + tx_root match.

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
        0        success
        1..4     body-extract status (K188)
        11..14   pair status (K174 / K189 codes 1..4 + 10)
        21..22   tx-root status (K186 / K189 codes 11..12 + 10) -/
def blockValidate1txFullWithBodyFunction : String :=
  "block_validate_1tx_full_with_body:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # header\n" ++
  "  mv s4, a4; mv s5, a5                # body\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # (A) Extract tx0 from body\n" ++
  "  mv a0, s4; mv a1, s5\n" ++
  "  la a2, bv1fb_struct\n" ++
  "  jal ra, block_body_extract_1tx\n" ++
  "  beqz a0, .Lbv1fb_body_ok\n" ++
  "  j .Lbv1fb_ret               # propagate body status 1..4\n" ++
  ".Lbv1fb_body_ok:\n" ++
  "  la t0, bv1fb_struct; ld t1, 0(t0); ld t2, 8(t0)\n" ++
  "  add t1, s4, t1              # tx0 ptr = body + off\n" ++
  "  # (B) K189 1-tx full validator\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  mv a4, t1; mv a5, t2\n" ++
  "  mv a6, s6\n" ++
  "  jal ra, block_validate_1tx_full\n" ++
  "  beqz a0, .Lbv1fb_ret\n" ++
  "  # K189 status 1..4 (pair) -> remap to 11..14\n" ++
  "  # K189 status 11..12 (tx_root) -> remap to 21..22\n" ++
  "  li t0, 5\n" ++
  "  bltu a0, t0, .Lbv1fb_remap_pair\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lbv1fb_ret\n" ++
  ".Lbv1fb_remap_pair:\n" ++
  "  addi a0, a0, 10\n" ++
  ".Lbv1fb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_1tx_full_with_body`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : header_rlp_len
      bytes 16..24 : body_rlp_len
      bytes 24..   : parent_rlp || header_rlp || body_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskBlockValidate1txFullWithBodyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)                # header_rlp_len\n" ++
  "  ld a5, 24(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 32              # parent_rlp ptr\n" ++
  "  add a2, a0, a1               # header_rlp ptr\n" ++
  "  add a4, a2, a3               # body_rlp ptr\n" ++
  "  li a6, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_1tx_full_with_body\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbv1fb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockValidateTransactionsRootOneTxFunction ++ "\n" ++
  blockValidate1txFullFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtract1txFunction ++ "\n" ++
  blockValidate1txFullWithBodyFunction ++ "\n" ++
  ".Lbv1fb_pdone:"

def ziskBlockValidate1txFullWithBodyDataSection : String :=
  ziskBlockValidate1txFullDataSection ++ "\n" ++
  "bv1fb_struct:\n" ++
  "  .zero 16\n" ++
  "bbe1_body_struct:\n" ++
  "  .zero 48\n" ++
  "bbe1_tx_count:\n" ++
  "  .zero 8\n" ++
  "bbe1_item_off:\n" ++
  "  .zero 8\n" ++
  "bbe1_item_len:\n" ++
  "  .zero 8"

def ziskBlockValidate1txFullWithBodyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidate1txFullWithBodyPrologue
  dataAsm     := ziskBlockValidate1txFullWithBodyDataSection
}



end EvmAsm.Codegen
