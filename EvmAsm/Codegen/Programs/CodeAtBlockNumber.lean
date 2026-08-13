/-
  EvmAsm.Codegen.Programs.CodeAtBlockNumber

  Number-keyed historical bytecode extractor. Pipeline:
  scan witness.headers for target block.number, extract
  state_root, walk to account code_hash, K19 over
  witness.codes.

  Number-keyed sibling of #7333 (block_hash) and #7417
  (state_root direct).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## code_at_block_number_address

    Pipeline:
      witness.headers ∋ ?h with h.block.number == target  [K233 scan]
      h -> header_extract_state_root                      [K201]
      state_root + address -> account.code_hash           [K28]
      code_hash + witness.codes -> (offset, length)       [K19]

    Completes the bytecode-extraction trio:
      | PR    | key            |
      |-------|----------------|
      | #7333 | block_hash     |
      | #7417 | state_root     |
      | this  | block_number   |

    Argument squeeze: 8 register args + 1 scratch label
    set by the prologue (cabn_code_offset_out_ptr).

    Status codes (10-way; distinguishes each stage of the
    pipeline):
      0 = success
      1 = no header with target block_number
      2 = K233 parse failure during scan
      3 = matched header state_root extraction failure
      4 = account absent in state trie
      5 = EMPTY_CODE_HASH (EOA / no code)
      6 = state-trie mpt parse error
      7 = account RLP decode failure
      8 = code_hash NOT in witness.codes
-/
def codeAtBlockNumberAddressFunction : String :=
  "code_at_block_number_address:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  sd t6, 104(sp)             # saw_parse_fail flag slot\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # witness.codes ptr\n" ++
  "  mv s7, a7                  # length out ptr (last)\n" ++
  "  la t6, cabn_codes_len\n" ++
  "  ld s8, 0(t6)               # witness.codes len\n" ++
  "  la t6, cabn_code_offset_out_ptr\n" ++
  "  ld s9, 0(t6)               # offset out ptr\n" ++
  "  sd zero, 0(s7)\n" ++
  "  sd zero, 0(s9)\n" ++
  "  li t6, 0\n" ++
  "  sd t6, 104(sp)             # saw_parse_fail = 0\n" ++
  "  beqz s2, .Lcabn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s10, t0, 2            # N\n" ++
  "  li s11, 0                  # i\n" ++
  ".Lcabn_loop:\n" ++
  "  beq s11, s10, .Lcabn_finish\n" ++
  "  slli t0, s11, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s1, t2             # el_i_start\n" ++
  "  addi t3, s11, 1\n" ++
  "  beq t3, s10, .Lcabn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lcabn_have_end\n" ++
  ".Lcabn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lcabn_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, cabn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lcabn_parse_fail\n" ++
  "  la t0, cabn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lcabn_hit\n" ++
  "  j .Lcabn_step\n" ++
  ".Lcabn_parse_fail:\n" ++
  "  li t6, 1\n" ++
  "  sd t6, 104(sp)\n" ++
  ".Lcabn_step:\n" ++
  "  addi s11, s11, 1\n" ++
  "  j .Lcabn_loop\n" ++
  ".Lcabn_hit:\n" ++
  "  # Re-derive header bounds for K201/K28.\n" ++
  "  slli t0, s11, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s1, t2             # header start\n" ++
  "  addi t3, s11, 1\n" ++
  "  beq t3, s10, .Lcabn_re_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lcabn_re_have\n" ++
  ".Lcabn_re_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lcabn_re_have:\n" ++
  "  sub a1, t4, a0             # header len\n" ++
  "  la a2, cabn_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lcabn_walk\n" ++
  "  li a0, 3\n" ++
  "  j .Lcabn_ret\n" ++
  ".Lcabn_walk:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, cabn_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la a5, cabn_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lcabn_check_empty\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcabn_absent\n" ++
  "  addi a0, a0, 4             # K28: 2 -> 6, 3 -> 7\n" ++
  "  j .Lcabn_ret\n" ++
  ".Lcabn_absent:\n" ++
  "  li a0, 4\n" ++
  "  j .Lcabn_ret\n" ++
  ".Lcabn_check_empty:\n" ++
  "  la t0, cabn_walked_struct\n" ++
  "  addi t0, t0, 72            # code_hash\n" ++
  "  la t1, cabn_empty_code_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lcabn_lookup\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lcabn_lookup\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lcabn_lookup\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lcabn_lookup\n" ++
  "  li a0, 5\n" ++
  "  j .Lcabn_ret\n" ++
  ".Lcabn_lookup:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  la t0, cabn_walked_struct\n" ++
  "  addi a2, t0, 72\n" ++
  "  mv a3, s9                  # offset out\n" ++
  "  mv a4, s7                  # length out\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  beqz a0, .Lcabn_done\n" ++
  "  li a0, 8\n" ++
  "  j .Lcabn_ret\n" ++
  ".Lcabn_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcabn_ret\n" ++
  ".Lcabn_finish:\n" ++
  "  ld t6, 104(sp)\n" ++
  "  bnez t6, .Lcabn_parse_status\n" ++
  ".Lcabn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcabn_ret\n" ++
  ".Lcabn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lcabn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  ld t6, 104(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

/-- `zisk_code_at_block_number_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_codes_len (u64 LE)
      bytes 32..40 : target_block_number (u64 LE)
      bytes 40..60 : address (20 bytes)
      bytes 60..   : witness.headers ++ witness.state ++ witness.codes
    Output layout (24 bytes):
      bytes  0.. 8 : status (0..8)
      bytes  8..16 : code_offset (u64)
      bytes 16..24 : code_length (u64) -/
def ziskCodeAtBlockNumberAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  ld t5, 24(t4)               # witness_codes_len\n" ++
  "  ld a0, 32(t4)               # target_block_number\n" ++
  "  addi a3, t4, 40             # address ptr\n" ++
  "  addi a1, t4, 60             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  add  a6, a4, a5             # witness.codes ptr\n" ++
  "  li a7, 0xa0010010           # length out\n" ++
  "  la t0, cabn_codes_len\n" ++
  "  sd t5, 0(t0)\n" ++
  "  la t0, cabn_code_offset_out_ptr\n" ++
  "  li t1, 0xa0010008\n" ++
  "  sd t1, 0(t0)\n" ++
  "  jal ra, code_at_block_number_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcabn_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  codeAtBlockNumberAddressFunction ++ "\n" ++
  ".Lcabn_pdone:"

def ziskCodeAtBlockNumberAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "cabn_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "cabn_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "cabn_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "cabn_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 8\n" ++
  "cabn_codes_len:\n" ++
  "  .zero 8\n" ++
  "cabn_code_offset_out_ptr:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
