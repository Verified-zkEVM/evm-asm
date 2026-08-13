/-
  EvmAsm.Codegen.Programs.ExtcodehashAtBlockNumber

  Number-keyed EIP-1052 EXTCODEHASH primitive. Sibling of
  ExtcodesizeAtBlockNumber (#7500 -- first EVM opcode at the
  block_number key level).

  Distinct from the plain `code_hash_at_block_number_address`
  extractor (#7486) in the EIP-1052 emptiness collapse:
  fully-empty accounts here yield 0, not EMPTY_CODE_HASH.

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

/-! ## extcodehash_at_block_number_address  (EIP-1052 at block_number)

    Returns the 32-byte EIP-1052 EXTCODEHASH value:
    `account.code_hash` when the account exists and is NOT
    EIP-161 empty, otherwise 0.

    EIP-1052 emptiness collapse distinguishes this from the
    plain code_hash extractor:

      | account contents       | code_hash extract | EXTCODEHASH |
      |------------------------|-------------------|-------------|
      | fully empty (in trie)  | EMPTY_CODE_HASH   | 0           |
      | nonce only             | EMPTY_CODE_HASH   | EMPTY_CODE_HASH |
      | balance only           | EMPTY_CODE_HASH   | EMPTY_CODE_HASH |
      | contract               | k256(code)        | k256(code)  |
      | (not in trie)          | 0                 | 0           |

    Block_number EVM opcode family progress:
      * extcodesize -- PR 7500
      * extcodehash -- THIS
      * extcodecopy -- (TODO)
      * sload       -- (TODO)

    Pipeline (composes K233 + K201 + K28 + EIP-161 check):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_state_root                      [K201]
      state_root + address -> account_at_address          [K28]
      if absent OR EIP-161 empty: return 0
      else: return account.code_hash

    Calling convention (7 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : 32-byte EXTCODEHASH out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (out buffer holds EIP-1052 result; may be 0)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header state_root extraction failure
        4 = state-trie mpt parse error
        5 = account RLP decode failure
-/
def extcodehashAtBlockNumberAddressFunction : String :=
  "extcodehash_at_block_number_address:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # target block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # 32 B output ptr\n" ++
  "  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)\n" ++
  "  li s9, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Leabn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s7, t0, 2             # N\n" ++
  "  li s8, 0                   # i\n" ++
  ".Leabn_loop:\n" ++
  "  beq s8, s7, .Leabn_finish\n" ++
  "  slli t0, s8, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s10, s1, t2            # header start\n" ++
  "  addi t3, s8, 1\n" ++
  "  beq t3, s7, .Leabn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Leabn_have_end\n" ++
  ".Leabn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Leabn_have_end:\n" ++
  "  sub t5, t4, s10\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, eabn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Leabn_parse_fail\n" ++
  "  la t0, eabn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Leabn_hit\n" ++
  "  j .Leabn_step\n" ++
  ".Leabn_parse_fail:\n" ++
  "  li s9, 1\n" ++
  ".Leabn_step:\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Leabn_loop\n" ++
  ".Leabn_hit:\n" ++
  "  slli t0, s8, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  addi t3, s8, 1\n" ++
  "  beq t3, s7, .Leabn_re_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  j .Leabn_re_have_end\n" ++
  ".Leabn_re_use_end:\n" ++
  "  mv t4, s2\n" ++
  ".Leabn_re_have_end:\n" ++
  "  sub t5, t4, t2\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, eabn_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Leabn_walk\n" ++
  "  li a0, 3\n" ++
  "  j .Leabn_ret\n" ++
  ".Leabn_walk:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, eabn_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la a5, eabn_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Leabn_check_empty\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Leabn_success_zero\n" ++
  "  addi a0, a0, 2             # 2->4, 3->5\n" ++
  "  j .Leabn_ret\n" ++
  ".Leabn_success_zero:\n" ++
  "  li a0, 0\n" ++
  "  j .Leabn_ret\n" ++
  ".Leabn_check_empty:\n" ++
  "  la t3, eabn_walked_struct\n" ++
  "  ld t1, 0(t3)\n" ++
  "  bnez t1, .Leabn_write_code_hash\n" ++
  "  ld t1,  8(t3); bnez t1, .Leabn_write_code_hash\n" ++
  "  ld t1, 16(t3); bnez t1, .Leabn_write_code_hash\n" ++
  "  ld t1, 24(t3); bnez t1, .Leabn_write_code_hash\n" ++
  "  ld t1, 32(t3); bnez t1, .Leabn_write_code_hash\n" ++
  "  la t0, eabn_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(t3); bne t1, t2, .Leabn_write_code_hash\n" ++
  "  ld t1,  8(t0); ld t2, 80(t3); bne t1, t2, .Leabn_write_code_hash\n" ++
  "  ld t1, 16(t0); ld t2, 88(t3); bne t1, t2, .Leabn_write_code_hash\n" ++
  "  ld t1, 24(t0); ld t2, 96(t3); bne t1, t2, .Leabn_write_code_hash\n" ++
  "  # EIP-161 empty -> output stays zero (EIP-1052 collapse).\n" ++
  "  li a0, 0\n" ++
  "  j .Leabn_ret\n" ++
  ".Leabn_write_code_hash:\n" ++
  "  ld t1, 72(t3); sd t1,  0(s6)\n" ++
  "  ld t1, 80(t3); sd t1,  8(s6)\n" ++
  "  ld t1, 88(t3); sd t1, 16(s6)\n" ++
  "  ld t1, 96(t3); sd t1, 24(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Leabn_ret\n" ++
  ".Leabn_finish:\n" ++
  "  bnez s9, .Leabn_parse_status\n" ++
  ".Leabn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Leabn_ret\n" ++
  ".Leabn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Leabn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_extcodehash_at_block_number_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : target_block_number (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..   : witness.headers ++ witness.state
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..5)
      bytes  8..40 : EXTCODEHASH (32 B; 0 on missing/empty) -/
def ziskExtcodehashAtBlockNumberAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  ld a0, 24(t4)               # target_block_number\n" ++
  "  addi a3, t4, 32             # address ptr\n" ++
  "  addi a1, t4, 52             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # 32 B output ptr\n" ++
  "  jal ra, extcodehash_at_block_number_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Leabn_pdone\n" ++
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
  extcodehashAtBlockNumberAddressFunction ++ "\n" ++
  ".Leabn_pdone:"

def ziskExtcodehashAtBlockNumberAddressDataSection : String :=
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
  "eabn_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "eabn_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "eabn_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "eabn_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
