/-
  EvmAsm.Codegen.Programs.ExtcodecopyAtBlockNumber

  Number-keyed EXTCODECOPY primitive. Mirrors
  `extcodecopy_at_block_hash_address` (#7477) but takes a
  block_number key. COMPLETES the block_number EVM-opcode
  family started by:
    * extcodesize -- PR 7500
    * extcodehash -- PR 7507
    * sload       -- PR 7514

  EXTCODECOPY is the only EVM opcode that emits code bytes
  into EVM memory, with the spec-defining zero-pad-past-end
  rule. Has too many inputs to fit RISC-V's 8 a-regs, so
  3 ptrs are stashed via global scratches in the prologue.

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

/-! ## extcodecopy_at_block_number_address  (EXTCODECOPY at block_number)

    Writes `length` bytes of `address`'s deployed code
    starting at `code_offset` into a caller-supplied output
    buffer, evaluated against the state of the block at
    `target_block_number`. Reads past the end of the code
    are zero-padded; missing accounts and empty-code accounts
    map to all-zeros output (status 0).

    Block_number EVM opcode family progress (now complete):
      * extcodesize -- PR 7500
      * extcodehash -- PR 7507
      * sload       -- PR 7514
      * extcodecopy -- THIS

    Pipeline (composes K233 + K201 + K28 + K19 + inline byte
    copy; no new helpers):

      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_state_root                      [K201]
      state_root + address -> account_at_address          [K28]
      if absent OR code_hash == EMPTY: output zeros, return 0
      else: witness.codes ∋ ?c with keccak(c) == code_hash [K19]
            for i in 0..length:
              output[i] = c[code_offset+i] if code_offset+i < len(c) else 0

    Has 11 effective inputs vs RISC-V's 8 a-regs; uses 3 global
    scratches (same pattern as `extcodecopy_at_block_hash_address`):
      * eccpbn_witness_state_len
      * eccpbn_codes_ptr
      * eccpbn_codes_len

    Calling convention (8 a-regs + 3 global scratches):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : code_offset (u64)
      a5 (input)  : length (u64; must be <= 256)
      a6 (input)  : output buffer ptr (`length` bytes)
      a7 (input)  : witness.state ptr
      [scratch]   : eccpbn_witness_state_len, eccpbn_codes_ptr,
                    eccpbn_codes_len -- caller-set.
      ra (input)  : return

      a0 (output) :
        0 = success (output filled, zero-padded as needed)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header state_root extraction failure
        4 = state-trie mpt parse error
        5 = account_decode failure
        6 = code_hash != EMPTY but not found in witness.codes
            (witness integrity violation)
        7 = length > 256 (probe cap; not a spec issue)
-/
def extcodecopyAtBlockNumberAddressFunction : String :=
  "extcodecopy_at_block_number_address:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra,   0(sp)\n" ++
  "  sd s0,   8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4,  40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8,  72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  sd tp, 104(sp); sd gp, 112(sp)\n" ++
  "  mv s0, a0                  # target block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # code_offset\n" ++
  "  mv s5, a5                  # length\n" ++
  "  mv s6, a6                  # output buffer ptr\n" ++
  "  mv s7, a7                  # witness.state ptr\n" ++
  "  la t0, eccpbn_witness_state_len\n" ++
  "  ld s11, 0(t0)              # witness.state len\n" ++
  "  li t0, 256\n" ++
  "  bgtu s5, t0, .Leccpbn_too_long\n" ++
  "  mv t0, s6\n" ++
  "  mv t1, s5\n" ++
  ".Leccpbn_zero_loop:\n" ++
  "  beqz t1, .Leccpbn_zero_done\n" ++
  "  sb zero, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Leccpbn_zero_loop\n" ++
  ".Leccpbn_zero_done:\n" ++
  "  li gp, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Leccpbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s8, t0, 2             # N\n" ++
  "  li s9, 0                   # i\n" ++
  ".Leccpbn_loop:\n" ++
  "  beq s9, s8, .Leccpbn_finish\n" ++
  "  slli t0, s9, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s10, s1, t2            # header start\n" ++
  "  addi t3, s9, 1\n" ++
  "  beq t3, s8, .Leccpbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Leccpbn_have_end\n" ++
  ".Leccpbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Leccpbn_have_end:\n" ++
  "  sub t5, t4, s10\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, eccpbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Leccpbn_parse_fail\n" ++
  "  la t0, eccpbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Leccpbn_hit\n" ++
  "  j .Leccpbn_step\n" ++
  ".Leccpbn_parse_fail:\n" ++
  "  li gp, 1\n" ++
  ".Leccpbn_step:\n" ++
  "  addi s9, s9, 1\n" ++
  "  j .Leccpbn_loop\n" ++
  ".Leccpbn_hit:\n" ++
  "  slli t0, s9, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  addi t3, s9, 1\n" ++
  "  beq t3, s8, .Leccpbn_re_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  j .Leccpbn_re_have_end\n" ++
  ".Leccpbn_re_use_end:\n" ++
  "  mv t4, s2\n" ++
  ".Leccpbn_re_have_end:\n" ++
  "  sub t5, t4, t2\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, eccpbn_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Leccpbn_step2\n" ++
  "  li a0, 3\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_step2:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, eccpbn_state_root\n" ++
  "  mv a3, s7\n" ++
  "  mv a4, s11\n" ++
  "  la tp, eccpbn_acct_struct\n" ++
  "  mv a5, tp\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Leccpbn_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Leccpbn_success_zero\n" ++
  "  addi a0, a0, 2             # 2->4, 3->5\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_success_zero:\n" ++
  "  li a0, 0\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_step3:\n" ++
  "  la t0, eccpbn_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(tp); bne t1, t2, .Leccpbn_step4\n" ++
  "  ld t1,  8(t0); ld t2, 80(tp); bne t1, t2, .Leccpbn_step4\n" ++
  "  ld t1, 16(t0); ld t2, 88(tp); bne t1, t2, .Leccpbn_step4\n" ++
  "  ld t1, 24(t0); ld t2, 96(tp); bne t1, t2, .Leccpbn_step4\n" ++
  "  li a0, 0\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_step4:\n" ++
  "  la t0, eccpbn_codes_ptr; ld a0, 0(t0)\n" ++
  "  la t0, eccpbn_codes_len; ld a1, 0(t0)\n" ++
  "  addi a2, tp, 72            # &acct.code_hash\n" ++
  "  la a3, eccpbn_code_match_offset\n" ++
  "  la a4, eccpbn_code_match_len\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  beqz a0, .Leccpbn_step5\n" ++
  "  li a0, 6\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_step5:\n" ++
  "  la t0, eccpbn_codes_ptr; ld t1, 0(t0)\n" ++
  "  la t0, eccpbn_code_match_offset; ld t2, 0(t0)\n" ++
  "  add s11, t1, t2            # reuse s11 for code_ptr\n" ++
  "  la t0, eccpbn_code_match_len; ld t3, 0(t0)\n" ++
  "  li t0, 0                   # i\n" ++
  ".Leccpbn_copy_loop:\n" ++
  "  beq t0, s5, .Leccpbn_copy_done\n" ++
  "  add t1, s4, t0\n" ++
  "  bgeu t1, t3, .Leccpbn_pad\n" ++
  "  add t2, s11, t1\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  add t5, s6, t0\n" ++
  "  sb t4, 0(t5)\n" ++
  ".Leccpbn_pad:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Leccpbn_copy_loop\n" ++
  ".Leccpbn_copy_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_too_long:\n" ++
  "  li a0, 7\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_finish:\n" ++
  "  bnez gp, .Leccpbn_parse_status\n" ++
  ".Leccpbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Leccpbn_ret\n" ++
  ".Leccpbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Leccpbn_ret:\n" ++
  "  ld ra,   0(sp)\n" ++
  "  ld s0,   8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4,  40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8,  72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  ld tp, 104(sp); ld gp, 112(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

/-- `zisk_extcodecopy_at_block_number_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_codes_len   (u64 LE)
      bytes 32..40 : target_block_number (u64 LE)
      bytes 40..48 : code_offset (u64 LE)
      bytes 48..56 : length (u64 LE; must be <= 256)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.headers ++ witness.state ++ witness.codes
    Output layout:
      bytes  0.. 8 : status (0..7)
      bytes  8..16 : effective length (= length on success; 0 otherwise)
      bytes 16..(16+length) : copied code bytes, zero-padded -/
def ziskExtcodecopyAtBlockNumberAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld t5,  8(t4)               # witness_headers_len\n" ++
  "  ld t6, 16(t4)               # witness_state_len\n" ++
  "  ld t3, 24(t4)               # witness_codes_len\n" ++
  "  ld a0, 32(t4)               # target_block_number\n" ++
  "  ld a4, 40(t4)               # code_offset\n" ++
  "  ld a5, 48(t4)               # length\n" ++
  "  mv s1, a5                   # stash length for output effective-length\n" ++
  "  addi a3, t4, 56             # address ptr\n" ++
  "  addi a1, t4, 76             # witness.headers ptr\n" ++
  "  mv a2, t5\n" ++
  "  add a7, a1, t5              # witness.state ptr\n" ++
  "  la t0, eccpbn_witness_state_len; sd t6, 0(t0)\n" ++
  "  add t1, a7, t6              # witness.codes ptr\n" ++
  "  la t0, eccpbn_codes_ptr; sd t1, 0(t0)\n" ++
  "  la t0, eccpbn_codes_len; sd t3, 0(t0)\n" ++
  "  li a6, 0xa0010010           # output buffer at OUTPUT + 16\n" ++
  "  jal ra, extcodecopy_at_block_number_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  bnez a0, .Leccpbn_no_len\n" ++
  "  sd s1, 8(t0)\n" ++
  "  j .Leccpbn_pdone\n" ++
  ".Leccpbn_no_len:\n" ++
  "  sd zero, 8(t0)\n" ++
  "  j .Leccpbn_pdone\n" ++
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
  extcodecopyAtBlockNumberAddressFunction ++ "\n" ++
  ".Leccpbn_pdone:"

def ziskExtcodecopyAtBlockNumberAddressDataSection : String :=
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
  "eccpbn_witness_state_len:\n" ++
  "  .zero 8\n" ++
  "eccpbn_codes_ptr:\n" ++
  "  .zero 8\n" ++
  "eccpbn_codes_len:\n" ++
  "  .zero 8\n" ++
  "eccpbn_code_match_offset:\n" ++
  "  .zero 8\n" ++
  "eccpbn_code_match_len:\n" ++
  "  .zero 8\n" ++
  "eccpbn_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "eccpbn_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "eccpbn_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "eccpbn_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
