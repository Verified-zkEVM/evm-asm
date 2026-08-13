/-
  EvmAsm.Codegen.Programs.ExtcodecopyAtBlockHash

  Hash-keyed EXTCODECOPY primitive. Mirrors the existing
  `extcodecopy_at_header_state_root` (under
  EvmOpcodesExtcodecopy) but takes a `block_hash` as the
  key instead of raw header bytes.

  EXTCODECOPY is the only EVM opcode that actually emits
  code bytes into EVM memory. Its spec divergence from a
  naive byte-copy is the zero-pad rule:

      for i in 0..length:
        output[i] = code[code_offset + i] if code_offset + i < len(code) else 0

  Reads past the end of the code are zero-padded, NOT
  truncated, NOT errored.

  This primitive has too many inputs to fit RISC-V's 8
  a-registers, so several get stashed via global scratch
  labels before the call -- the same pattern established
  by sload_at_block_hash_address.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## extcodecopy_at_block_hash_address  (EXTCODECOPY at block_hash)

    Writes `length` bytes of `address`'s deployed code
    starting at `code_offset` into a caller-supplied output
    buffer, evaluated against the state of the block named
    by `block_hash`. Reads past the end of the code are
    zero-padded; missing accounts and empty-code accounts
    map to all-zeros output (status 0).

    Completes the EXT* trio at block_hash:
      * extcodesize (#7470) -- u64 length
      * extcodehash (#7474) -- 32 B EIP-1052 hash
      * extcodecopy (THIS)  -- bytes with zero-pad-past-end

    Use cases:
      * EXTCODECOPY opcode replay against a historical
        block keyed by hash.
      * Off-chain code-inspection oracles when the caller
        identifies blocks by hash, not number / state_root.
      * Code-equality checks across forks: copy a fixed
        window at two block_hashes, diff in caller.

    Pipeline (composes K19 + K201 + K28 + K19' + inline
    zero-padded byte copy; no new helpers):

      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_state_root                     [K201]
      state_root + address -> account_at_address         [K28]
      if account absent OR code_hash == EMPTY_CODE_HASH:
        output := all zeros, return 0 (spec)
      else:
        witness.codes ∋ ?c with keccak(c) == code_hash    [K19']
        for i in 0..length:
          output[i] = c[code_offset+i] if code_offset+i < len(c) else 0

    Calling convention (8 a-regs + 3 global scratches):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : code_offset (u64)
      a5 (input)  : length (u64; must be <= 256)
      a6 (input)  : output buffer ptr (`length` bytes)
      a7 (input)  : witness.state ptr
      [scratch ecccbh_witness_state_len] : witness.state len
      [scratch ecccbh_codes_ptr]         : witness.codes ptr
      [scratch ecccbh_codes_len]         : witness.codes len
      ra (input)  : return

      a0 (output) :
        0 = success (output filled, zero-padded as needed)
        1 = block_hash not in witness.headers
        2 = matched header parse / state_root size fail
        3 = state-trie mpt parse error
        4 = account_decode failure
        5 = code_hash != EMPTY but not found in witness.codes
            (witness integrity violation)
        6 = length > 256 (probe cap; not a spec issue)
-/
def extcodecopyAtBlockHashAddressFunction : String :=
  "extcodecopy_at_block_hash_address:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # code_offset\n" ++
  "  mv s5, a5                  # length\n" ++
  "  mv s6, a6                  # output buffer ptr\n" ++
  "  mv s7, a7                  # witness.state ptr\n" ++
  "  la t0, ecccbh_witness_state_len\n" ++
  "  ld s11, 0(t0)              # witness.state len\n" ++
  "  li t0, 256\n" ++
  "  bgtu s5, t0, .Lecccbh_too_long\n" ++
  "  # Pre-zero output[0..length] byte-by-byte.\n" ++
  "  mv t0, s6\n" ++
  "  mv t1, s5\n" ++
  ".Lecccbh_zero_loop:\n" ++
  "  beqz t1, .Lecccbh_zero_done\n" ++
  "  sb zero, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lecccbh_zero_loop\n" ++
  ".Lecccbh_zero_done:\n" ++
  "  # Step 0: K19 on witness.headers by block_hash.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, ecccbh_match_offset\n" ++
  "  la a4, ecccbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lecccbh_no_match\n" ++
  "  la t0, ecccbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s8, s1, t1\n" ++
  "  la t0, ecccbh_match_length\n" ++
  "  ld s9, 0(t0)\n" ++
  "  # Step 1: header.state_root.\n" ++
  "  mv a0, s8\n" ++
  "  mv a1, s9\n" ++
  "  la a2, ecccbh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lecccbh_step2\n" ++
  "  li a0, 2\n" ++
  "  j .Lecccbh_ret\n" ++
  ".Lecccbh_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, ecccbh_state_root\n" ++
  "  mv a3, s7\n" ++
  "  mv a4, s11\n" ++
  "  la s10, ecccbh_acct_struct\n" ++
  "  mv a5, s10\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lecccbh_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lecccbh_success_zero\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lecccbh_ret\n" ++
  ".Lecccbh_success_zero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lecccbh_ret\n" ++
  ".Lecccbh_step3:\n" ++
  "  # Check code_hash == EMPTY_CODE_HASH.\n" ++
  "  la t0, ecccbh_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(s10); bne t1, t2, .Lecccbh_step4\n" ++
  "  ld t1,  8(t0); ld t2, 80(s10); bne t1, t2, .Lecccbh_step4\n" ++
  "  ld t1, 16(t0); ld t2, 88(s10); bne t1, t2, .Lecccbh_step4\n" ++
  "  ld t1, 24(t0); ld t2, 96(s10); bne t1, t2, .Lecccbh_step4\n" ++
  "  # Empty code; output stays zero.\n" ++
  "  li a0, 0\n" ++
  "  j .Lecccbh_ret\n" ++
  ".Lecccbh_step4:\n" ++
  "  # Step 4: K19 on witness.codes by code_hash.\n" ++
  "  la t0, ecccbh_codes_ptr; ld a0, 0(t0)\n" ++
  "  la t0, ecccbh_codes_len; ld a1, 0(t0)\n" ++
  "  addi a2, s10, 72           # &acct.code_hash\n" ++
  "  la a3, ecccbh_code_match_offset\n" ++
  "  la a4, ecccbh_code_match_len\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  beqz a0, .Lecccbh_step5\n" ++
  "  li a0, 5\n" ++
  "  j .Lecccbh_ret\n" ++
  ".Lecccbh_step5:\n" ++
  "  # code_ptr = codes_ptr + match_offset; code_len = match_len.\n" ++
  "  la t0, ecccbh_codes_ptr; ld t1, 0(t0)\n" ++
  "  la t0, ecccbh_code_match_offset; ld t2, 0(t0)\n" ++
  "  add s11, t1, t2            # reusing s11 for code_ptr\n" ++
  "  la t0, ecccbh_code_match_len; ld t3, 0(t0)\n" ++
  "  # Byte-by-byte zero-padded copy.\n" ++
  "  li t0, 0                   # i\n" ++
  ".Lecccbh_copy_loop:\n" ++
  "  beq t0, s5, .Lecccbh_copy_done\n" ++
  "  add t1, s4, t0             # src_idx = code_offset + i\n" ++
  "  bgeu t1, t3, .Lecccbh_pad  # past code end -> already zero\n" ++
  "  add t2, s11, t1\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  add t5, s6, t0\n" ++
  "  sb t4, 0(t5)\n" ++
  ".Lecccbh_pad:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lecccbh_copy_loop\n" ++
  ".Lecccbh_copy_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lecccbh_ret\n" ++
  ".Lecccbh_too_long:\n" ++
  "  li a0, 6\n" ++
  "  j .Lecccbh_ret\n" ++
  ".Lecccbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lecccbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_extcodecopy_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_codes_len   (u64 LE)
      bytes 32..40 : code_offset (u64 LE)
      bytes 40..48 : length (u64 LE; must be <= 256)
      bytes 48..80 : block_hash (32 bytes)
      bytes 80..100: address (20 bytes)
      bytes 100..  : witness.headers ++ witness.state ++ witness.codes
    Output layout:
      bytes  0.. 8 : status (0..6)
      bytes  8..16 : effective length (= length on success; 0 otherwise)
      bytes 16..(16+length) : copied code bytes, zero-padded -/
def ziskExtcodecopyAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld t5,  8(t4)               # witness_headers_len\n" ++
  "  ld t6, 16(t4)               # witness_state_len\n" ++
  "  ld t3, 24(t4)               # witness_codes_len\n" ++
  "  ld a4, 32(t4)               # code_offset\n" ++
  "  ld a5, 40(t4)               # length\n" ++
  "  mv s1, a5                   # stash length for output effective-length write\n" ++
  "  addi a0, t4, 48             # block_hash ptr\n" ++
  "  addi a3, t4, 80             # address ptr\n" ++
  "  addi a1, t4, 100            # witness.headers ptr\n" ++
  "  mv a2, t5                   # witness.headers len\n" ++
  "  add a7, a1, t5              # witness.state ptr\n" ++
  "  la t0, ecccbh_witness_state_len; sd t6, 0(t0)\n" ++
  "  add t1, a7, t6              # witness.codes ptr\n" ++
  "  la t0, ecccbh_codes_ptr; sd t1, 0(t0)\n" ++
  "  la t0, ecccbh_codes_len; sd t3, 0(t0)\n" ++
  "  li a6, 0xa0010010           # output buffer at OUTPUT + 16\n" ++
  "  jal ra, extcodecopy_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  bnez a0, .Lecccbh_no_len\n" ++
  "  sd s1, 8(t0)\n" ++
  "  j .Lecccbh_pdone\n" ++
  ".Lecccbh_no_len:\n" ++
  "  sd zero, 8(t0)\n" ++
  "  j .Lecccbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  extcodecopyAtBlockHashAddressFunction ++ "\n" ++
  ".Lecccbh_pdone:"

def ziskExtcodecopyAtBlockHashAddressDataSection : String :=
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
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ecccbh_witness_state_len:\n" ++
  "  .zero 8\n" ++
  "ecccbh_codes_ptr:\n" ++
  "  .zero 8\n" ++
  "ecccbh_codes_len:\n" ++
  "  .zero 8\n" ++
  "ecccbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "ecccbh_match_length:\n" ++
  "  .zero 8\n" ++
  "ecccbh_code_match_offset:\n" ++
  "  .zero 8\n" ++
  "ecccbh_code_match_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecccbh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecccbh_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "ecccbh_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
