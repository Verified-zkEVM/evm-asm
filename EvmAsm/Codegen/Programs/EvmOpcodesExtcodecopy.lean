/-
  EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy

  EXTCODECOPY opcode probe — carved out of EvmOpcodes.lean to
  stay under the file-size hard cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.WitnessCodeLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## extcodecopy_at_header_state_root  (EVM EXTCODECOPY opcode)

    Witness-side implementation of the EVM EXTCODECOPY opcode.
    Given a parent header RLP, an address, a code offset, a
    length, an SSZ `witness.state` list, and an SSZ
    `witness.codes` list, write `length` bytes into a
    caller-supplied output buffer:

        for i in 0..length:
          output[i] = code[code_offset + i] if code_offset + i < len(code) else 0

    i.e., reads past the end of the code are zero-padded
    (NOT truncated, NOT errored). This zero-pad rule is the
    EXTCODECOPY-specific spec divergence from a naive byte-copy.

    Distinct from PR `code_at_header_state_root` (which returns
    the full code's offset/length in witness.codes without
    range-extraction) and from PR `extcodesize_at_header_state_root`
    (which returns just the length). EXTCODECOPY is the only
    opcode that actually emits code bytes into EVM memory.

    Composes K201 `header_extract_state_root` + K28
    `account_at_address` + code-specific K19 `witness_codes_lookup_by_hash` + an
    inline byte-by-byte zero-padded copy loop.

    Calling convention (8 args, fits in a0..a7):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : code_offset (u64)
      a4 (input)  : length (u64; must be <= 256)
      a5 (input)  : output buffer ptr (`length` bytes)
      a6 (input)  : witness.state ptr
      a7 (input)  : witness.state len
      (precondition: caller pre-set `eccp_codes_ptr` and
       `eccp_codes_len` in .data scratch.)
      ra (input)  : return

      a0 (output) :
        0 = success (output filled, zero-padded as needed)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        5 = code_hash != EMPTY but not in witness.codes
            (witness integrity violation)
        6 = length > 256 (probe cap; not a spec issue)

      (Code 1 "account not in trie" is intentionally absent:
      missing accounts map to `status=0, output=all zeros` per
      the EXTCODECOPY spec.)
-/
def extcodecopyAtHeaderStateRootFunction : String :=
  "extcodecopy_at_header_state_root:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # code_offset\n" ++
  "  mv s4, a4                  # length\n" ++
  "  mv s5, a5                  # output buffer ptr\n" ++
  "  mv s6, a6                  # witness.state ptr\n" ++
  "  mv s7, a7                  # witness.state len\n" ++
  "  # Reject length > 256.\n" ++
  "  li t0, 256\n" ++
  "  bgtu s4, t0, .Lecc_too_long\n" ++
  "  # Pre-zero output[0..length] byte-by-byte (length <= 256).\n" ++
  "  mv t0, s5\n" ++
  "  mv t1, s4\n" ++
  ".Lecc_zero_loop:\n" ++
  "  beqz t1, .Lecc_zero_done\n" ++
  "  sb zero, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lecc_zero_loop\n" ++
  ".Lecc_zero_done:\n" ++
  "  # Step 1: header.state_root -> ecc_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, ecc_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lecc_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lecc_ret\n" ++
  ".Lecc_step2:\n" ++
  "  # Step 2: account_at_address -> ecc_acct_struct.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, ecc_state_root\n" ++
  "  mv a3, s6\n" ++
  "  mv a4, s7\n" ++
  "  la s8, ecc_acct_struct\n" ++
  "  mv a5, s8\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lecc_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lecc_success_zero  # 1 -> output is zeros\n" ++
  "  j .Lecc_ret                     # 2/3 propagate\n" ++
  ".Lecc_success_zero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lecc_ret\n" ++
  ".Lecc_step3:\n" ++
  "  # Check code_hash == EMPTY_CODE_HASH.\n" ++
  "  la t0, ecc_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(s8); bne t1, t2, .Lecc_step4\n" ++
  "  ld t1,  8(t0); ld t2, 80(s8); bne t1, t2, .Lecc_step4\n" ++
  "  ld t1, 16(t0); ld t2, 88(s8); bne t1, t2, .Lecc_step4\n" ++
  "  ld t1, 24(t0); ld t2, 96(s8); bne t1, t2, .Lecc_step4\n" ++
  "  # Empty code; output stays zero, return 0.\n" ++
  "  li a0, 0\n" ++
  "  j .Lecc_ret\n" ++
  ".Lecc_step4:\n" ++
  "  # Step 4: lookup code in witness.codes.\n" ++
  "  la t0, eccp_codes_ptr; ld a0, 0(t0)\n" ++
  "  la t0, eccp_codes_len; ld a1, 0(t0)\n" ++
  "  addi a2, s8, 72            # &acct.code_hash\n" ++
  "  la a3, ecc_match_offset\n" ++
  "  la a4, ecc_match_len\n" ++
  "  jal ra, witness_codes_lookup_by_hash\n" ++
  "  beqz a0, .Lecc_step5\n" ++
  "  li a0, 5                   # integrity violation\n" ++
  "  j .Lecc_ret\n" ++
  ".Lecc_step5:\n" ++
  "  # s9 = code_ptr = codes_ptr + match_offset\n" ++
  "  la t0, eccp_codes_ptr; ld t1, 0(t0)\n" ++
  "  la t0, ecc_match_offset; ld t2, 0(t0)\n" ++
  "  add s9, t1, t2\n" ++
  "  # code_len in t3\n" ++
  "  la t0, ecc_match_len; ld t3, 0(t0)\n" ++
  "  # Byte-by-byte zero-padded copy.\n" ++
  "  # for i in 0..length: output[i] = code[code_offset+i] if code_offset+i < code_len else 0\n" ++
  "  li t0, 0                   # i\n" ++
  ".Lecc_copy_loop:\n" ++
  "  beq t0, s4, .Lecc_copy_done\n" ++
  "  add t1, s3, t0             # src_idx = code_offset + i\n" ++
  "  bgeu t1, t3, .Lecc_pad     # past code end -> already zero\n" ++
  "  add t2, s9, t1             # code_ptr + src_idx\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  add t5, s5, t0\n" ++
  "  sb t4, 0(t5)\n" ++
  ".Lecc_pad:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lecc_copy_loop\n" ++
  ".Lecc_copy_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lecc_ret\n" ++
  ".Lecc_too_long:\n" ++
  "  li a0, 6\n" ++
  ".Lecc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_extcodecopy_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_codes_len (u64 LE)
      bytes 32..40 : code_offset (u64 LE)
      bytes 40..48 : length (u64 LE; must be <= 256)
      bytes 48..68 : address (20 bytes)
      bytes 68..68+H              : header_rlp
      bytes 68+H..68+H+WS         : witness.state
      bytes 68+H+WS..             : witness.codes
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4 / 5 / 6)
      bytes  8..16 : effective length (= length on success; 0 otherwise)
      bytes 16..(16+length) : copied code bytes, zero-padded -/
def ziskExtcodecopyAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1,  8(s0)               # header_rlp_len\n" ++
  "  ld s2, 16(s0)               # witness_state_len\n" ++
  "  ld s3, 24(s0)               # witness_codes_len\n" ++
  "  ld s4, 32(s0)               # code_offset\n" ++
  "  ld s5, 40(s0)               # length\n" ++
  "  addi s6, s0, 68             # header_rlp ptr\n" ++
  "  add s7, s6, s1              # witness.state ptr\n" ++
  "  add s8, s7, s2              # witness.codes ptr\n" ++
  "  mv a0, s8; mv a1, s3; jal ra, witness_codes_index_build\n" ++
  "  mv a0, s6                   # header_rlp ptr\n" ++
  "  mv a1, s1                   # header_rlp_len\n" ++
  "  addi a2, s0, 48             # address ptr\n" ++
  "  mv a3, s4                   # code_offset\n" ++
  "  mv a4, s5                   # length\n" ++
  "  li a5, 0xa0010010           # output buffer at OUTPUT + 16\n" ++
  "  mv a6, s7                   # witness.state ptr\n" ++
  "  mv a7, s2                   # witness.state len\n" ++
  "  la t0, eccp_codes_ptr; sd s8, 0(t0)\n" ++
  "  la t0, eccp_codes_len; sd s3, 0(t0)\n" ++
  "  jal ra, extcodecopy_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  # Write effective length = length on success, else 0.\n" ++
  "  bnez a0, .Lecc_no_len\n" ++
  "  sd s5, 8(t0)                # success: use saved length\n" ++
  "  j .Lecc_pdone\n" ++
  ".Lecc_no_len:\n" ++
  "  sd zero, 8(t0)\n" ++
  "  j .Lecc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashFunction ++ "\n" ++
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
  extcodecopyAtHeaderStateRootFunction ++ "\n" ++
  ".Lecc_pdone:"

def ziskExtcodecopyAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  "wclh_scratch_hash:\n" ++
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
  ".balign 32\n" ++
  "ecc_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecc_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "eccp_codes_ptr:\n" ++
  "  .zero 8\n" ++
  "eccp_codes_len:\n" ++
  "  .zero 8\n" ++
  "ecc_match_offset:\n" ++
  "  .zero 8\n" ++
  "ecc_match_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecc_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskExtcodecopyAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtcodecopyAtHeaderStateRootPrologue
  dataAsm     := ziskExtcodecopyAtHeaderStateRootDataSection
}

end EvmAsm.Codegen
