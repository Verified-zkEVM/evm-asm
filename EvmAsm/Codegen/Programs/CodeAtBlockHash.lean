/-
  EvmAsm.Codegen.Programs.CodeAtBlockHash

  Historical bytecode extractor keyed by block_hash.
  Pipeline: find header by block_hash, walk to account,
  extract code_hash, then look up the code in witness.codes
  by that hash. Returns (offset, length) of the bytecode
  within witness.codes.

  Composes the hash-keyed walk family (#7314/#7320/#7326/#7331)
  with a final K19 over witness.codes.

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

/-! ## code_at_block_hash_address

    Historical bytecode lookup keyed by block_hash:
      block_hash + witness.headers -- K19 -> header
      header + witness.state + addr -- K201 + K28 -> account
      account.code_hash + witness.codes -- K19 -> (offset, length)

    Returns the location of the bytecode within
    witness.codes so the caller can slice it without
    materialising the bytes here.

    For EOAs / absent accounts: code_hash = EMPTY_CODE_HASH;
    K19 over witness.codes will miss (witness.codes
    typically doesn't contain the empty string), so the
    primitive returns (offset=0, length=0) with a distinct
    status (5) indicating "empty code -- expected miss".

    Use cases:
      * EXTCODECOPY-style queries at a trusted historical
        block: caller wants the bytecode bytes; this
        primitive returns where in witness.codes they sit.
      * EXTCODESIZE-style queries: the length component
        gives the deployed code size at that historical
        block.
      * Bytecode-fingerprint audit: chain N calls across
        block hashes to track contract deployment /
        replacement.

    Argument squeeze: 8 register args + 2 scratch labels
    set by the prologue
      (cabh_codes_len, cabh_code_offset_out_ptr).
    The (offset, length) output is two u64s written to
    consecutive 8-byte locations (caller-provided ptr).

    Calling convention (8 register args + 2 scratch):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : witness.codes ptr
      a7 (input)  : (u64 length out ptr)
      cabh_codes_len           : u64 (caller-set scratch)
      cabh_code_offset_out_ptr : u64* (caller-set scratch
                                 pointing to the u64 offset
                                 output)
      ra (input)  : return

      a0 (output) :
        0 = success (offset, length valid)
        1 = block_hash not in witness.headers
        2 = matched header parse failure
        3 = state_root size unexpected
        4 = account absent (caller can interpret as empty code)
        5 = code_hash = EMPTY_CODE_HASH (EOA / no code);
            (offset, length) = (0, 0)
        6 = state-trie mpt parse error
        7 = account RLP decode failure
        8 = code_hash NOT found in witness.codes (witness
            structurally invalid -- chain-claimed code_hash
            should be discoverable here)

    Output is written via the two caller-supplied ptrs:
      cabh_code_offset_out_ptr (u64): offset into witness.codes
      a7 (u64):                       length of the bytecode
-/
def codeAtBlockHashAddressFunction : String :=
  "code_at_block_hash_address:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # witness.codes ptr\n" ++
  "  mv s7, a7                  # length out ptr\n" ++
  "  la t6, cabh_codes_len\n" ++
  "  ld s8, 0(t6)               # witness.codes len\n" ++
  "  la t6, cabh_code_offset_out_ptr\n" ++
  "  ld s9, 0(t6)               # offset out ptr\n" ++
  "  sd zero, 0(s7)\n" ++
  "  sd zero, 0(s9)\n" ++
  "  # Step 1: find header.\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s0\n" ++
  "  la a3, cabh_match_offset; la a4, cabh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lcabh_no_match\n" ++
  "  la t0, cabh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s10, s1, t1            # header start\n" ++
  "  la t0, cabh_match_length\n" ++
  "  ld s11, 0(t0)              # header len\n" ++
  "  # Step 2: extract state_root.\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, s11\n" ++
  "  la a2, cabh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lcabh_walk\n" ++
  "  addi a0, a0, 1             # K201 1->2, 2->3\n" ++
  "  j .Lcabh_ret\n" ++
  ".Lcabh_walk:\n" ++
  "  # Step 3: account_at_address into scratch struct.\n" ++
  "  mv a0, s3                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a2, cabh_state_root\n" ++
  "  mv a3, s4                  # witness.state ptr\n" ++
  "  mv a4, s5                  # witness.state len\n" ++
  "  la a5, cabh_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lcabh_check_empty\n" ++
  "  li t0, 1\n" ++
  "  bne a0, t0, .Lcabh_decode_err\n" ++
  "  # absent -> status 4\n" ++
  "  li a0, 4\n" ++
  "  j .Lcabh_ret\n" ++
  ".Lcabh_decode_err:\n" ++
  "  # K28: 2 -> 6, 3 -> 7.\n" ++
  "  addi a0, a0, 4\n" ++
  "  j .Lcabh_ret\n" ++
  ".Lcabh_check_empty:\n" ++
  "  # If code_hash field is EMPTY_CODE_HASH, status 5.\n" ++
  "  la t0, cabh_walked_struct\n" ++
  "  addi t0, t0, 72            # code_hash field\n" ++
  "  la t1, cabh_empty_code_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lcabh_lookup_code\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lcabh_lookup_code\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lcabh_lookup_code\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lcabh_lookup_code\n" ++
  "  li a0, 5\n" ++
  "  j .Lcabh_ret\n" ++
  ".Lcabh_lookup_code:\n" ++
  "  # Step 4: K19 over witness.codes with code_hash.\n" ++
  "  mv a0, s6                  # witness.codes ptr\n" ++
  "  mv a1, s8                  # witness.codes len\n" ++
  "  la t0, cabh_walked_struct\n" ++
  "  addi a2, t0, 72            # target_hash = code_hash\n" ++
  "  mv a3, s9                  # offset out\n" ++
  "  mv a4, s7                  # length out\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  beqz a0, .Lcabh_done\n" ++
  "  li a0, 8                   # code_hash not in witness.codes\n" ++
  "  j .Lcabh_ret\n" ++
  ".Lcabh_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcabh_ret\n" ++
  ".Lcabh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lcabh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_code_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_codes_len (u64 LE)
      bytes 32..64 : block_hash (32 bytes)
      bytes 64..84 : address (20 bytes)
      bytes 84..   : witness.headers ++ witness.state ++ witness.codes
    Output layout (24 bytes):
      bytes  0.. 8 : status (0..8)
      bytes  8..16 : code_offset (u64; offset into witness.codes)
      bytes 16..24 : code_length (u64) -/
def ziskCodeAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  ld t5, 24(t4)               # witness_codes_len\n" ++
  "  addi a0, t4, 32             # block_hash ptr\n" ++
  "  addi a3, t4, 64             # address ptr\n" ++
  "  addi a1, t4, 84             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  add  a6, a4, a5             # witness.codes ptr\n" ++
  "  li a7, 0xa0010010           # length out (OUTPUT + 16)\n" ++
  "  la t0, cabh_codes_len\n" ++
  "  sd t5, 0(t0)\n" ++
  "  la t0, cabh_code_offset_out_ptr\n" ++
  "  li t1, 0xa0010008\n" ++
  "  sd t1, 0(t0)\n" ++
  "  jal ra, code_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcabh_pdone\n" ++
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
  codeAtBlockHashAddressFunction ++ "\n" ++
  ".Lcabh_pdone:"

def ziskCodeAtBlockHashAddressDataSection : String :=
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
  "cabh_match_offset:\n" ++
  "  .zero 8\n" ++
  "cabh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "cabh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "cabh_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "cabh_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 8\n" ++
  "cabh_codes_len:\n" ++
  "  .zero 8\n" ++
  "cabh_code_offset_out_ptr:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
