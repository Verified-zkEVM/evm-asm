/-
  EvmAsm.Codegen.Programs.ExtcodesizeAtBlockHash

  Hash-keyed EXTCODESIZE primitive. Mirrors the existing
  `extcodesize_at_header_state_root` (under StateCompose) but
  takes a `block_hash` as the key rather than raw header bytes.

  Pipeline:
    witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
    h -> header_extract_state_root                     [K201]
    state_root + address -> account_at_address         [K28]
    if code_hash == EMPTY_CODE_HASH:
      return 0  (spec: empty code)
    else:
      witness.codes ∋ ?c with keccak(c) == code_hash    [K19']
      return len(c)

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

/-! ## extcodesize_at_block_hash_address  (EXTCODESIZE at block_hash)

    Returns the byte length of the deployed code at `address`
    in the state trie of the block named by `block_hash`.

    Spec-defining edge cases:
      * Account not in state trie -> 0 (no code at all).
      * Account present but code_hash == EMPTY_CODE_HASH -> 0
        (deployed-empty-code case).
      * Account present with non-empty code_hash but code body
        missing from witness.codes -> structural error
        (witness integrity violation; status 5).

    Use cases:
      * EXTCODESIZE opcode replay against a historical block.
      * Light-client-driven contract-presence detection.
      * Bridge / oracle "size of deployed code at block_hash"
        query without committing to fetching the code body.

    Composes K19 (witness_lookup_by_hash, twice -- once on
    witness.headers by block_hash, once on witness.codes by
    code_hash) + K201 + K28. No new helpers.

    Calling convention (8 args; full a0..a7 register file):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : witness.codes ptr
      a7 (input)  : witness.codes len
      ra (input)  : return

      a0 (output) :
        0 = success (`ecsabh_code_len` holds the code length;
            may be 0 for missing/empty)
        1 = block_hash not in witness.headers
        2 = matched header parse / state_root size fail
        3 = state-trie mpt parse error
        4 = account_decode failure
        5 = code_hash != EMPTY but not found in witness.codes
            (witness integrity violation)

    The probe BuildUnit copies `ecsabh_code_len` to OUTPUT + 8.
-/
def extcodesizeAtBlockHashAddressFunction : String :=
  "extcodesize_at_block_hash_address:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # witness.codes ptr\n" ++
  "  mv s10, a7                 # witness.codes len\n" ++
  "  la t0, ecsabh_code_len\n" ++
  "  sd zero, 0(t0)\n" ++
  "  # Step 0: witness_lookup_by_hash on witness.headers.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, ecsabh_match_offset\n" ++
  "  la a4, ecsabh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lecsabh_no_match\n" ++
  "  la t0, ecsabh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s7, s1, t1\n" ++
  "  la t0, ecsabh_match_length\n" ++
  "  ld s8, 0(t0)\n" ++
  "  # Step 1: header_extract_state_root.\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, ecsabh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lecsabh_step2\n" ++
  "  li a0, 2\n" ++
  "  j .Lecsabh_ret\n" ++
  ".Lecsabh_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, ecsabh_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la s9, ecsabh_acct_struct\n" ++
  "  mv a5, s9\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lecsabh_check_empty\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lecsabh_success_zero\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lecsabh_ret\n" ++
  ".Lecsabh_success_zero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lecsabh_ret\n" ++
  ".Lecsabh_check_empty:\n" ++
  "  # code_hash == EMPTY_CODE_HASH ?\n" ++
  "  la t0, ecsabh_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(s9); bne t1, t2, .Lecsabh_lookup\n" ++
  "  ld t1,  8(t0); ld t2, 80(s9); bne t1, t2, .Lecsabh_lookup\n" ++
  "  ld t1, 16(t0); ld t2, 88(s9); bne t1, t2, .Lecsabh_lookup\n" ++
  "  ld t1, 24(t0); ld t2, 96(s9); bne t1, t2, .Lecsabh_lookup\n" ++
  "  # code is empty; output stays 0, return 0.\n" ++
  "  li a0, 0\n" ++
  "  j .Lecsabh_ret\n" ++
  ".Lecsabh_lookup:\n" ++
  "  # Step 3: witness_lookup_by_hash(codes, &acct.code_hash).\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s10\n" ++
  "  addi a2, s9, 72            # &acct.code_hash\n" ++
  "  la a3, ecsabh_dummy_offset\n" ++
  "  la a4, ecsabh_code_len\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  beqz a0, .Lecsabh_ret\n" ++
  "  la t0, ecsabh_code_len\n" ++
  "  sd zero, 0(t0)\n" ++
  "  li a0, 5\n" ++
  "  j .Lecsabh_ret\n" ++
  ".Lecsabh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lecsabh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_extcodesize_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_codes_len   (u64 LE)
      bytes 32..64 : block_hash (32 bytes)
      bytes 64..84 : address (20 bytes)
      bytes 84..   : witness.headers ++ witness.state ++ witness.codes
    Output layout:
      bytes  0.. 8 : status (0..5)
      bytes  8..16 : code length (u64; 0 for missing/empty) -/
def ziskExtcodesizeAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld t5, 8(t4)                # witness_headers_len\n" ++
  "  ld t6, 16(t4)               # witness_state_len\n" ++
  "  ld a7, 24(t4)               # witness_codes_len\n" ++
  "  addi a0, t4, 32             # block_hash ptr\n" ++
  "  addi a3, t4, 64             # address ptr\n" ++
  "  addi a1, t4, 84             # witness.headers ptr\n" ++
  "  mv a2, t5                   # witness.headers len\n" ++
  "  add a4, a1, t5              # witness.state ptr\n" ++
  "  mv a5, t6                   # witness.state len\n" ++
  "  add a6, a4, t6              # witness.codes ptr\n" ++
  "  jal ra, extcodesize_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, ecsabh_code_len; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Lecsabh_pdone\n" ++
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
  extcodesizeAtBlockHashAddressFunction ++ "\n" ++
  ".Lecsabh_pdone:"

def ziskExtcodesizeAtBlockHashAddressDataSection : String :=
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
  "ecsabh_match_offset:\n" ++
  "  .zero 8\n" ++
  "ecsabh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecsabh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecsabh_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "ecsabh_dummy_offset:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ecsabh_code_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecsabh_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
