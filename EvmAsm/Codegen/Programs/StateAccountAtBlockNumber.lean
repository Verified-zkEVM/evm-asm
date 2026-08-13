/-
  EvmAsm.Codegen.Programs.StateAccountAtBlockNumber

  Number-keyed historical account walk. Given a target
  block_number, witness.headers, address, witness.state,
  find the header matching the number, extract its
  state_root, then walk witness.state for the account.

  Number-keyed sibling of:
    * #7283 witness_headers_account_at_index_address (index)
    * #7307 state_account_at_block_hash_address (hash)

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

/-! ## state_account_at_block_number_address

    Pipeline:
      witness.headers ∋ ?h with h.block.number == target  [K233 scan]
      h -> header_extract_state_root                      [K201]
      state_root + address -> account                     [K28]

    Use cases:
      * Light-client historical state at height N: "what
        was Alice's account state at block 12345?"
      * EVM replay validation: account state at the block
        a transaction was supposedly executed against.
      * Auditing: cross-reference an off-chain claim of
        balance/nonce at a known height.

    Distinct from siblings:
      | PR    | key            | output         |
      |-------|----------------|----------------|
      | #7283 | header_idx     | account struct |
      | #7307 | block_hash     | account struct |
      | this  | block_number   | account struct |

    Calling convention (7 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : 104-byte account struct out ptr
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = no header with target block_number
        2 = K233 parse failure during scan (only surfaces
            if no match found among parseable entries)
        3 = matched header state_root extraction failure
        4 = account absent in state trie (struct zeroed)
        5 = state-trie mpt parse error
        6 = account RLP decode failure
-/
def stateAccountAtBlockNumberAddressFunction : String :=
  "state_account_at_block_number_address:\n" ++
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
  "  mv s6, a6                  # account struct out (104 B)\n" ++
  "  # Pre-zero struct.\n" ++
  "  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)\n" ++
  "  sd zero, 32(s6); sd zero, 40(s6); sd zero, 48(s6); sd zero, 56(s6)\n" ++
  "  sd zero, 64(s6); sd zero, 72(s6); sd zero, 80(s6); sd zero, 88(s6)\n" ++
  "  sd zero, 96(s6)\n" ++
  "  li s9, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lsabn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s7, t0, 2             # N\n" ++
  "  li s8, 0                   # i\n" ++
  ".Lsabn_loop:\n" ++
  "  beq s8, s7, .Lsabn_finish\n" ++
  "  slli t0, s8, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s10, s1, t2            # header start\n" ++
  "  addi t3, s8, 1\n" ++
  "  beq t3, s7, .Lsabn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lsabn_have_end\n" ++
  ".Lsabn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lsabn_have_end:\n" ++
  "  sub t5, t4, s10            # header_len (clobbered later; re-derived)\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, sabn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lsabn_parse_fail\n" ++
  "  la t0, sabn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lsabn_hit\n" ++
  "  j .Lsabn_step\n" ++
  ".Lsabn_parse_fail:\n" ++
  "  li s9, 1\n" ++
  ".Lsabn_step:\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lsabn_loop\n" ++
  ".Lsabn_hit:\n" ++
  "  # Re-derive header_len for K201/K28.\n" ++
  "  # s10 = header start. Compute len from inner-offset table again.\n" ++
  "  slli t0, s8, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)              # start offset\n" ++
  "  addi t3, s8, 1\n" ++
  "  beq t3, s7, .Lsabn_re_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)              # next offset (relative)\n" ++
  "  j .Lsabn_re_have_end\n" ++
  ".Lsabn_re_use_end:\n" ++
  "  mv t4, s2                  # section_len as end-offset\n" ++
  ".Lsabn_re_have_end:\n" ++
  "  sub t5, t4, t2             # header_len\n" ++
  "  # Step 2: state_root.\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, sabn_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsabn_walk\n" ++
  "  li a0, 3\n" ++
  "  j .Lsabn_ret\n" ++
  ".Lsabn_walk:\n" ++
  "  # Step 3: account_at_address.\n" ++
  "  mv a0, s3                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a2, sabn_state_root\n" ++
  "  mv a3, s4                  # witness.state ptr\n" ++
  "  mv a4, s5                  # witness.state len\n" ++
  "  mv a5, s6                  # struct out\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsabn_ret\n" ++
  "  # K28: 1 -> 4, 2 -> 5, 3 -> 6.\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Lsabn_ret\n" ++
  ".Lsabn_finish:\n" ++
  "  bnez s9, .Lsabn_parse_status\n" ++
  ".Lsabn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lsabn_ret\n" ++
  ".Lsabn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lsabn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_state_account_at_block_number_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : target_block_number (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..   : witness.headers ++ witness.state
    Output layout (112 bytes):
      bytes  0.. 8 : status (0..6)
      bytes  8..112 : account struct -/
def ziskStateAccountAtBlockNumberAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  ld a0, 24(t4)               # target_block_number\n" ++
  "  addi a3, t4, 32             # address ptr\n" ++
  "  addi a1, t4, 52             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # struct out\n" ++
  "  jal ra, state_account_at_block_number_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsabn_pdone\n" ++
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
  stateAccountAtBlockNumberAddressFunction ++ "\n" ++
  ".Lsabn_pdone:"

def ziskStateAccountAtBlockNumberAddressDataSection : String :=
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
  "sabn_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sabn_state_root:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
