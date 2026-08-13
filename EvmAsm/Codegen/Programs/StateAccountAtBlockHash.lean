/-
  EvmAsm.Codegen.Programs.StateAccountAtBlockHash

  Block-hash-keyed historical account lookup. Given a
  block_hash (caller-supplied), witness.headers, address,
  and witness.state, find the witness header whose keccak
  matches the given block_hash, extract its state_root,
  then walk witness.state for the account at the address.

  Counterpart to #7283
  (`witness_headers_account_at_index_address`) which keys
  by index. This primitive keys by hash, useful when the
  caller has a block hash from an external source
  (a Pectra-style verifying root, a precompile contract
  output, an off-chain log).

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

/-! ## state_account_at_block_hash_address

    Pipeline:
      witness.headers ∋ ?h  with keccak256(h) == block_hash
                     -- via K19 witness_lookup_by_hash
      h -- header_extract_state_root -> 32 B state_root
        -- account_at_address(addr, state_root, witness.state)
        -> 104-B struct

    Distinct from #7283 (which keys by index):
      * #7283 caller must know the position of the target
        header.
      * THIS caller has a block hash but may not know
        position; primitive scans witness.headers by keccak.

    Distinct from #7222 + downstream chain:
      * #7222 verifies ONE link; doesn't search by hash.
      * THIS searches by hash and walks state in one call.

    Use cases:
      * Caller has a block_hash from an oracle / precompile
        output (e.g. EIP-2935 BLOCKHASH lookup) and wants
        account state at that block.
      * Cross-witness verification: caller has the trusted
        block_hash from header N and the witness.headers
        contains historical headers; this primitive scans
        for N's entry.
      * Hash-keyed audit: bridge claims an account state
        was correct at block_hash X; this verifies.

    Calling convention (7 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : 104-byte account struct out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (struct copied from walked leaf)
        1 = block_hash not in witness.headers
        2 = matched header parse failure
        3 = state_root size unexpected
        4 = account absent (struct zeroed)
        5 = state-trie mpt parse error
        6 = account RLP decode failure
-/
def stateAccountAtBlockHashAddressFunction : String :=
  "state_account_at_block_hash_address:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # struct out (104 B)\n" ++
  "  # Pre-zero the 104-byte struct.\n" ++
  "  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)\n" ++
  "  sd zero, 32(s6); sd zero, 40(s6); sd zero, 48(s6); sd zero, 56(s6)\n" ++
  "  sd zero, 64(s6); sd zero, 72(s6); sd zero, 80(s6); sd zero, 88(s6)\n" ++
  "  sd zero, 96(s6)\n" ++
  "  # Step 1: K19 over witness.headers with block_hash.\n" ++
  "  mv a0, s1                  # section ptr\n" ++
  "  mv a1, s2                  # section_len\n" ++
  "  mv a2, s0                  # target_hash\n" ++
  "  la a3, sabh_match_offset\n" ++
  "  la a4, sabh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsabh_no_match\n" ++
  "  # Step 2: extract state_root from matched header slice.\n" ++
  "  la t0, sabh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s7, s1, t1             # matched header start\n" ++
  "  la t0, sabh_match_length\n" ++
  "  ld s8, 0(t0)               # matched header len\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, sabh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsabh_walk\n" ++
  "  # K201: 1 -> 2, 2 -> 3.\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lsabh_ret\n" ++
  ".Lsabh_walk:\n" ++
  "  # Step 3: account_at_address.\n" ++
  "  mv a0, s3                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a2, sabh_state_root\n" ++
  "  mv a3, s4                  # witness.state ptr\n" ++
  "  mv a4, s5                  # witness.state len\n" ++
  "  mv a5, s6                  # struct out\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsabh_ret\n" ++
  "  # K28: 1 -> 4, 2 -> 5, 3 -> 6.\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Lsabh_ret\n" ++
  ".Lsabh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lsabh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_state_account_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..56 : block_hash (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.headers ++ witness.state
    Output layout (112 bytes):
      bytes  0.. 8 : status (0..6)
      bytes  8..112 : 104-byte account struct -/
def ziskStateAccountAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  addi a0, t4, 24             # block_hash ptr\n" ++
  "  addi a3, t4, 56             # address ptr\n" ++
  "  addi a1, t4, 76             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # struct out\n" ++
  "  jal ra, state_account_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsabh_pdone\n" ++
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
  stateAccountAtBlockHashAddressFunction ++ "\n" ++
  ".Lsabh_pdone:"

def ziskStateAccountAtBlockHashAddressDataSection : String :=
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
  "sabh_match_offset:\n" ++
  "  .zero 8\n" ++
  "sabh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sabh_state_root:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
