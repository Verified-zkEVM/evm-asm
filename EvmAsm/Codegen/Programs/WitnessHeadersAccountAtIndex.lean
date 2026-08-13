/-
  EvmAsm.Codegen.Programs.WitnessHeadersAccountAtIndex

  Historical-state account lookup: given a witness.headers
  section, a header index i, an address, and witness.state,
  walk the state trie under header_i.state_root and return
  the account struct.

  Fuses #7271 (witness_headers_state_root_at_index) + K28
  (account_at_address) into a single primitive so the
  caller doesn't have to round-trip the intermediate
  state_root through the host.

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

/-! ## witness_headers_account_at_index_address

    Given a witness.headers section, a header index, an
    address, and witness.state, walk the state trie under
    header_i.state_root and return the account struct.

    Pipeline:
      witness.headers[i] -- SSZ index lookup
        -> header_i RLP slice
        -> header_extract_state_root -> 32-byte state_root
        -> account_at_address(addr, state_root,
                              witness.state) -> 104-B struct

    Use cases:
      * Light-client historical-state queries: "what was
        Alice's nonce at the state of block i?"
      * Multi-block audit: chain N calls with different
        header indices to track an account's evolution
        across the witness.headers run.
      * Replay against historical state: extract balance at
        block i to validate a fee calculation that took
        place there.

    Calling convention (7 args):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : header_idx (u64)
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : 104-byte account struct out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (struct copied from walked leaf)
        1 = header_idx out of bounds
        2 = header at index could not be RLP-decoded
        3 = state_root field size unexpected
        4 = account not in state trie (struct zeroed)
        5 = state-trie mpt walk parse error
        6 = account RLP decode failure
-/
def witnessHeadersAccountAtIndexAddressFunction : String :=
  "witness_headers_account_at_index_address:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # witness.headers ptr\n" ++
  "  mv s1, a1                  # headers section_len\n" ++
  "  mv s2, a2                  # header_idx\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # account struct out (104 B)\n" ++
  "  # Pre-zero the 104-byte struct.\n" ++
  "  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)\n" ++
  "  sd zero, 32(s6); sd zero, 40(s6); sd zero, 48(s6); sd zero, 56(s6)\n" ++
  "  sd zero, 64(s6); sd zero, 72(s6); sd zero, 80(s6); sd zero, 88(s6)\n" ++
  "  sd zero, 96(s6)\n" ++
  "  beqz s1, .Lwhai_oob\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s7, t0, 2             # s7 = N\n" ++
  "  bgeu s2, s7, .Lwhai_oob\n" ++
  "  # Compute header i bounds.\n" ++
  "  slli t0, s2, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s8, s0, t2             # header_i start\n" ++
  "  addi t3, s2, 1\n" ++
  "  beq t3, s7, .Lwhai_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # header_i end\n" ++
  "  j .Lwhai_have_end\n" ++
  ".Lwhai_use_end:\n" ++
  "  add t4, s0, s1             # = section end\n" ++
  ".Lwhai_have_end:\n" ++
  "  sub t5, t4, s8             # header_i len  (preserved across calls below in s8 update)\n" ++
  "  # Step 1: extract state_root into scratch.\n" ++
  "  mv a0, s8\n" ++
  "  mv a1, t5\n" ++
  "  la a2, whai_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lwhai_walk\n" ++
  "  # K201: 1 = parse fail (remap to 2), 2 = size fail (remap to 3).\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lwhai_ret\n" ++
  ".Lwhai_walk:\n" ++
  "  # Step 2: account_at_address using the extracted state_root.\n" ++
  "  mv a0, s3                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a2, whai_state_root\n" ++
  "  mv a3, s4                  # witness.state ptr\n" ++
  "  mv a4, s5                  # witness.state len\n" ++
  "  mv a5, s6                  # struct out\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lwhai_ret        # status 0 propagates.\n" ++
  "  # K28: 1 = absent (remap to 4), 2 = mpt parse (remap to 5),\n" ++
  "  #      3 = decode (remap to 6).\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Lwhai_ret\n" ++
  ".Lwhai_oob:\n" ++
  "  li a0, 1\n" ++
  ".Lwhai_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_witness_headers_account_at_index_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : header_idx (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..   : witness.headers ++ witness.state
    Output layout (112 bytes):
      bytes  0.. 8 : status (0..6)
      bytes  8..112 : 104-byte account struct
                       nonce (8) | balance (32 BE) |
                       storage_root (32) | code_hash (32) -/
def ziskWitnessHeadersAccountAtIndexAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a1, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  ld a2, 24(t4)               # header_idx\n" ++
  "  addi a3, t4, 32             # address ptr\n" ++
  "  addi a0, t4, 52             # witness.headers ptr\n" ++
  "  add  a4, a0, a1             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # struct out (104 B)\n" ++
  "  jal ra, witness_headers_account_at_index_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhai_pdone\n" ++
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
  witnessHeadersAccountAtIndexAddressFunction ++ "\n" ++
  ".Lwhai_pdone:"

def ziskWitnessHeadersAccountAtIndexAddressDataSection : String :=
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
  ".balign 32\n" ++
  "whai_state_root:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
