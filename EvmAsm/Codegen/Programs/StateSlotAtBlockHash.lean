/-
  EvmAsm.Codegen.Programs.StateSlotAtBlockHash

  Block-hash-keyed e2e historical slot lookup. Sibling of
  #7296 (index-keyed) and #7307 (hash-keyed account).

  Pipeline:
    block_hash -- K19 over witness.headers -> matched header
    header -- K201 -> state_root
    state_root + address -- K28 -> account.storage_root
    storage_root + slot_idx -- K29 -> slot value

  Returns u256 BE slot value with 0 on any absent (SLOAD
  spec).

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

/-! ## state_slot_at_block_hash_address

    Hash-keyed historical SLOAD pipeline:
      witness.headers ∋ ?h with keccak(h) == block_hash
                     -- via K19 witness_lookup_by_hash
      h -- K201 header_extract_state_root -> 32 B state_root
        -- K28 account_at_address -> 104 B struct
      struct.storage_root + slot_idx_be
        -- K29 slot_at_index -> u256 BE slot value

    Distinct from siblings:
      | PR    | key       | output         |
      |-------|-----------|----------------|
      | #7283 | index     | account struct |
      | #7296 | index     | slot value     |
      | #7307 | block hash| account struct |
      | this  | block hash| slot value     |

    Argument squeeze: 8 register args + 2 scratch labels
    set by the prologue (sslbh_storage_len,
    sslbh_slot_value_out_ptr).

    Calling convention (8 register args + 2 scratch):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : slot_idx_be ptr (32 bytes)
      a5 (input)  : witness.state ptr
      a6 (input)  : witness.state len
      a7 (input)  : witness.storage ptr
      sslbh_storage_len    : u64 (caller-set scratch)
      sslbh_slot_value_out : u64* (caller-set scratch ptr
                             to a 32-byte buffer)
      ra (input)  : return

      a0 (output) :
        0 = success (slot value walked)
        1 = block_hash not in witness.headers
        2 = matched header parse failure
        3 = state_root size unexpected
        4 = account absent (slot = 0 per SLOAD)
        5 = state-trie mpt parse error
        6 = account RLP decode failure
        7 = slot absent (SLOAD = 0)
        8 = storage-trie mpt parse error
        9 = slot RLP decode failure
-/
def stateSlotAtBlockHashAddressFunction : String :=
  "state_slot_at_block_hash_address:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # slot_idx_be ptr\n" ++
  "  mv s5, a5                  # witness.state ptr\n" ++
  "  mv s6, a6                  # witness.state len\n" ++
  "  mv s7, a7                  # witness.storage ptr\n" ++
  "  la t6, sslbh_storage_len\n" ++
  "  ld s8, 0(t6)               # witness.storage len\n" ++
  "  la t6, sslbh_slot_value_out_ptr\n" ++
  "  ld s9, 0(t6)               # slot_value u256 out ptr\n" ++
  "  sd zero,  0(s9); sd zero,  8(s9); sd zero, 16(s9); sd zero, 24(s9)\n" ++
  "  # Step 1: K19 over witness.headers with block_hash.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, sslbh_match_offset\n" ++
  "  la a4, sslbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsslbh_no_match\n" ++
  "  la t0, sslbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s10, s1, t1            # matched header start\n" ++
  "  la t0, sslbh_match_length\n" ++
  "  ld s11, 0(t0)              # matched header len\n" ++
  "  # Step 2: extract state_root.\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, s11\n" ++
  "  la a2, sslbh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsslbh_walk_state\n" ++
  "  addi a0, a0, 1             # K201: 1 -> 2, 2 -> 3\n" ++
  "  j .Lsslbh_ret\n" ++
  ".Lsslbh_walk_state:\n" ++
  "  # Step 3: account_at_address.\n" ++
  "  mv a0, s3                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a2, sslbh_state_root\n" ++
  "  mv a3, s5\n" ++
  "  mv a4, s6\n" ++
  "  la a5, sslbh_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsslbh_walk_storage\n" ++
  "  addi a0, a0, 3             # K28: 1 -> 4, 2 -> 5, 3 -> 6\n" ++
  "  j .Lsslbh_ret\n" ++
  ".Lsslbh_walk_storage:\n" ++
  "  # Step 4: slot_at_index.\n" ++
  "  la t0, sslbh_walked_struct\n" ++
  "  addi t0, t0, 40            # storage_root ptr (struct + 40)\n" ++
  "  mv a0, s4                  # slot_idx_be\n" ++
  "  li a1, 32\n" ++
  "  mv a2, t0                  # storage_root ptr\n" ++
  "  mv a3, s7                  # witness.storage ptr\n" ++
  "  mv a4, s8                  # witness.storage len\n" ++
  "  mv a5, s9                  # u256 out\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lsslbh_ret\n" ++
  "  addi a0, a0, 6             # K29: 1 -> 7, 2 -> 8, 3 -> 9\n" ++
  "  j .Lsslbh_ret\n" ++
  ".Lsslbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lsslbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_state_slot_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..64 : block_hash (32 bytes)
      bytes 64..84 : address (20 bytes)
      bytes 84..116: slot_idx_be (32 bytes)
      bytes 116..  : witness.headers ++ witness.state ++ witness.storage
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..9)
      bytes  8..40 : u256 BE slot value -/
def ziskStateSlotAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a6, 16(t4)               # witness_state_len\n" ++
  "  ld t5, 24(t4)               # witness_storage_len\n" ++
  "  addi a0, t4, 32             # block_hash ptr\n" ++
  "  addi a3, t4, 64             # address ptr\n" ++
  "  addi a4, t4, 84             # slot_idx_be ptr\n" ++
  "  addi a1, t4, 116            # witness.headers ptr\n" ++
  "  add  a5, a1, a2             # witness.state ptr\n" ++
  "  add  a7, a5, a6             # witness.storage ptr\n" ++
  "  la t0, sslbh_storage_len\n" ++
  "  sd t5, 0(t0)\n" ++
  "  la t0, sslbh_slot_value_out_ptr\n" ++
  "  li t1, 0xa0010008\n" ++
  "  sd t1, 0(t0)\n" ++
  "  jal ra, state_slot_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsslbh_pdone\n" ++
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
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  stateSlotAtBlockHashAddressFunction ++ "\n" ++
  ".Lsslbh_pdone:"

def ziskStateSlotAtBlockHashAddressDataSection : String :=
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
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sslbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "sslbh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sslbh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sslbh_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "sslbh_storage_len:\n" ++
  "  .zero 8\n" ++
  "sslbh_slot_value_out_ptr:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
