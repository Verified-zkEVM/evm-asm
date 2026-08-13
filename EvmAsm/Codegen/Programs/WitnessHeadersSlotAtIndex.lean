/-
  EvmAsm.Codegen.Programs.WitnessHeadersSlotAtIndex

  End-to-end historical slot lookup. Given a witness.headers
  section, a header index i, an address, and a slot_idx,
  extract header_i.state_root, walk witness.state to find
  the account at that address, then walk witness.storage to
  find the slot value under the account's storage_root.

  Fuses #7271 (witness_headers_state_root_at_index) + K28
  account_at_address + K29 slot_at_index into one
  primitive. SLOAD-spec semantics: any absent (account or
  slot) yields slot value 0.

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

/-! ## witness_headers_slot_at_index_address

    Historical slot lookup pipeline:
      witness.headers[i] -- SSZ index lookup
        -> header_i RLP slice
        -> header_extract_state_root -> 32 B state_root_i
        -> account_at_address(addr, state_root_i,
                              witness.state) -> 104 B struct
        -> storage_root from struct + 40
        -> slot_at_index(slot_idx_be, storage_root,
                         witness.storage) -> u256 BE

    Use cases:
      * Historical SLOAD against trusted chain: "what value
        was at slot X of contract Y at block i?"
      * Bridge audit across multiple snapshot points.
      * Replay of block-i transactions reading historical
        storage to validate computed gas / output.

    Argument squeeze: 8 register args (a0..a7) carry the
    primary inputs; witness.storage_len and the u256
    slot_value output pointer are stashed into scratch
    labels (whsi_storage_len, whsi_slot_value_out_ptr) by
    the prologue.

    Calling convention (8 register args + 2 scratch):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : header_idx (u64)
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : slot_idx_be ptr (32 bytes)
      a5 (input)  : witness.state ptr
      a6 (input)  : witness.state len
      a7 (input)  : witness.storage ptr
      whsi_storage_len     : u64 (caller-set scratch)
      whsi_slot_value_out  : u64* (caller-set scratch
                             pointing to 32-byte u256 buffer)
      ra (input)  : return

      a0 (output) :
        0 = success (slot value walked)
        1 = header_idx OOB
        2 = header parse failure
        3 = state_root size unexpected
        4 = account not in state trie (slot = 0)
        5 = state-trie mpt parse error
        6 = account RLP decode failure
        7 = slot not in storage trie (slot = 0)
        8 = storage-trie mpt parse error
        9 = slot RLP decode failure
-/
def witnessHeadersSlotAtIndexAddressFunction : String :=
  "witness_headers_slot_at_index_address:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # headers ptr\n" ++
  "  mv s1, a1                  # headers section_len\n" ++
  "  mv s2, a2                  # header_idx\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # slot_idx_be ptr\n" ++
  "  mv s5, a5                  # witness.state ptr\n" ++
  "  mv s6, a6                  # witness.state len\n" ++
  "  mv s7, a7                  # witness.storage ptr\n" ++
  "  la t6, whsi_storage_len\n" ++
  "  ld s8, 0(t6)               # witness.storage len\n" ++
  "  la t6, whsi_slot_value_out_ptr\n" ++
  "  ld s9, 0(t6)               # slot_value u256 out ptr\n" ++
  "  # Pre-zero output u256.\n" ++
  "  sd zero,  0(s9); sd zero,  8(s9); sd zero, 16(s9); sd zero, 24(s9)\n" ++
  "  beqz s1, .Lwhsi_oob\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s10, t0, 2            # s10 = N\n" ++
  "  bgeu s2, s10, .Lwhsi_oob\n" ++
  "  # Compute header i bounds.\n" ++
  "  slli t0, s2, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s11, s0, t2            # header_i start\n" ++
  "  addi t3, s2, 1\n" ++
  "  beq t3, s10, .Lwhsi_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lwhsi_have_end\n" ++
  ".Lwhsi_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwhsi_have_end:\n" ++
  "  sub t5, t4, s11            # header_i len\n" ++
  "  # Step 1: extract state_root.\n" ++
  "  mv a0, s11\n" ++
  "  mv a1, t5\n" ++
  "  la a2, whsi_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lwhsi_walk_state\n" ++
  "  # K201: 1 -> 2, 2 -> 3.\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lwhsi_ret\n" ++
  ".Lwhsi_walk_state:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s3                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a2, whsi_state_root\n" ++
  "  mv a3, s5                  # witness.state ptr\n" ++
  "  mv a4, s6                  # witness.state len\n" ++
  "  la a5, whsi_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lwhsi_walk_storage\n" ++
  "  # K28: 1 -> 4 (absent, slot=0 per SLOAD), 2 -> 5, 3 -> 6.\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Lwhsi_ret\n" ++
  ".Lwhsi_walk_storage:\n" ++
  "  # Step 3: slot_at_index.\n" ++
  "  la t0, whsi_walked_struct\n" ++
  "  addi t0, t0, 40            # storage_root ptr (struct + 40)\n" ++
  "  mv a0, s4                  # slot_idx_be ptr\n" ++
  "  li a1, 32\n" ++
  "  mv a2, t0                  # storage_root ptr\n" ++
  "  mv a3, s7                  # witness.storage ptr\n" ++
  "  mv a4, s8                  # witness.storage len\n" ++
  "  mv a5, s9                  # u256 out\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lwhsi_ret\n" ++
  "  # K29: 1 -> 7 (slot absent, value=0 per SLOAD), 2 -> 8, 3 -> 9.\n" ++
  "  addi a0, a0, 6\n" ++
  "  j .Lwhsi_ret\n" ++
  ".Lwhsi_oob:\n" ++
  "  li a0, 1\n" ++
  ".Lwhsi_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_witness_headers_slot_at_index_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..40 : header_idx (u64 LE)
      bytes 40..60 : address (20 bytes)
      bytes 60..92 : slot_idx_be (32 bytes)
      bytes 92..   : witness.headers ++ witness.state ++ witness.storage
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..9)
      bytes  8..40 : u256 slot value (32 B BE) -/
def ziskWitnessHeadersSlotAtIndexAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a1, 8(t4)                # witness_headers_len\n" ++
  "  ld a6, 16(t4)               # witness_state_len\n" ++
  "  ld t5, 24(t4)               # witness_storage_len\n" ++
  "  ld a2, 32(t4)               # header_idx\n" ++
  "  addi a3, t4, 40             # address ptr\n" ++
  "  addi a4, t4, 60             # slot_idx_be ptr\n" ++
  "  addi a0, t4, 92             # witness.headers ptr\n" ++
  "  add  a5, a0, a1             # witness.state ptr\n" ++
  "  add  a7, a5, a6             # witness.storage ptr\n" ++
  "  # Stash storage len + u256 out ptr into scratch.\n" ++
  "  la t0, whsi_storage_len\n" ++
  "  sd t5, 0(t0)\n" ++
  "  la t0, whsi_slot_value_out_ptr\n" ++
  "  li t1, 0xa0010008\n" ++
  "  sd t1, 0(t0)\n" ++
  "  jal ra, witness_headers_slot_at_index_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhsi_pdone\n" ++
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
  witnessHeadersSlotAtIndexAddressFunction ++ "\n" ++
  ".Lwhsi_pdone:"

def ziskWitnessHeadersSlotAtIndexAddressDataSection : String :=
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
  ".balign 32\n" ++
  "whsi_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "whsi_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "whsi_storage_len:\n" ++
  "  .zero 8\n" ++
  "whsi_slot_value_out_ptr:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
