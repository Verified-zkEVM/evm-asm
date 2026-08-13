/-
  EvmAsm.Codegen.Programs.StateWalkExtractSlot

  End-to-end slot extractor against a trusted state_root.
  Given (state_root, address, slot_idx), walks both the
  state trie (to find the account's storage_root) and the
  storage trie (to find the slot value), and returns the
  u256 slot value with 0 default on any absent.

  Complements #7194 (`state_slot_inclusion_proof_verify`)
  which verifies against an expected value. This primitive
  returns the walked value directly.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## state_walk_extract_slot_value

    End-to-end slot value extractor. Given a trusted
    state_root, an address, and a slot_idx, walks the
    state trie to find the account's storage_root, then
    the storage trie to find the slot value.

    On any absent (account or slot) returns SLOAD-spec
    default 0 in the output buffer with the appropriate
    status code so the caller can distinguish:
      * status 0  -- both present, walked value
      * status 1  -- account absent (SLOAD = 0)
      * status 4  -- slot absent (SLOAD = 0)
      * status 2/3, 5/6 -- parse/decode failures

    Distinct from #7194:
      * #7194 takes EXPECTED slot value, returns is_match.
      * THIS returns the walked value itself.

    Distinct from #7233 + K29 chain:
      * Two-call chain extracts storage_root then walks slot;
        caller must handle the storage_root pass.
      * THIS does both walks internally; storage_root never
        exposed.

    Calling convention (8 args):
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : slot_idx_be ptr (32 bytes BE)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : witness.storage ptr
      a6 (input)  : witness.storage len
      a7 (input)  : 32-byte u256 out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (slot value walked)
        1 = account not in state trie (value = 0)
        2 = state-trie mpt walk error
        3 = account RLP decode failure
        4 = slot not in storage trie (value = 0)
        5 = storage-trie mpt walk error
        6 = slot RLP decode failure
-/
def stateWalkExtractSlotValueFunction : String :=
  "state_walk_extract_slot_value:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # slot_idx_be ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # witness.storage ptr\n" ++
  "  mv s6, a6                  # witness.storage len\n" ++
  "  mv s7, a7                  # u256 out ptr (32 B)\n" ++
  "  # Pre-zero output buffer (handles all absent-default and error cases).\n" ++
  "  sd zero,  0(s7); sd zero,  8(s7); sd zero, 16(s7); sd zero, 24(s7)\n" ++
  "  # Step 1: account_at_address(addr, state_root, witness.state).\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root ptr\n" ++
  "  mv a3, s3                  # witness.state ptr\n" ++
  "  mv a4, s4                  # witness.state len\n" ++
  "  la a5, swes_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lswes_state_ok\n" ++
  "  # status 1/2/3 propagate; output stays zero (SLOAD default for absent).\n" ++
  "  j .Lswes_ret\n" ++
  ".Lswes_state_ok:\n" ++
  "  # Storage root is at struct + 40.\n" ++
  "  la s8, swes_walked_struct\n" ++
  "  addi s8, s8, 40            # storage_root ptr (inside struct)\n" ++
  "  # Step 2: slot_at_index(slot_idx_be, storage_root, witness.storage).\n" ++
  "  mv a0, s2                  # slot_idx_be ptr\n" ++
  "  li a1, 32\n" ++
  "  mv a2, s8                  # storage_root ptr\n" ++
  "  mv a3, s5                  # witness.storage ptr\n" ++
  "  mv a4, s6                  # witness.storage len\n" ++
  "  mv a5, s7                  # u256 out (caller's buffer)\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lswes_ret\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lswes_slot_absent\n" ++
  "  # status 2/3 from slot_at_index = remap to 5/6.\n" ++
  "  addi a0, a0, 3             # 2 -> 5, 3 -> 6\n" ++
  "  j .Lswes_ret\n" ++
  ".Lswes_slot_absent:\n" ++
  "  li a0, 4\n" ++
  ".Lswes_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_state_walk_extract_slot_value`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..24 : witness_storage_len (u64 LE)
      bytes 24..56 : state_root (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..108: slot_idx_be (32 bytes BE)
      bytes 108..  : witness.state ++ witness.storage
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..6)
      bytes  8..40 : u256 slot value (32 B BE) -/
def ziskStateWalkExtractSlotValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a4, 8(t4)                # witness_state_len\n" ++
  "  ld a6, 16(t4)               # witness_storage_len\n" ++
  "  addi a0, t4, 24             # state_root ptr\n" ++
  "  addi a1, t4, 56             # address ptr\n" ++
  "  addi a2, t4, 76             # slot_idx_be ptr\n" ++
  "  addi a3, t4, 108            # witness.state ptr\n" ++
  "  add  a5, a3, a4             # witness.storage ptr\n" ++
  "  li a7, 0xa0010008           # u256 out\n" ++
  "  jal ra, state_walk_extract_slot_value\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lswes_pdone\n" ++
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
  stateWalkExtractSlotValueFunction ++ "\n" ++
  ".Lswes_pdone:"

def ziskStateWalkExtractSlotValueDataSection : String :=
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
  ".balign 32\n" ++
  "swes_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
