/-
  EvmAsm.Codegen.Programs.StateSlotAtBlockNumber

  Number-keyed end-to-end historical SLOAD. Given a target
  block_number, walk witness.headers to find the header
  with that number, extract state_root, walk witness.state
  to find the account's storage_root, walk witness.storage
  to find the slot value.

  Number-keyed sibling of #7296 (index) and #7312 (hash).

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

/-! ## state_slot_at_block_number_address

    Number-keyed SLOAD pipeline:
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_state_root                      [K201]
      state_root + addr -> account.storage_root           [K28]
      storage_root + slot_idx -> u256 value               [K29]

    Returns u256 BE slot value with 0 on any absent
    (SLOAD spec).

    Distinct from siblings:
      | PR    | key            | output     |
      |-------|----------------|------------|
      | #7296 | header_idx     | slot value |
      | #7312 | block_hash     | slot value |
      | this  | block_number   | slot value |

    Argument squeeze: 8 register args + 2 scratch labels
    set by the prologue:
      sasb_storage_len   - u64
      sasb_slot_val_ptr  - u64* (32-byte buffer)

    Calling convention (8 register args + 2 scratch):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : slot_idx_be ptr (32 bytes)
      a5 (input)  : witness.state ptr
      a6 (input)  : witness.state len
      a7 (input)  : witness.storage ptr
      sasb_storage_len   : u64 (scratch, set by prologue)
      sasb_slot_val_ptr  : u64* (scratch, set by prologue)
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = no header has target_block_number
        2 = K233 parse failure during scan
        3 = matched header state_root size unexpected
        4 = account absent (slot = 0 per SLOAD)
        5 = state-trie mpt parse error
        6 = account RLP decode failure
        7 = slot absent (SLOAD = 0)
        8 = storage-trie mpt parse error
        9 = slot RLP decode failure
-/
def stateSlotAtBlockNumberAddressFunction : String :=
  "state_slot_at_block_number_address:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  sd t6, 104(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # slot_idx_be ptr\n" ++
  "  mv s5, a5                  # witness.state ptr\n" ++
  "  mv s6, a6                  # witness.state len\n" ++
  "  mv s7, a7                  # witness.storage ptr\n" ++
  "  la t6, sasb_storage_len\n" ++
  "  ld s8, 0(t6)               # witness.storage len\n" ++
  "  la t6, sasb_slot_val_ptr\n" ++
  "  ld s9, 0(t6)               # slot_value u256 out ptr\n" ++
  "  sd zero,  0(s9); sd zero,  8(s9); sd zero, 16(s9); sd zero, 24(s9)\n" ++
  "  li t6, 0                   # saw_parse_fail (encoded in s11 high bit free; use sp[104] hack? simpler: use t6 register saved)\n" ++
  "  beqz s2, .Lsasb_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s10, t0, 2            # N\n" ++
  "  li s11, 0                  # i\n" ++
  ".Lsasb_loop:\n" ++
  "  beq s11, s10, .Lsasb_finish\n" ++
  "  slli t0, s11, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s1, t2             # el_i_start\n" ++
  "  addi t3, s11, 1\n" ++
  "  beq t3, s10, .Lsasb_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lsasb_have_end\n" ++
  ".Lsasb_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lsasb_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, sasb_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lsasb_parse_fail\n" ++
  "  la t0, sasb_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lsasb_hit\n" ++
  "  j .Lsasb_step\n" ++
  ".Lsasb_parse_fail:\n" ++
  "  li t6, 1\n" ++
  "  sd t6, 104(sp)             # store saw_parse_fail flag\n" ++
  ".Lsasb_step:\n" ++
  "  addi s11, s11, 1\n" ++
  "  j .Lsasb_loop\n" ++
  ".Lsasb_hit:\n" ++
  "  # Recompute header bounds for K201 (a0/a1 clobbered by K233 call).\n" ++
  "  slli t0, s11, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s1, t2             # header start\n" ++
  "  addi t3, s11, 1\n" ++
  "  beq t3, s10, .Lsasb_re_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lsasb_re_have\n" ++
  ".Lsasb_re_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lsasb_re_have:\n" ++
  "  sub a1, t4, a0             # header len\n" ++
  "  la a2, sasb_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsasb_walk_state\n" ++
  "  li a0, 3\n" ++
  "  j .Lsasb_ret\n" ++
  ".Lsasb_walk_state:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, sasb_state_root\n" ++
  "  mv a3, s5\n" ++
  "  mv a4, s6\n" ++
  "  la a5, sasb_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsasb_walk_storage\n" ++
  "  addi a0, a0, 3             # K28: 1->4, 2->5, 3->6\n" ++
  "  j .Lsasb_ret\n" ++
  ".Lsasb_walk_storage:\n" ++
  "  la t0, sasb_walked_struct\n" ++
  "  addi t0, t0, 40\n" ++
  "  mv a0, s4\n" ++
  "  li a1, 32\n" ++
  "  mv a2, t0                  # storage_root\n" ++
  "  mv a3, s7\n" ++
  "  mv a4, s8\n" ++
  "  mv a5, s9\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lsasb_ret\n" ++
  "  addi a0, a0, 6             # K29: 1->7, 2->8, 3->9\n" ++
  "  j .Lsasb_ret\n" ++
  ".Lsasb_finish:\n" ++
  "  ld t6, 104(sp)\n" ++
  "  bnez t6, .Lsasb_parse_status\n" ++
  ".Lsasb_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lsasb_ret\n" ++
  ".Lsasb_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lsasb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  ld t6, 104(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

/-- `zisk_state_slot_at_block_number_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..40 : target_block_number (u64 LE)
      bytes 40..60 : address (20 bytes)
      bytes 60..92 : slot_idx_be (32 bytes)
      bytes 92..   : witness.headers ++ witness.state ++ witness.storage
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..9)
      bytes  8..40 : u256 BE slot value -/
def ziskStateSlotAtBlockNumberAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a6, 16(t4)               # witness_state_len\n" ++
  "  ld t5, 24(t4)               # witness_storage_len\n" ++
  "  ld a0, 32(t4)               # target_block_number\n" ++
  "  addi a3, t4, 40             # address ptr\n" ++
  "  addi a4, t4, 60             # slot_idx_be ptr\n" ++
  "  addi a1, t4, 92             # witness.headers ptr\n" ++
  "  add  a5, a1, a2             # witness.state ptr\n" ++
  "  add  a7, a5, a6             # witness.storage ptr\n" ++
  "  la t0, sasb_storage_len\n" ++
  "  sd t5, 0(t0)\n" ++
  "  la t0, sasb_slot_val_ptr\n" ++
  "  li t1, 0xa0010008\n" ++
  "  sd t1, 0(t0)\n" ++
  "  jal ra, state_slot_at_block_number_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsasb_pdone\n" ++
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
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  stateSlotAtBlockNumberAddressFunction ++ "\n" ++
  ".Lsasb_pdone:"

def ziskStateSlotAtBlockNumberAddressDataSection : String :=
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
  "sasb_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sasb_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sasb_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "sasb_storage_len:\n" ++
  "  .zero 8\n" ++
  "sasb_slot_val_ptr:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
