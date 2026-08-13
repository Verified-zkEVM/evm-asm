/-
  EvmAsm.Codegen.Programs.SloadAtBlockNumber

  Number-keyed SLOAD primitive. Mirrors `sload_at_block_hash_address`
  (#7476) but takes a block_number key. Continues the
  block_number EVM-opcode family started by ExtcodesizeAtBlockNumber
  (PR 7500) and ExtcodehashAtBlockNumber (PR 7507).

  Has 9 effective inputs vs RISC-V's 8 a-regs; uses the
  established >8-input pattern (side-effect global for
  output + scratch label for one extra ptr).

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

/-! ## sload_at_block_number_address  (SLOAD at block_number)

    Returns the u256 value `SLOAD(slot)` would push when
    executed against the storage trie of `address` at the
    block with `target_block_number`.

    Per spec, returns 0 for any of:
      * block_number found but account absent
      * `account.storage_root == EMPTY_TRIE_ROOT`
      * storage slot simply not present in storage trie

    Distinct from `state_slot_at_block_number_address` (which
    surfaces absence cases as distinct statuses): this
    collapses all of them to `(status=0, value=0)` per SLOAD
    spec, so callers don't have to special-case absence.

    Block_number EVM opcode family progress:
      * extcodesize -- PR 7500
      * extcodehash -- PR 7507
      * extcodecopy -- (TODO)
      * sload       -- THIS

    Pipeline (composes K233 scan + K201 + K28 + K29; no new
    helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_state_root                      [K201]
      state_root + address -> account_at_address          [K28]
      slot_idx + acct.storage_root -> slot_at_index       [K29]

    Has 9 effective inputs vs RISC-V's 8 a-regs; uses the
    same pattern as `sload_at_block_hash_address`:
      * `sloadbn_u256` side-effect global for output (saves 1 arg)
      * `sloadbn_witness_storage_len` scratch for the 9th arg.

    Calling convention (7 args + 1 global scratch):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : slot_idx ptr (32-byte BE u256)
      a5 (input)  : witness.state ptr
      a6 (input)  : witness.state len
      a7 (input)  : witness.storage ptr
      [scratch]   : sloadbn_witness_storage_len -- caller-set.
      ra (input)  : return

      a0 (output) :
        0 = success (`sloadbn_u256` holds u256 BE; may be 0)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header state_root extraction failure
        4 = state-trie mpt parse error
        5 = account_decode failure
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure
-/
def sloadAtBlockNumberAddressFunction : String :=
  "sload_at_block_number_address:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra,   0(sp)\n" ++
  "  sd s0,   8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4,  40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8,  72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  sd tp, 104(sp); sd gp, 112(sp)\n" ++
  "  mv s0, a0                  # target block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # slot_idx ptr\n" ++
  "  mv s5, a5                  # witness.state ptr\n" ++
  "  mv s6, a6                  # witness.state len\n" ++
  "  mv s7, a7                  # witness.storage ptr\n" ++
  "  la t0, sloadbn_witness_storage_len\n" ++
  "  ld s11, 0(t0)              # witness.storage len\n" ++
  "  la t0, sloadbn_u256\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  li gp, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lsloadbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s8, t0, 2             # N\n" ++
  "  li s9, 0                   # i\n" ++
  ".Lsloadbn_loop:\n" ++
  "  beq s9, s8, .Lsloadbn_finish\n" ++
  "  slli t0, s9, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s10, s1, t2            # header start\n" ++
  "  addi t3, s9, 1\n" ++
  "  beq t3, s8, .Lsloadbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lsloadbn_have_end\n" ++
  ".Lsloadbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lsloadbn_have_end:\n" ++
  "  sub t5, t4, s10\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, sloadbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lsloadbn_parse_fail\n" ++
  "  la t0, sloadbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lsloadbn_hit\n" ++
  "  j .Lsloadbn_step\n" ++
  ".Lsloadbn_parse_fail:\n" ++
  "  li gp, 1\n" ++
  ".Lsloadbn_step:\n" ++
  "  addi s9, s9, 1\n" ++
  "  j .Lsloadbn_loop\n" ++
  ".Lsloadbn_hit:\n" ++
  "  slli t0, s9, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  addi t3, s9, 1\n" ++
  "  beq t3, s8, .Lsloadbn_re_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  j .Lsloadbn_re_have_end\n" ++
  ".Lsloadbn_re_use_end:\n" ++
  "  mv t4, s2\n" ++
  ".Lsloadbn_re_have_end:\n" ++
  "  sub t5, t4, t2\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, sloadbn_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsloadbn_step2\n" ++
  "  li a0, 3\n" ++
  "  j .Lsloadbn_ret\n" ++
  ".Lsloadbn_step2:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, sloadbn_state_root\n" ++
  "  mv a3, s5\n" ++
  "  mv a4, s6\n" ++
  "  la tp, sloadbn_acct_struct\n" ++
  "  mv a5, tp\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsloadbn_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsloadbn_missing_acct\n" ++
  "  addi a0, a0, 2             # 2->4, 3->5\n" ++
  "  j .Lsloadbn_ret\n" ++
  ".Lsloadbn_missing_acct:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsloadbn_ret\n" ++
  ".Lsloadbn_step3:\n" ++
  "  mv a0, s4\n" ++
  "  li a1, 32\n" ++
  "  addi a2, tp, 40            # &acct.storage_root\n" ++
  "  mv a3, s7                  # witness.storage ptr\n" ++
  "  mv a4, s11                 # witness.storage len\n" ++
  "  la a5, sloadbn_u256\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lsloadbn_ret\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsloadbn_missing_slot\n" ++
  "  addi a0, a0, 4             # slot_at_index 2->6, 3->7\n" ++
  "  j .Lsloadbn_ret\n" ++
  ".Lsloadbn_missing_slot:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsloadbn_ret\n" ++
  ".Lsloadbn_finish:\n" ++
  "  bnez gp, .Lsloadbn_parse_status\n" ++
  ".Lsloadbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lsloadbn_ret\n" ++
  ".Lsloadbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lsloadbn_ret:\n" ++
  "  ld ra,   0(sp)\n" ++
  "  ld s0,   8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4,  40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8,  72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  ld tp, 104(sp); ld gp, 112(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

/-- `zisk_sload_at_block_number_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..40 : target_block_number (u64 LE)
      bytes 40..72 : slot_idx (32-byte BE u256)
      bytes 72..92 : address  (20 bytes)
      bytes 92..   : witness.headers ++ witness.state ++ witness.storage
    Output layout (40 bytes):
      bytes  0.. 8 : status (0 / 1 / 2 / 3 / 4 / 5 / 6 / 7)
      bytes  8..40 : slot value (u256 BE; 0 on missing/absent) -/
def ziskSloadAtBlockNumberAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld t5,  8(t4)               # witness_headers_len\n" ++
  "  ld t6, 16(t4)               # witness_state_len\n" ++
  "  ld t3, 24(t4)               # witness_storage_len\n" ++
  "  la t0, sloadbn_witness_storage_len\n" ++
  "  sd t3, 0(t0)\n" ++
  "  ld a0, 32(t4)               # target_block_number\n" ++
  "  addi a4, t4, 40             # slot_idx ptr\n" ++
  "  addi a3, t4, 72             # address ptr\n" ++
  "  addi a1, t4, 92             # witness.headers ptr\n" ++
  "  mv a2, t5                   # witness.headers len\n" ++
  "  add a5, a1, t5              # witness.state ptr\n" ++
  "  mv a6, t6                   # witness.state len\n" ++
  "  add a7, a5, t6              # witness.storage ptr\n" ++
  "  jal ra, sload_at_block_number_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, sloadbn_u256\n" ++
  "  ld t2,  0(t1); sd t2,  8(t0)\n" ++
  "  ld t2,  8(t1); sd t2, 16(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 24(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 32(t0)\n" ++
  "  j .Lsloadbn_pdone\n" ++
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
  sloadAtBlockNumberAddressFunction ++ "\n" ++
  ".Lsloadbn_pdone:"

def ziskSloadAtBlockNumberAddressDataSection : String :=
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
  "sloadbn_witness_storage_len:\n" ++
  "  .zero 8\n" ++
  "sloadbn_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sloadbn_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sloadbn_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "sloadbn_u256:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
