/-
  EvmAsm.Codegen.Programs.SloadAtBlockHash

  Hash-keyed SLOAD primitive. Mirrors the existing
  `sload_at_header_state_root` (under EvmOpcodes) but takes
  a `block_hash` as the key instead of raw header bytes.

  Pipeline:
    witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
    h -> header_extract_state_root                     [K201]
    state_root + address -> account_at_address         [K28]
    slot_idx -> slot_at_index                          [K29]
    returns 0 for missing account / missing slot per SLOAD spec.

  Notably the function needs 9 inputs but RISC-V passes
  only 8 in a0..a7. We solve this by:
    * Using a side-effect global `sloadbh_u256` for the
      output (saves 1 arg).
    * Stashing `witness.storage_len` into a global scratch
      `sloadbh_witness_storage_len` before the call (saves
      another arg, so the actual call uses 7 args).

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

/-! ## sload_at_block_hash_address  (SLOAD at block_hash)

    Returns the u256 value an `SLOAD(slot)` frame would push
    when executed against the storage trie of `address` in
    the block named by `block_hash`.

    Per the spec, SLOAD returns 0 if:
      * `block_hash` is in witness.headers BUT the account
        is not present in the state trie, OR
      * `account.storage_root == EMPTY_TRIE_ROOT`, OR
      * the storage slot is simply not present in the
        storage trie (any uninitialised slot is implicitly
        zero).

    Distinct from `state_slot_at_block_hash_address`
    (#7307 family) in that absence-cases here are collapsed
    to (status=0, value=0); that primitive surfaces them as
    distinct statuses.

    Use cases:
      * SLOAD opcode replay against a historical block keyed
        by hash.
      * Light-client storage oracle, e.g. querying a known
        ERC-20 balance slot at a specific block_hash.
      * Cross-chain bridge: a counter-party claims slot
        value V at block_hash B; verify directly.

    Composes K19 (witness.headers) + K201 + K28 + K29
    (slot_at_index). No new helpers.

    Calling convention (7 args + 1 global scratch):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : slot_idx ptr (32-byte BE u256)
      a5 (input)  : witness.state ptr
      a6 (input)  : witness.state len
      a7 (input)  : witness.storage ptr
      [scratch]   : sloadbh_witness_storage_len -- must be
                    written by the caller before the call.
      ra (input)  : return

      a0 (output) :
        0 = success (`sloadbh_u256` holds the u256 BE value;
            may be 0)
        1 = block_hash not in witness.headers
        2 = matched header parse / state_root size fail
        3 = state-trie mpt parse error
        4 = account_decode failure
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure

      (Statuses 5 and "account/slot absent" are intentionally
      mapped to status=0, value=0 per SLOAD semantics.)
-/
def sloadAtBlockHashAddressFunction : String :=
  "sload_at_block_hash_address:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # slot_idx ptr\n" ++
  "  mv s5, a5                  # witness.state ptr\n" ++
  "  mv s6, a6                  # witness.state len\n" ++
  "  mv s7, a7                  # witness.storage ptr\n" ++
  "  la t0, sloadbh_witness_storage_len\n" ++
  "  ld s11, 0(t0)              # witness.storage len (from scratch)\n" ++
  "  # Pre-zero the u256 output.\n" ++
  "  la t0, sloadbh_u256\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, sloadbh_match_offset\n" ++
  "  la a4, sloadbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsloadbh_no_match\n" ++
  "  la t0, sloadbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s8, s1, t1\n" ++
  "  la t0, sloadbh_match_length\n" ++
  "  ld s9, 0(t0)\n" ++
  "  mv a0, s8\n" ++
  "  mv a1, s9\n" ++
  "  la a2, sloadbh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsloadbh_step2\n" ++
  "  li a0, 2\n" ++
  "  j .Lsloadbh_ret\n" ++
  ".Lsloadbh_step2:\n" ++
  "  # account_at_address.\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, sloadbh_state_root\n" ++
  "  mv a3, s5\n" ++
  "  mv a4, s6\n" ++
  "  la s10, sloadbh_acct_struct\n" ++
  "  mv a5, s10\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsloadbh_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsloadbh_missing_acct\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lsloadbh_ret\n" ++
  ".Lsloadbh_missing_acct:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsloadbh_ret\n" ++
  ".Lsloadbh_step3:\n" ++
  "  # slot_at_index over witness.storage with acct.storage_root.\n" ++
  "  mv a0, s4                  # slot_idx ptr\n" ++
  "  li a1, 32\n" ++
  "  addi a2, s10, 40           # &acct.storage_root\n" ++
  "  mv a3, s7                  # witness.storage ptr\n" ++
  "  mv a4, s11                 # witness.storage len\n" ++
  "  la a5, sloadbh_u256\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lsloadbh_ret\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsloadbh_missing_slot\n" ++
  "  # slot_at_index status 2 -> 6, 3 -> 7.\n" ++
  "  addi a0, a0, 4\n" ++
  "  j .Lsloadbh_ret\n" ++
  ".Lsloadbh_missing_slot:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsloadbh_ret\n" ++
  ".Lsloadbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lsloadbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_sload_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..64 : block_hash (32 bytes)
      bytes 64..96 : slot_idx   (32-byte BE u256)
      bytes 96..116: address    (20 bytes)
      bytes 116..  : witness.headers ++ witness.state ++ witness.storage
    Output layout:
      bytes  0.. 8 : status (0 / 1 / 2 / 3 / 4 / 6 / 7)
      bytes  8..40 : slot value (u256 BE; 0 on missing/absent) -/
def ziskSloadAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld t5, 8(t4)                # witness_headers_len\n" ++
  "  ld t6, 16(t4)               # witness_state_len\n" ++
  "  ld t3, 24(t4)               # witness_storage_len\n" ++
  "  # Stash witness_storage_len into scratch.\n" ++
  "  la t0, sloadbh_witness_storage_len\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi a0, t4, 32             # block_hash ptr\n" ++
  "  addi a4, t4, 64             # slot_idx ptr\n" ++
  "  addi a3, t4, 96             # address ptr\n" ++
  "  addi a1, t4, 116            # witness.headers ptr\n" ++
  "  mv a2, t5                   # witness.headers len\n" ++
  "  add a5, a1, t5              # witness.state ptr\n" ++
  "  mv a6, t6                   # witness.state len\n" ++
  "  add a7, a5, t6              # witness.storage ptr\n" ++
  "  jal ra, sload_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, sloadbh_u256\n" ++
  "  ld t2,  0(t1); sd t2,  8(t0)\n" ++
  "  ld t2,  8(t1); sd t2, 16(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 24(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 32(t0)\n" ++
  "  j .Lsloadbh_pdone\n" ++
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
  sloadAtBlockHashAddressFunction ++ "\n" ++
  ".Lsloadbh_pdone:"

def ziskSloadAtBlockHashAddressDataSection : String :=
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
  "sloadbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "sloadbh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sloadbh_witness_storage_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sloadbh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sloadbh_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "sloadbh_u256:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
