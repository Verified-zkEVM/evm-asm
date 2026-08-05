/-
  EvmAsm.Codegen.Programs.Eip4788

  EIP-4788 parent-beacon-block-root storage lookup. Per the
  Cancun fork, the Beacon Chain commits each slot's parent
  beacon block root into the EVM at
  `BEACON_ROOTS_ADDRESS` (`0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02`)
  using a ring-buffer encoding:

      timestamp_idx = timestamp mod HISTORY_BUFFER_LENGTH
      root_idx      = timestamp_idx + HISTORY_BUFFER_LENGTH
      storage[timestamp_idx] = timestamp
      storage[root_idx]      = parent_beacon_block_root

  with `HISTORY_BUFFER_LENGTH = 8191`. The pair encoding lets
  callers detect a stale slot (different timestamp wrote there
  later) by comparing `storage[timestamp_idx]` against the
  requested timestamp.

  Currently hosts `eip4788_beacon_root_lookup`; future PRs may
  add the system-transaction-side primitive that WRITES the
  parent root each block.

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

/-! ## eip4788_beacon_root_lookup

    Resolve the parent beacon block root committed by the
    Beacon Chain for a block with the given timestamp, via
    the EIP-4788 system contract:

      timestamp_idx = timestamp mod 8191
      root_idx      = timestamp_idx + 8191
      Verify:  storage[timestamp_idx] == timestamp
      Return:  storage[root_idx]

    Sibling of PR `eip2935_blockhash_lookup` (the BLOCKHASH
    system contract); both are probe primitives, not on the production
    path. The two share the
    "look up via system-contract storage" pattern but EIP-4788
    adds the extra timestamp-verification step to detect stale
    slots: a writer many epochs later may have overwritten the
    same slot, so the timestamp field at the corresponding
    metadata slot tells the reader whether the data is for
    the requested timestamp.

    Spec-defining edge cases:
      * Beacon contract absent from witness -> output zeros,
        status 0.
      * `storage[timestamp_idx]` absent (slot uninitialised) ->
        output zeros, status 0 (SLOAD "unknown -> 0" rule
        + the verification check fails since `0 != timestamp`).
      * `storage[timestamp_idx]` present but != requested
        timestamp -> the slot belongs to a different
        (wrapped-around) timestamp; output zeros, status 0.
        This is the spec-defining stale-slot detection.
      * `storage[root_idx]` absent but `storage[timestamp_idx]`
        matches -> output zeros, status 0 (treated like SLOAD
        miss). Practically this shouldn't happen if the
        writer system transaction wrote both slots together.

    Composes K201 `header_extract_state_root`, K28
    `account_at_address`, and two K29 `slot_at_index` calls
    (one for the timestamp probe, one for the root). Uses
    RISC-V `remu` for the `mod 8191` since 8191 isn't a power
    of two.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : target_timestamp (u64)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : witness.storage ptr
      a6 (input)  : witness.storage len
      a7 (input)  : 32-byte output ptr (beacon root)
      ra (input)  : return

      a0 (output) :
        0 = success (output filled; may be zeros for absent
            contract / stale slot / missing slot)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure

      (Codes 1 and 5 are intentionally absent.)
-/
def eip4788BeaconRootLookupFunction : String :=
  "eip4788_beacon_root_lookup:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,   8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4,  40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8,  72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # target_timestamp\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # witness.storage ptr\n" ++
  "  mv s6, a6                  # witness.storage len\n" ++
  "  mv s7, a7                  # output ptr\n" ++
  "  # Pre-zero output -- spec default on absent / stale.\n" ++
  "  sd zero,  0(s7); sd zero,  8(s7); sd zero, 16(s7); sd zero, 24(s7)\n" ++
  "  # Step 1: header.state_root -> ebrl_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, ebrl_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lebrl_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lebrl_ret\n" ++
  ".Lebrl_step2:\n" ++
  "  # Step 2: account_at_address(BEACON_ROOTS_ADDRESS).\n" ++
  "  la a0, ebrl_beacon_addr\n" ++
  "  li a1, 20\n" ++
  "  la a2, ebrl_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s8, ebrl_acct_struct\n" ++
  "  mv a5, s8\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lebrl_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lebrl_zero_success  # beacon contract absent -> 0\n" ++
  "  j .Lebrl_ret                      # 2/3 propagate\n" ++
  ".Lebrl_zero_success:\n" ++
  "  li a0, 0\n" ++
  "  j .Lebrl_ret\n" ++
  ".Lebrl_step3:\n" ++
  "  # Compute timestamp_idx = target_timestamp mod 8191.\n" ++
  "  li t1, 8191\n" ++
  "  remu s9, s2, t1            # s9 = timestamp_idx\n" ++
  "  # Build slot 1 key: 32 BE bytes of timestamp_idx.\n" ++
  "  la s10, ebrl_slot_idx_ts\n" ++
  "  sd zero,  0(s10); sd zero,  8(s10); sd zero, 16(s10); sd zero, 24(s10)\n" ++
  "  srli t0, s9, 8             # high byte\n" ++
  "  andi t2, s9, 0xff          # low byte\n" ++
  "  sb t0, 30(s10)\n" ++
  "  sb t2, 31(s10)\n" ++
  "  # Step 4: slot_at_index(timestamp_idx_slot, &storage_root, ..., scratch).\n" ++
  "  mv a0, s10\n" ++
  "  li a1, 32\n" ++
  "  addi a2, s8, 40            # &acct.storage_root\n" ++
  "  mv a3, s5\n" ++
  "  mv a4, s6\n" ++
  "  la a5, ebrl_stored_ts_be\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lebrl_check_ts\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lebrl_zero_success  # ts slot uninit -> 0\n" ++
  "  addi a0, a0, 4             # 2 -> 6, 3 -> 7\n" ++
  "  j .Lebrl_ret\n" ++
  ".Lebrl_check_ts:\n" ++
  "  # ebrl_stored_ts_be is 32 BE bytes; compare to target_timestamp (8-byte u64).\n" ++
  "  # The stored value is small (a timestamp), so all but the last 8 bytes should be 0.\n" ++
  "  # Easier: convert the last 8 bytes of stored_ts_be to a u64 and compare against s2.\n" ++
  "  la t0, ebrl_stored_ts_be\n" ++
  "  # First check top 24 bytes are zero (would only fail with corrupted/very large stored value).\n" ++
  "  ld t1,  0(t0); bnez t1, .Lebrl_zero_success_top\n" ++
  "  ld t1,  8(t0); bnez t1, .Lebrl_zero_success_top\n" ++
  "  ld t1, 16(t0); bnez t1, .Lebrl_zero_success_top\n" ++
  "  # Convert last 8 bytes BE to u64 LE.\n" ++
  "  li t2, 0\n" ++
  "  lbu t3, 24(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  lbu t3, 25(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  lbu t3, 26(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  lbu t3, 27(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  lbu t3, 28(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  lbu t3, 29(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  lbu t3, 30(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  lbu t3, 31(t0); slli t2, t2, 8; or t2, t2, t3\n" ++
  "  bne t2, s2, .Lebrl_zero_success  # stale slot\n" ++
  "  j .Lebrl_read_root\n" ++
  ".Lebrl_zero_success_top:\n" ++
  "  # Stored timestamp is absurdly large (> u64); definitely not matching s2 (a u64).\n" ++
  "  li a0, 0\n" ++
  "  j .Lebrl_ret\n" ++
  ".Lebrl_read_root:\n" ++
  "  # Step 5: build root_idx = timestamp_idx + 8191; slot_at_index for the root.\n" ++
  "  li t0, 8191\n" ++
  "  add s11, s9, t0            # s11 = root_idx (fits in ≤15 bits)\n" ++
  "  la s10, ebrl_slot_idx_root\n" ++
  "  sd zero,  0(s10); sd zero,  8(s10); sd zero, 16(s10); sd zero, 24(s10)\n" ++
  "  srli t0, s11, 8\n" ++
  "  andi t2, s11, 0xff\n" ++
  "  sb t0, 30(s10)\n" ++
  "  sb t2, 31(s10)\n" ++
  "  mv a0, s10\n" ++
  "  li a1, 32\n" ++
  "  addi a2, s8, 40\n" ++
  "  mv a3, s5\n" ++
  "  mv a4, s6\n" ++
  "  mv a5, s7                  # output ptr (32-byte beacon root)\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lebrl_ret\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lebrl_zero_success  # root slot uninit -> 0\n" ++
  "  addi a0, a0, 4             # 2 -> 6, 3 -> 7\n" ++
  ".Lebrl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,   8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4,  40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8,  72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_eip4788_beacon_root_lookup`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len      (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..40 : target_timestamp    (u64 LE)
      bytes 40..40+H              : header_rlp
      bytes 40+H..40+H+WS         : witness.state
      bytes 40+H+WS..             : witness.storage
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : beacon root (u256 BE; zeros on absent/stale) -/
def ziskEip4788BeaconRootLookupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # witness_storage_len\n" ++
  "  ld a2, 32(t1)               # target_timestamp\n" ++
  "  addi a0, t1, 40\n" ++
  "  mv a1, t2\n" ++
  "  add a3, a0, t2\n" ++
  "  mv a4, t3\n" ++
  "  add a5, a3, t3\n" ++
  "  mv a6, t4\n" ++
  "  li a7, 0xa0010008\n" ++
  "  jal ra, eip4788_beacon_root_lookup\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lebrl_pdone\n" ++
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
  eip4788BeaconRootLookupFunction ++ "\n" ++
  ".Lebrl_pdone:"

def ziskEip4788BeaconRootLookupDataSection : String :=
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
  "ebrl_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ebrl_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "ebrl_slot_idx_ts:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ebrl_slot_idx_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "ebrl_stored_ts_be:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ebrl_beacon_addr:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02"

def ziskEip4788BeaconRootLookupProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip4788BeaconRootLookupPrologue
  dataAsm     := ziskEip4788BeaconRootLookupDataSection
}

end EvmAsm.Codegen
