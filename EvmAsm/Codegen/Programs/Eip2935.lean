/-
  EvmAsm.Codegen.Programs.Eip2935

  EIP-2935 BLOCKHASH-via-storage primitives. Per the Amsterdam
  fork, recent block hashes are stored at
  `HISTORY_STORAGE_ADDRESS` (`0x0000F90827F1C53a10cb7A02335B175320002935`)
  under the slot `block_number % HISTORY_SERVE_WINDOW`
  (HISTORY_SERVE_WINDOW = 8191). A BLOCKHASH-via-storage path exists here
  as a probe primitive (`eip2935_blockhash_lookup`, registered for probes
  only, not on the production path). The production BLOCKHASH handler does
  not consult this contract's storage: it answers from the witness-header
  block-hash table built by `stage_blockhash_m29` (`evm_block_hashes`).

  Currently hosts `eip2935_blockhash_lookup`; future PRs may add
  the system-transaction-side primitive that WRITES to the
  history contract at each block start.

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

/-! ## eip2935_blockhash_lookup

    Resolve `BLOCKHASH(target_block_number)` in the Amsterdam
    fork via the EIP-2935 history contract:
      * account = `state[HISTORY_STORAGE_ADDRESS]`
      * slot    = `target_block_number mod 8191`  (HISTORY_SERVE_WINDOW)
      * return  = `account.storage[slot]`         (as a 32-byte hash)

    `HISTORY_STORAGE_ADDRESS` is the constant
    `0x0000F90827F1C53a10cb7A02335B175320002935` baked into
    the .data section.

    Spec-defining edge cases:
      * If the history contract doesn't exist in the witness
        (e.g., the chain is at the genesis block and the contract
        hasn't been deployed yet): return 0.
      * If `target_block_number mod 8191` is not present in the
        history contract's storage trie (e.g., the chain hasn't
        run far enough to fill this slot): return 0. This matches
        the SLOAD-style "uninitialised slot is 0" rule.

    Composes K201 `header_extract_state_root`, K28
    `account_at_address`, and K29 `slot_at_index`. The
    target-to-slot conversion is a single `remu t, target, 8191`
    followed by a 30-byte zero pad and 2-byte BE write. (8191 is
    not a power of two, so this is a true `mod`, not a bit mask.)

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : target_block_number (u64)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : witness.storage ptr
      a6 (input)  : witness.storage len
      a7 (input)  : 32-byte output ptr (block hash)
      ra (input)  : return

      a0 (output) :
        0 = success (output filled per EIP-2935 semantic;
            may be all zeros for missing-contract / missing-slot)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure

      (Codes 1 and 5 are intentionally absent: history-contract
       absent maps to status=0 / output=zeros; slot absent maps
       to the same per SLOAD spec.)
-/
def eip2935BlockhashLookupFunction : String :=
  "eip2935_blockhash_lookup:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # target_block_number\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # witness.storage ptr\n" ++
  "  mv s6, a6                  # witness.storage len\n" ++
  "  mv s7, a7                  # output ptr\n" ++
  "  # Pre-zero output -- spec default on absent.\n" ++
  "  sd zero,  0(s7); sd zero,  8(s7); sd zero, 16(s7); sd zero, 24(s7)\n" ++
  "  # Step 1: header.state_root -> ebhl_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, ebhl_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lebhl_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lebhl_ret\n" ++
  ".Lebhl_step2:\n" ++
  "  # Step 2: account_at_address(HISTORY_STORAGE_ADDRESS).\n" ++
  "  la a0, ebhl_history_addr\n" ++
  "  li a1, 20\n" ++
  "  la a2, ebhl_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s8, ebhl_acct_struct\n" ++
  "  mv a5, s8\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lebhl_step3\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lebhl_zero_success  # history contract absent -> 0\n" ++
  "  j .Lebhl_ret                      # 2/3 propagate\n" ++
  ".Lebhl_zero_success:\n" ++
  "  li a0, 0\n" ++
  "  j .Lebhl_ret\n" ++
  ".Lebhl_step3:\n" ++
  "  # Compute slot_idx_be = u256(target_block_number mod 8192).\n" ++
  "  # Zero 30 leading bytes, then write 2-byte BE result.\n" ++
  "  la s9, ebhl_slot_idx\n" ++
  "  sd zero,  0(s9); sd zero,  8(s9); sd zero, 16(s9); sd zero, 24(s9)\n" ++
  "  li t3, 8191\n" ++
  "  remu t0, s2, t3             # target mod 8191 (HISTORY_SERVE_WINDOW)\n" ++
  "  srli t1, t0, 8             # high byte\n" ++
  "  andi t2, t0, 0xff          # low byte (0xff fits in 12-bit immediate)\n" ++
  "  sb t1, 30(s9)\n" ++
  "  sb t2, 31(s9)\n" ++
  "  # Step 4: slot_at_index(slot_idx, 32, &storage_root, witness.storage, ..., output).\n" ++
  "  mv a0, s9                  # slot_idx ptr\n" ++
  "  li a1, 32\n" ++
  "  addi a2, s8, 40            # &acct.storage_root\n" ++
  "  mv a3, s5                  # witness.storage ptr\n" ++
  "  mv a4, s6                  # witness.storage len\n" ++
  "  mv a5, s7                  # 32-byte BE output\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lebhl_ret        # 0 -> success\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lebhl_zero_success  # slot absent -> 0 per SLOAD spec\n" ++
  "  # 2 -> 6, 3 -> 7\n" ++
  "  addi a0, a0, 4\n" ++
  "  # value buffer was zeroed by slot_at_index on failure.\n" ++
  ".Lebhl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_eip2935_blockhash_lookup`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len      (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..40 : target_block_number (u64 LE)
      bytes 40..40+H              : header_rlp
      bytes 40+H..40+H+WS         : witness.state
      bytes 40+H+WS..             : witness.storage
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4 / 6 / 7)
      bytes  8..40 : block hash (u256 BE; zeros on absent/error) -/
def ziskEip2935BlockhashLookupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # witness_storage_len\n" ++
  "  ld a2, 32(t1)               # target_block_number\n" ++
  "  addi a0, t1, 40             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3\n" ++
  "  add a5, a3, t3              # witness.storage ptr\n" ++
  "  mv a6, t4\n" ++
  "  li a7, 0xa0010008           # 32 B output\n" ++
  "  jal ra, eip2935_blockhash_lookup\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lebhl_pdone\n" ++
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
  eip2935BlockhashLookupFunction ++ "\n" ++
  ".Lebhl_pdone:"

def ziskEip2935BlockhashLookupDataSection : String :=
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
  "ebhl_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ebhl_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "ebhl_slot_idx:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ebhl_history_addr:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35"

def ziskEip2935BlockhashLookupProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip2935BlockhashLookupPrologue
  dataAsm     := ziskEip2935BlockhashLookupDataSection
}

end EvmAsm.Codegen
