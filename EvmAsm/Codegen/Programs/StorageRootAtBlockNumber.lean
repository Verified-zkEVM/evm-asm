/-
  EvmAsm.Codegen.Programs.StorageRootAtBlockNumber

  Number-keyed historical storage_root extractor.
  **Completes the 4-field block_number row** alongside:
    * balance     -- PR 7479
    * nonce       -- PR 7481
    * code_hash   -- PR 7486

  Extracts the raw stored `account.storage_root` field at
  offset +40 (32 B). Spec default: zero (32 zero bytes) on
  absent.

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

/-! ## storage_root_at_block_number_address

    Number-keyed historical storage_root extractor.

    Pipeline:
      witness.headers ∋ ?h with h.block.number == target  [K233 scan]
      h -> header_extract_state_root                      [K201]
      state_root + address -> account                     [K28]
      struct.storage_root (offset +40, 32 B) -> 32-byte out

    Spec default on absent: zero (32 zero bytes). Note that
    a present-but-with-empty-storage account returns
    `EMPTY_TRIE_ROOT` (0x56e8...) -- distinct from the
    32-zero-bytes absent case. Callers branching on storage
    emptiness should compare against EMPTY_TRIE_ROOT, not
    against zero.

    Completes the per-field × per-key matrix's block_number
    column:

      | field         | by_hash | by_number | by_state_root |
      |---------------|---------|-----------|---------------|
      | balance       | #7326   | (PR 7479) | (existing)    |
      | nonce         | (mer.)  | (PR 7481) | (existing)    |
      | code_hash     | #7320   | (PR 7486) | (existing)    |
      | storage_root  | #7314   | THIS      | (existing)    |

    Use cases:
      * Storage-trie freshness audit: compare
        storage_root at successive block_numbers to detect
        storage writes without enumerating slots.
      * Light-client cold-call gate: storage_root ==
        EMPTY_TRIE_ROOT  -> SLOAD always returns 0; skip
        the storage-trie walk.
      * Bridge consistency: counter-party records
        storage_root at height N; verify directly.

    Calling convention (7 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : 32-byte storage_root out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (storage_root written; 32 zero bytes if
            absent via status 4)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header state_root extraction failure
        4 = account absent in state trie (buffer zero)
        5 = state-trie mpt parse error
        6 = account RLP decode failure
-/
def storageRootAtBlockNumberAddressFunction : String :=
  "storage_root_at_block_number_address:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # target block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # storage_root out (32 B)\n" ++
  "  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)\n" ++
  "  li s9, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lsrbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s7, t0, 2             # N\n" ++
  "  li s8, 0                   # i\n" ++
  ".Lsrbn_loop:\n" ++
  "  beq s8, s7, .Lsrbn_finish\n" ++
  "  slli t0, s8, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s10, s1, t2            # header start\n" ++
  "  addi t3, s8, 1\n" ++
  "  beq t3, s7, .Lsrbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lsrbn_have_end\n" ++
  ".Lsrbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lsrbn_have_end:\n" ++
  "  sub t5, t4, s10\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, srbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lsrbn_parse_fail\n" ++
  "  la t0, srbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lsrbn_hit\n" ++
  "  j .Lsrbn_step\n" ++
  ".Lsrbn_parse_fail:\n" ++
  "  li s9, 1\n" ++
  ".Lsrbn_step:\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lsrbn_loop\n" ++
  ".Lsrbn_hit:\n" ++
  "  slli t0, s8, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  addi t3, s8, 1\n" ++
  "  beq t3, s7, .Lsrbn_re_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  j .Lsrbn_re_have_end\n" ++
  ".Lsrbn_re_use_end:\n" ++
  "  mv t4, s2\n" ++
  ".Lsrbn_re_have_end:\n" ++
  "  sub t5, t4, t2\n" ++
  "  mv a0, s10\n" ++
  "  mv a1, t5\n" ++
  "  la a2, srbn_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsrbn_walk\n" ++
  "  li a0, 3\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_walk:\n" ++
  "  mv a0, s3\n" ++
  "  li a1, 20\n" ++
  "  la a2, srbn_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la a5, srbn_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsrbn_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsrbn_absent\n" ++
  "  addi a0, a0, 3\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_present:\n" ++
  "  # Copy storage_root (offset +40, 32 B) to output.\n" ++
  "  la t0, srbn_walked_struct\n" ++
  "  ld t2, 40(t0); sd t2,  0(s6)\n" ++
  "  ld t2, 48(t0); sd t2,  8(s6)\n" ++
  "  ld t2, 56(t0); sd t2, 16(s6)\n" ++
  "  ld t2, 64(t0); sd t2, 24(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_absent:\n" ++
  "  # buffer already zero (spec default).\n" ++
  "  li a0, 4\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_finish:\n" ++
  "  bnez s9, .Lsrbn_parse_status\n" ++
  ".Lsrbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lsrbn_ret\n" ++
  ".Lsrbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lsrbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_storage_root_at_block_number_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : target_block_number (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..   : witness.headers ++ witness.state
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..6)
      bytes  8..40 : storage_root (32 B; 0 on absent) -/
def ziskStorageRootAtBlockNumberAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  ld a0, 24(t4)               # target_block_number\n" ++
  "  addi a3, t4, 32             # address ptr\n" ++
  "  addi a1, t4, 52             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # storage_root out\n" ++
  "  jal ra, storage_root_at_block_number_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrbn_pdone\n" ++
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
  headerExtractNumberFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  storageRootAtBlockNumberAddressFunction ++ "\n" ++
  ".Lsrbn_pdone:"

def ziskStorageRootAtBlockNumberAddressDataSection : String :=
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
  "srbn_number_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "srbn_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "srbn_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
