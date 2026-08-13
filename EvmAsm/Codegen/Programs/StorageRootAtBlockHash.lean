/-
  EvmAsm.Codegen.Programs.StorageRootAtBlockHash

  Hash-keyed historical storage_root extractor. Given a
  block_hash, witness.headers, address, and witness.state,
  finds the witness header by hash, walks to find the
  account, and returns its storage_root field. Spec default
  EMPTY_TRIE_ROOT on miss.

  Sibling of #7233 (state_extract_storage_root_for_address,
  no header) and the hash-keyed family (#7307 returns full
  struct, #7312 returns slot value). This primitive's
  surface is minimal: just the 32-byte storage_root.

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

/-! ## storage_root_at_block_hash_address

    Pipeline:
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_state_root                     [K201]
      state_root + address -> account                    [K28]
      struct.storage_root (offset +40) -> 32-byte output

    On absent: write EMPTY_TRIE_ROOT to output buffer
    (spec default = EOA empty-storage), status 4.

    Use case: light-client storage walk chained from a
    historical block:
      storage_root = storage_root_at_block_hash_address(...)
      v = storage_slot_inclusion_proof_verify(storage_root,
                                              slot, value,
                                              witness.storage)
    The storage_root is anchored to the trusted block_hash
    via the witness.headers + witness.state path.

    Distinct from neighbours:
      | PR    | key       | output            |
      |-------|-----------|-------------------|
      | #7233 | state_root| storage_root      |
      | #7307 | block hash| account struct    |
      | #7312 | block hash| slot value        |
      | this  | block hash| storage_root only |

    Calling convention (7 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : address ptr (20 bytes)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : 32-byte storage_root out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (walked storage_root written)
        1 = block_hash not in witness.headers
        2 = matched header parse failure
        3 = state_root size unexpected
        4 = account absent (EMPTY_TRIE_ROOT written)
        5 = state-trie mpt parse error
        6 = account RLP decode failure
-/
def storageRootAtBlockHashAddressFunction : String :=
  "storage_root_at_block_hash_address:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # address ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # storage_root out (32 B)\n" ++
  "  sd zero,  0(s6); sd zero,  8(s6); sd zero, 16(s6); sd zero, 24(s6)\n" ++
  "  # Step 1: find header by hash.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, srbh_match_offset\n" ++
  "  la a4, srbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsrbh_no_match\n" ++
  "  la t0, srbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s7, s1, t1             # header start\n" ++
  "  la t0, srbh_match_length\n" ++
  "  ld s8, 0(t0)               # header len\n" ++
  "  # Step 2: extract state_root.\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, srbh_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsrbh_walk\n" ++
  "  addi a0, a0, 1             # K201: 1 -> 2, 2 -> 3\n" ++
  "  j .Lsrbh_ret\n" ++
  ".Lsrbh_walk:\n" ++
  "  # Step 3: account_at_address into scratch struct.\n" ++
  "  mv a0, s3                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a2, srbh_state_root\n" ++
  "  mv a3, s4                  # witness.state ptr\n" ++
  "  mv a4, s5                  # witness.state len\n" ++
  "  la a5, srbh_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsrbh_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsrbh_absent\n" ++
  "  addi a0, a0, 3             # K28: 2 -> 5, 3 -> 6\n" ++
  "  j .Lsrbh_ret\n" ++
  ".Lsrbh_present:\n" ++
  "  # Copy storage_root from walked struct (+40) to caller's buffer.\n" ++
  "  la t0, srbh_walked_struct\n" ++
  "  ld t2, 40(t0); sd t2,  0(s6)\n" ++
  "  ld t2, 48(t0); sd t2,  8(s6)\n" ++
  "  ld t2, 56(t0); sd t2, 16(s6)\n" ++
  "  ld t2, 64(t0); sd t2, 24(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lsrbh_ret\n" ++
  ".Lsrbh_absent:\n" ++
  "  # Write EMPTY_TRIE_ROOT spec default.\n" ++
  "  la t1, srbh_empty_trie_root\n" ++
  "  ld t2,  0(t1); sd t2,  0(s6)\n" ++
  "  ld t2,  8(t1); sd t2,  8(s6)\n" ++
  "  ld t2, 16(t1); sd t2, 16(s6)\n" ++
  "  ld t2, 24(t1); sd t2, 24(s6)\n" ++
  "  li a0, 4\n" ++
  "  j .Lsrbh_ret\n" ++
  ".Lsrbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lsrbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_storage_root_at_block_hash_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..56 : block_hash (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.headers ++ witness.state
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..6)
      bytes  8..40 : storage_root (32 B) -/
def ziskStorageRootAtBlockHashAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a5, 16(t4)               # witness_state_len\n" ++
  "  addi a0, t4, 24             # block_hash ptr\n" ++
  "  addi a3, t4, 56             # address ptr\n" ++
  "  addi a1, t4, 76             # witness.headers ptr\n" ++
  "  add  a4, a1, a2             # witness.state ptr\n" ++
  "  li a6, 0xa0010008           # storage_root out (32 B)\n" ++
  "  jal ra, storage_root_at_block_hash_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrbh_pdone\n" ++
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
  storageRootAtBlockHashAddressFunction ++ "\n" ++
  ".Lsrbh_pdone:"

def ziskStorageRootAtBlockHashAddressDataSection : String :=
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
  ".balign 8\n" ++
  "srbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "srbh_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "srbh_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "srbh_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "srbh_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"


end EvmAsm.Codegen
