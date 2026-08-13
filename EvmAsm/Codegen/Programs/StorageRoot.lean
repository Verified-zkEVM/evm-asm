/-
  EvmAsm.Codegen.Programs.StorageRoot

  Storage-side recompute primitives. The storage trie counterpart
  of K33 `state_root_single_account`: given a key/value the
  account's storage trie would contain, recompute the storage
  trie root that the account record would hold in its
  `storage_root` field.

  Currently hosts `storage_root_recompute_single_slot`. Future
  PRs may add multi-slot variants once an inner-branch MPT
  builder lands.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## storage_root_recompute_single_slot

    Recompute the storage trie root for a single-slot storage
    trie. Storage-side analog of K33
    `state_root_single_account`.

    Per the spec, the storage trie maps `keccak256(slot_idx_BE)`
    (a 64-nibble path) to `rlp.encode(slot_value:U256)`. For a
    single-slot trie:

      key       = keccak256(slot_idx_BE)
      value     = rlp.encode(slot_value_BE)
      leaf      = rlp.encode([hp_encode(nibbles(key), leaf=True), value])
      storage_root = keccak256(leaf)

    The double-RLP for the value is the spec edge case driving
    this PR: a naive implementation that just writes `slot_value`
    directly as the leaf's value bytes (instead of
    `rlp.encode(slot_value)`) would produce the wrong storage
    root.

    Composes:
      * K3  `zkvm_keccak256`     -- hash slot_idx and the leaf
      * K30 `rlp_encode_uint_be` -- encode slot_value canonically
      * K157 `single_leaf_trie_root` -- assemble and hash the leaf

    Useful for unit-testing storage-trie integrity: given an
    account that should have only slot `i = v`, this primitive
    computes the storage_root the account record must hold.

    Calling convention:
      a0 (input)  : slot_idx_be ptr (32 bytes; big-endian u256)
      a1 (input)  : slot_value_be ptr (32 bytes; big-endian u256)
      a2 (input)  : 32-byte output ptr (storage root)
      ra (input)  : return
      a0 (output) : 0 always
-/
def storageRootRecomputeSingleSlotFunction : String :=
  "storage_root_recompute_single_slot:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # slot_idx_be ptr\n" ++
  "  mv s1, a1                  # slot_value_be ptr\n" ++
  "  mv s2, a2                  # storage root output ptr\n" ++
  "  # Step 1: keccak256(slot_idx) -> srss_hashed_key.\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 32\n" ++
  "  la a2, srss_hashed_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 2: rlp_encode_uint_be(slot_value, 32) -> srss_value_rlp.\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 32\n" ++
  "  la a2, srss_value_rlp\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, srss_value_rlp_len; sd a0, 0(t0)\n" ++
  "  # Step 3: single_leaf_trie_root(hashed_key, 32, value_rlp, value_rlp_len, out).\n" ++
  "  la a0, srss_hashed_key\n" ++
  "  li a1, 32\n" ++
  "  la a2, srss_value_rlp\n" ++
  "  la t0, srss_value_rlp_len; ld a3, 0(t0)\n" ++
  "  mv a4, s2\n" ++
  "  jal ra, single_leaf_trie_root\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_storage_root_recompute_single_slot`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..40 : slot_idx_be (32 bytes BE u256)
      bytes 40..72 : slot_value_be (32 bytes BE u256)
    Output layout:
      bytes  0.. 8 : status (always 0)
      bytes  8..40 : storage_root (32 bytes) -/
def ziskStorageRootRecomputeSingleSlotPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8              # slot_idx ptr\n" ++
  "  addi a1, a3, 40             # slot_value ptr\n" ++
  "  li a2, 0xa0010008           # storage root output ptr\n" ++
  "  jal ra, storage_root_recompute_single_slot\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrss_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootRecomputeSingleSlotFunction ++ "\n" ++
  ".Lsrss_pdone:"

def ziskStorageRootRecomputeSingleSlotDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "srss_hashed_key:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "srss_value_rlp:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "srss_value_rlp_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_nibbles:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "sltr_nibble_count:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_hp_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "sltr_hp_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_payload_buf:\n" ++
  "  .zero 512\n" ++
  ".balign 8\n" ++
  "sltr_field_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_cursor:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_total_payload:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_node_buf:\n" ++
  "  .zero 1024"


end EvmAsm.Codegen
