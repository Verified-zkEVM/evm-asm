/-
  EvmAsm.Codegen.Programs.StorageRootInWitness

  Cheapest precondition primitive for storage-trie
  verification: given a storage_root and a witness.storage
  SSZ list section, answer whether the section contains a
  node whose keccak256 equals the storage_root. Storage-side
  analog of `parent_state_root_present_in_witness_state`
  (#7200).

  No header parsing -- the caller is presumed to already
  have a trusted storage_root (e.g. from an account walk
  upstream or from a bridge oracle).

  Special edge case: a brand-new contract or EOA has
  storage_root = EMPTY_TRIE_ROOT (the canonical RLP-encoded
  empty list keccak). That root is never present in any
  witness.storage section because no node has it as
  content -- so this predicate returns `is_present = 0` and
  the caller should interpret that specifically as
  "empty storage". Distinct from "stale witness" /
  "witness mismatched against caller's storage_root".

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## storage_root_present_in_witness_storage

    Pure presence/reachability predicate over a trusted
    storage_root and a witness.storage section. Does NOT
    walk the MPT, does NOT decode any node.

    Useful for:
      * Fail-fast screening before
        `storage_slot_inclusion_proof_verify` (#7191) /
        `state_slot_inclusion_proof_verify` (#7194).
      * Distinguishing "empty storage" (root = EMPTY_TRIE_ROOT;
        not in section) from "stale witness" (root != EMPTY,
        not in section) -- both surface as is_present=0, but
        callers can compare the root to EMPTY_TRIE_ROOT once
        and branch.
      * Probing whether a caller-supplied storage_root from a
        non-walked source (e.g. another account's storage_root
        for an unrelated address) appears anywhere in the
        section.

    Calling convention (4 args):
      a0 (input)  : storage_root ptr (32 bytes)
      a1 (input)  : witness.storage ptr
      a2 (input)  : witness.storage len
      a3 (input)  : u64 out ptr (is_present)
      ra (input)  : return

      a0 (output) : status (always 0; predicate cannot fail
                    structurally -- K19 handles empty section
                    and malformed-offset cases by reporting
                    no match)
-/
def storageRootPresentInWitnessStorageFunction : String :=
  "storage_root_present_in_witness_storage:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # storage_root ptr\n" ++
  "  mv s1, a3                  # is_present out\n" ++
  "  sd zero, 0(s1)\n" ++
  "  # K19 over witness.storage with storage_root as target.\n" ++
  "  mv a0, a1                  # section ptr\n" ++
  "  mv a1, a2                  # section_len\n" ++
  "  mv a2, s0                  # target_hash = storage_root\n" ++
  "  la a3, srpw_match_offset   # discard\n" ++
  "  la a4, srpw_match_length   # discard\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsrpw_miss       # K19 returned miss -> leave is_present=0\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s1)\n" ++
  ".Lsrpw_miss:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_storage_root_present_in_witness_storage`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_storage_len (u64 LE)
      bytes 16..48 : storage_root (32 bytes)
      bytes 48..   : witness.storage section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : is_present (u64; 0 or 1) -/
def ziskStorageRootPresentInWitnessStoragePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_storage_len\n" ++
  "  addi a0, a6, 16             # storage_root ptr\n" ++
  "  addi a1, a6, 48             # witness.storage ptr\n" ++
  "  li a3, 0xa0010008           # is_present out\n" ++
  "  jal ra, storage_root_present_in_witness_storage\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrpw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  storageRootPresentInWitnessStorageFunction ++ "\n" ++
  ".Lsrpw_pdone:"

def ziskStorageRootPresentInWitnessStorageDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "srpw_match_offset:\n" ++
  "  .zero 8\n" ++
  "srpw_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
