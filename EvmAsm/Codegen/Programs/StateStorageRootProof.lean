/-
  EvmAsm.Codegen.Programs.StateStorageRootProof

  Light-client storage-root inclusion proof against a
  trusted state_root. Sibling of:
    * state_code_hash_inclusion_proof_verify (#7197)
    * state_account_inclusion_proof_verify (#7193)

  Where #7197 compares the code_hash field (offset +72) and
  #7193 compares the entire 104-byte struct, this primitive
  compares ONLY the 32-byte storage_root field (offset +40).
  Useful as the precondition for any subsequent storage walk
  -- caller wants to confirm "this address uses this exact
  storage_root at this state_root" before feeding the
  storage_root into a slot-inclusion-proof primitive.

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

/-! ## state_storage_root_inclusion_proof_verify

    Light-client storage-root inclusion-proof primitive:
    given a trusted `state_root`, address, expected 32-byte
    storage_root, and witness.state SSZ list section, verify
    that walking the MPT yields an account whose
    `storage_root` field matches.

    Smaller surface than #7193 (full struct): 32-byte
    compare only on field at struct offset +40.

    Used as the canonical precondition for a downstream
    storage walk: a light client wants to confirm a
    caller-supplied storage_root before feeding it into
    `storage_slot_inclusion_proof_verify` (#7191). With this
    primitive returning is_match=1, the storage_root is
    cryptographically tied back to the trusted state_root.

    Spec-defining edge case: a non-existent address has
    `storage_root = EMPTY_TRIE_ROOT` (spec default --
    canonical RLP-encoded-empty-list keccak). So an absent
    address with expected = EMPTY_TRIE_ROOT reports
    `is_match = 1` (the EOA-default storage state) AND
    `status = 1` (account not in trie). Two signals --
    callers caring about presence use status; those caring
    only about "is this exactly the storage_root I expect?"
    use is_match.

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : expected_storage_root ptr (32 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : u64 out ptr (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (walked storage_root field matches)
        1 = account not in trie (is_match = expected==EMPTY_TRIE_ROOT)
        2 = mpt_walk parse error
        3 = account RLP decode failure
-/
def stateStorageRootInclusionProofVerifyFunction : String :=
  "state_storage_root_inclusion_proof_verify:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # expected_storage_root ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # is_match out\n" ++
  "  sd zero, 0(s5)\n" ++
  "  # K28 account_at_address(addr, state_root, witness.state).\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root ptr\n" ++
  "  mv a3, s3                  # witness.state ptr\n" ++
  "  mv a4, s4                  # witness.state len\n" ++
  "  la a5, ssrip_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lssrip_compare_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lssrip_compare_absent\n" ++
  "  # status 2/3 propagate.\n" ++
  "  j .Lssrip_ret\n" ++
  ".Lssrip_compare_present:\n" ++
  "  # Walked struct: storage_root at offset +40.\n" ++
  "  la t0, ssrip_walked_struct\n" ++
  "  ld t2, 40(t0); ld t3,  0(s2); bne t2, t3, .Lssrip_no_match\n" ++
  "  ld t2, 48(t0); ld t3,  8(s2); bne t2, t3, .Lssrip_no_match\n" ++
  "  ld t2, 56(t0); ld t3, 16(s2); bne t2, t3, .Lssrip_no_match\n" ++
  "  ld t2, 64(t0); ld t3, 24(s2); bne t2, t3, .Lssrip_no_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lssrip_no_match:\n" ++
  "  li a0, 0\n" ++
  "  j .Lssrip_ret\n" ++
  ".Lssrip_compare_absent:\n" ++
  "  # Absent: spec default storage_root = EMPTY_TRIE_ROOT.\n" ++
  "  # is_match = 1 iff caller's expected == EMPTY_TRIE_ROOT.\n" ++
  "  la t1, ssrip_empty_trie_root\n" ++
  "  ld t2,  0(s2); ld t3,  0(t1); bne t2, t3, .Lssrip_absent_done\n" ++
  "  ld t2,  8(s2); ld t3,  8(t1); bne t2, t3, .Lssrip_absent_done\n" ++
  "  ld t2, 16(s2); ld t3, 16(t1); bne t2, t3, .Lssrip_absent_done\n" ++
  "  ld t2, 24(s2); ld t3, 24(t1); bne t2, t3, .Lssrip_absent_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lssrip_absent_done:\n" ++
  "  li a0, 1\n" ++
  ".Lssrip_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_state_storage_root_inclusion_proof_verify`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..68 : address (20 bytes)
      bytes 68..100: expected_storage_root (32 bytes)
      bytes 100..  : witness.state section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : is_match -/
def ziskStateStorageRootInclusionProofVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a4, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # expected_storage_root ptr\n" ++
  "  addi a3, a6, 100            # witness.state ptr\n" ++
  "  li a5, 0xa0010008           # is_match out\n" ++
  "  jal ra, state_storage_root_inclusion_proof_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lssrip_pdone\n" ++
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
  stateStorageRootInclusionProofVerifyFunction ++ "\n" ++
  ".Lssrip_pdone:"

def ziskStateStorageRootInclusionProofVerifyDataSection : String :=
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
  ".balign 32\n" ++
  "ssrip_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "ssrip_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"


end EvmAsm.Codegen
