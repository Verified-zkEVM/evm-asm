/-
  EvmAsm.Codegen.Programs.StateExtractStorageRoot

  Pure field extractor: walk the state trie to find an
  address's storage_root and return it. Spec-default
  `EMPTY_TRIE_ROOT` on miss.

  Pipeline connector between trusted state_root and
  downstream storage walks: caller passes a trusted
  state_root, gets back the 32-byte storage_root that's
  cryptographically tied to that state_root.

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

/-! ## state_extract_storage_root_for_address

    Given (state_root, address, witness.state), walk the
    MPT and write the matching account's `storage_root`
    field (32 bytes) to the caller's output buffer.

    On absent: write EMPTY_TRIE_ROOT (spec default) to the
    output buffer; status = 1.

    Distinction from neighbouring primitives:

      * `state_storage_root_inclusion_proof_verify` (#7206)
        takes EXPECTED storage_root and verifies match.
      * `state_account_inclusion_proof_verify` (#7193)
        takes the entire EXPECTED struct.
      * `state_account_with_spec_default` (#7230) returns
        the entire 104-byte struct.
      * THIS primitive EXTRACTS just the 32-byte
        storage_root, with spec default on miss -- minimal
        surface for the "fetch storage_root for downstream
        walk" pattern.

    Use case:
      caller has trusted state_root, wants to query slots in
      one address's storage:
        sr = state_extract_storage_root_for_address(...)
        v  = storage_slot_inclusion_proof_verify(sr, slot,
                                                 ..., witness.storage)
      Because `sr` is freshly extracted under the trusted
      state_root, the storage walk is cryptographically
      anchored to the chain.

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : witness.state ptr
      a3 (input)  : witness.state len
      a4 (input)  : 32-byte storage_root out buffer ptr
      ra (input)  : return

      a0 (output) :
        0 = present (walked storage_root written)
        1 = absent (EMPTY_TRIE_ROOT written -- spec default)
        2 = mpt_walk parse error (buffer zeroed)
        3 = account RLP decode failure (buffer zeroed)
-/
def stateExtractStorageRootForAddressFunction : String :=
  "state_extract_storage_root_for_address:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a4                  # output buffer (32 B)\n" ++
  "  # Zero the output buffer.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # account_at_address(addr_ptr, 20, state_root_ptr, witness_ptr, witness_len, struct_buf).\n" ++
  "  mv a4, a3                  # witness_len  (move a3 to a4 first)\n" ++
  "  mv a3, a2                  # witness_ptr  (then a2 to a3)\n" ++
  "  mv a2, s0                  # state_root_ptr\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a5, sesr_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsesr_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsesr_absent\n" ++
  "  # status 2/3 propagate; output stays zero.\n" ++
  "  j .Lsesr_ret\n" ++
  ".Lsesr_present:\n" ++
  "  la t0, sesr_walked_struct\n" ++
  "  ld t2, 40(t0); sd t2,  0(s2)\n" ++
  "  ld t2, 48(t0); sd t2,  8(s2)\n" ++
  "  ld t2, 56(t0); sd t2, 16(s2)\n" ++
  "  ld t2, 64(t0); sd t2, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lsesr_ret\n" ++
  ".Lsesr_absent:\n" ++
  "  la t1, sesr_empty_trie_root\n" ++
  "  ld t2,  0(t1); sd t2,  0(s2)\n" ++
  "  ld t2,  8(t1); sd t2,  8(s2)\n" ++
  "  ld t2, 16(t1); sd t2, 16(s2)\n" ++
  "  ld t2, 24(t1); sd t2, 24(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lsesr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_state_extract_storage_root_for_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..68 : address (20 bytes)
      bytes 68..   : witness.state section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status
      bytes  8..40 : storage_root (32 bytes) -/
def ziskStateExtractStorageRootForAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a3, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # witness.state ptr\n" ++
  "  li a4, 0xa0010008           # storage_root out (32 B)\n" ++
  "  jal ra, state_extract_storage_root_for_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsesr_pdone\n" ++
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
  stateExtractStorageRootForAddressFunction ++ "\n" ++
  ".Lsesr_pdone:"

def ziskStateExtractStorageRootForAddressDataSection : String :=
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
  "sesr_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "sesr_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"


end EvmAsm.Codegen
