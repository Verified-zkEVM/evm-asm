/-
  EvmAsm.Codegen.Programs.StateExtractCodeHash

  Pure field extractor: walk the state trie to find an
  address's code_hash. Spec-default EMPTY_CODE_HASH on miss.

  Sibling of #7233 (`state_extract_storage_root_for_address`):
  same template, same shape, but the code_hash field
  (offset +72) and EMPTY_CODE_HASH default.

  Useful as the cryptographically anchored input to
  EXTCODEHASH-style queries, or as a precursor to fetching
  the contract bytecode from witness.codes via K19
  (witness_lookup_by_hash with the extracted code_hash as
  target).

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

/-! ## state_extract_code_hash_for_address

    Given (state_root, address, witness.state), walk the MPT
    and write the matching account's `code_hash` field
    (32 bytes) to the caller's output buffer.

    On absent: write EMPTY_CODE_HASH (spec default,
    keccak256(""), `c5d2460186...d85a470`) to the buffer;
    status = 1.

    Use cases:
      * EXTCODEHASH against a trusted state snapshot. Pass
        the trusted state_root and an address; receive the
        chain-anchored code_hash without materialising the
        full account struct.
      * Bytecode-fetch chain: caller wants the bytecode of
        a contract at an address.
          ch = state_extract_code_hash_for_address(...)
          K19(ch, witness.codes_section, ...)   -- returns
                                                   offset/len
        Both lookups are cryptographically tied to
        state_root.
      * "Is this address running my contract?" -- pass the
        trusted state_root; compare the returned code_hash
        against keccak256(your_bytecode).

    Distinct from #7197 (`state_code_hash_inclusion_proof_verify`):
      * #7197 takes EXPECTED code_hash, VERIFIES match.
      * THIS extracts the actual code_hash (with spec default
        on miss) and returns it.

    Distinct from #7233 (`state_extract_storage_root_for_address`):
      * #7233 returns the storage_root field (struct +40)
        with EMPTY_TRIE_ROOT default.
      * THIS returns the code_hash field (struct +72) with
        EMPTY_CODE_HASH default.

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : witness.state ptr
      a3 (input)  : witness.state len
      a4 (input)  : 32-byte code_hash out buffer ptr
      ra (input)  : return

      a0 (output) :
        0 = present (walked code_hash written)
        1 = absent (EMPTY_CODE_HASH written)
        2 = mpt_walk parse error (buffer zeroed)
        3 = account RLP decode failure (buffer zeroed)
-/
def stateExtractCodeHashForAddressFunction : String :=
  "state_extract_code_hash_for_address:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a4                  # output buffer (32 B)\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # account_at_address(addr_ptr, 20, state_root_ptr, witness_ptr, witness_len, struct_buf).\n" ++
  "  mv a4, a3                  # witness_len\n" ++
  "  mv a3, a2                  # witness_ptr\n" ++
  "  mv a2, s0                  # state_root_ptr\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  la a5, sech_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsech_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsech_absent\n" ++
  "  j .Lsech_ret\n" ++
  ".Lsech_present:\n" ++
  "  la t0, sech_walked_struct\n" ++
  "  ld t2, 72(t0); sd t2,  0(s2)\n" ++
  "  ld t2, 80(t0); sd t2,  8(s2)\n" ++
  "  ld t2, 88(t0); sd t2, 16(s2)\n" ++
  "  ld t2, 96(t0); sd t2, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lsech_ret\n" ++
  ".Lsech_absent:\n" ++
  "  la t1, sech_empty_code_hash\n" ++
  "  ld t2,  0(t1); sd t2,  0(s2)\n" ++
  "  ld t2,  8(t1); sd t2,  8(s2)\n" ++
  "  ld t2, 16(t1); sd t2, 16(s2)\n" ++
  "  ld t2, 24(t1); sd t2, 24(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lsech_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_state_extract_code_hash_for_address`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..68 : address (20 bytes)
      bytes 68..   : witness.state section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status
      bytes  8..40 : code_hash (32 B) -/
def ziskStateExtractCodeHashForAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a3, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # witness.state ptr\n" ++
  "  li a4, 0xa0010008           # code_hash out (32 B)\n" ++
  "  jal ra, state_extract_code_hash_for_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsech_pdone\n" ++
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
  stateExtractCodeHashForAddressFunction ++ "\n" ++
  ".Lsech_pdone:"

def ziskStateExtractCodeHashForAddressDataSection : String :=
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
  "sech_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "sech_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
