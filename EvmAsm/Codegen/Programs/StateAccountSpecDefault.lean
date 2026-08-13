/-
  EvmAsm.Codegen.Programs.StateAccountSpecDefault

  Sibling of K28 `account_at_address` that returns the
  SPEC-DEFINED empty account on miss rather than a zero
  struct. Useful for callers normalising every address to
  its canonical spec representation (every uninhabited
  address is implicitly an EOA with empty storage and code).

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

/-! ## state_account_with_spec_default

    Walk to the account at `address` under `state_root` in
    `witness.state`. On HIT: copy the walked struct to the
    caller's output buffer. On MISS: fill the output buffer
    with the spec-defined empty account:
      nonce         = 0
      balance       = 0
      storage_root  = EMPTY_TRIE_ROOT
      code_hash     = EMPTY_CODE_HASH

    Distinction from K28 `account_at_address`:
      * K28 on miss leaves the struct zeroed (every byte 0).
        This silently corrupts the storage_root (becomes 0
        not EMPTY_TRIE) and code_hash (becomes 0 not
        EMPTY_CODE_HASH).
      * THIS primitive on miss fills the SPEC-CORRECT empty
        struct, so callers using the output to feed into
        downstream MPT walks won't accidentally chase a
        zero-hash storage_root.

    Why this matters concretely: a caller doing
      walked = K28(addr, state_root, witness.state)
      sr = walked.storage_root  // may be 0 if absent
      slot_at_index(slot, sr, witness.storage)  // chases hash 0
    will silently get garbage. The proper invariant is that an
    absent address has EMPTY_TRIE storage; this primitive
    upholds that invariant in the struct output.

    Calling convention (same arg shape as K28):
      a0 (input)  : address ptr (20 bytes)
      a1 (input)  : address len (20)
      a2 (input)  : state_root ptr (32 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : output struct ptr (104 bytes)
      ra (input)  : return

      a0 (output) :
        0 = present (struct copied from walked leaf)
        1 = absent (struct filled with spec default)
        2 = mpt_walk parse error (struct zeroed)
        3 = account RLP decode failure (struct zeroed)
-/
def stateAccountWithSpecDefaultFunction : String :=
  "state_account_with_spec_default:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a5                  # output struct ptr (preserved)\n" ++
  "  jal ra, account_at_address\n" ++
  "  mv s1, a0                  # save K28 status\n" ++
  "  beqz a0, .Lsasd_done       # present -> struct already filled\n" ++
  "  li t0, 1\n" ++
  "  bne a0, t0, .Lsasd_done    # parse/decode fail -> leave zeroed\n" ++
  "  # Absent: K28 already zeroed the 104-byte struct.\n" ++
  "  # Fill storage_root (offset +40) with EMPTY_TRIE_ROOT.\n" ++
  "  la t1, sasd_empty_trie_root\n" ++
  "  ld t2,  0(t1); sd t2, 40(s0)\n" ++
  "  ld t2,  8(t1); sd t2, 48(s0)\n" ++
  "  ld t2, 16(t1); sd t2, 56(s0)\n" ++
  "  ld t2, 24(t1); sd t2, 64(s0)\n" ++
  "  # Fill code_hash (offset +72) with EMPTY_CODE_HASH.\n" ++
  "  la t1, sasd_empty_code_hash\n" ++
  "  ld t2,  0(t1); sd t2, 72(s0)\n" ++
  "  ld t2,  8(t1); sd t2, 80(s0)\n" ++
  "  ld t2, 16(t1); sd t2, 88(s0)\n" ++
  "  ld t2, 24(t1); sd t2, 96(s0)\n" ++
  ".Lsasd_done:\n" ++
  "  mv a0, s1\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_state_account_with_spec_default`: probe BuildUnit.
    Same input/output layout as zisk_account_at_address. -/
def ziskStateAccountWithSpecDefaultPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # addr_len\n" ++
  "  addi a2, a7, 24             # state_root ptr\n" ++
  "  addi a0, a7, 56             # address ptr\n" ++
  "  mv a1, t5\n" ++
  "  add a3, a0, t5              # witness ptr\n" ++
  "  mv a4, t6\n" ++
  "  li a5, 0xa0010008           # output struct (104 B)\n" ++
  "  sd zero, 0(a5); sd zero, 8(a5); sd zero, 16(a5); sd zero, 24(a5)\n" ++
  "  sd zero, 32(a5); sd zero, 40(a5); sd zero, 48(a5); sd zero, 56(a5)\n" ++
  "  sd zero, 64(a5); sd zero, 72(a5); sd zero, 80(a5); sd zero, 88(a5)\n" ++
  "  sd zero, 96(a5)\n" ++
  "  jal ra, state_account_with_spec_default\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsasd_pdone\n" ++
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
  stateAccountWithSpecDefaultFunction ++ "\n" ++
  ".Lsasd_pdone:"

def ziskStateAccountWithSpecDefaultDataSection : String :=
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
  "sasd_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "sasd_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
