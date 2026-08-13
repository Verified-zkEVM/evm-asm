/-
  EvmAsm.Codegen.Programs.EvmOpcodesStorageRoot

  storage_root_at_header_state_root probe — carved out of EvmOpcodes.lean
  to stay under the file-size hard cap.
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

/-! ## storage_root_at_header_state_root

    Witness-side getter for `account.storage_root` as a 32-byte
    hash. Sibling of BALANCE / NONCE but with a DIFFERENT
    spec-defining default: missing accounts return
    `EMPTY_TRIE_ROOT` (= `keccak(rlp([])) = 0x56e81f17...`), not
    zeros.

    The EMPTY_TRIE_ROOT default is the spec edge case that drives
    this PR. From the execution-specs view, "the account doesn't
    exist" is equivalent to "the account has an empty storage
    trie" -- and the canonical empty-trie root is EMPTY_TRIE_ROOT.
    A naive getter that returned 32 zeros for missing accounts
    would diverge from this convention.

    Concretely, this primitive is what SLOAD / SSTORE need before
    descending into per-account storage:
      * If `account.storage_root == EMPTY_TRIE_ROOT`, no storage
        lookups are needed (every slot is 0).
      * Otherwise, the storage_root anchors the storage MPT walk.

    Composes K201 `header_extract_state_root` + K28
    `account_at_address`, then copies the 32-byte storage_root
    field (struct + 40 .. + 72) to the caller's output, OR
    writes EMPTY_TRIE_ROOT when the account is absent.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : 32-byte output ptr
      ra (input)  : return

      a0 (output) :
        0 = success (storage_root written; EMPTY_TRIE_ROOT
            on absent)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

      (Code 1 is intentionally absent: missing accounts map to
      `status=0, output=EMPTY_TRIE_ROOT`.)
-/
def storageRootAtHeaderStateRootFunction : String :=
  "storage_root_at_header_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # 32-byte output ptr\n" ++
  "  # Pre-fill output with EMPTY_TRIE_ROOT (spec default on absent).\n" ++
  "  la t0, srahsr_empty_trie_root\n" ++
  "  ld t1,  0(t0); sd t1,  0(s5)\n" ++
  "  ld t1,  8(t0); sd t1,  8(s5)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s5)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s5)\n" ++
  "  # Step 1: header.state_root -> srahsr_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, srahsr_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsrahsr_step2\n" ++
  "  # Pre-fill with EMPTY_TRIE_ROOT was overkill for status 4 (header parse fail).\n" ++
  "  # Zero the output to make the spec error case unambiguous.\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  li a0, 4\n" ++
  "  j .Lsrahsr_ret\n" ++
  ".Lsrahsr_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, srahsr_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s6, srahsr_acct_struct\n" ++
  "  mv a5, s6\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsrahsr_copy\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsrahsr_absent  # 1 -> output stays EMPTY_TRIE_ROOT\n" ++
  "  # 2/3 propagate. Zero the output for unambiguous error reporting.\n" ++
  "  sd zero,  0(s5); sd zero,  8(s5); sd zero, 16(s5); sd zero, 24(s5)\n" ++
  "  j .Lsrahsr_ret\n" ++
  ".Lsrahsr_absent:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsrahsr_ret\n" ++
  ".Lsrahsr_copy:\n" ++
  "  # Copy storage_root (struct + 40 .. + 72) to output.\n" ++
  "  ld t1, 40(s6); sd t1,  0(s5)\n" ++
  "  ld t1, 48(s6); sd t1,  8(s5)\n" ++
  "  ld t1, 56(s6); sd t1, 16(s5)\n" ++
  "  ld t1, 64(s6); sd t1, 24(s5)\n" ++
  "  li a0, 0\n" ++
  ".Lsrahsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_storage_root_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..40 : storage_root (32 bytes; EMPTY_TRIE_ROOT on
                     absent; zeros on error) -/
def ziskStorageRootAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a5, 0xa0010008           # 32 B output\n" ++
  "  jal ra, storage_root_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrahsr_pdone\n" ++
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
  storageRootAtHeaderStateRootFunction ++ "\n" ++
  ".Lsrahsr_pdone:"

def ziskStorageRootAtHeaderStateRootDataSection : String :=
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
  ".balign 32\n" ++
  "srahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "srahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "srahsr_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"

end EvmAsm.Codegen
