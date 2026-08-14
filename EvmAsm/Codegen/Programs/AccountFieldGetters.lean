/-
  EvmAsm.Codegen.Programs.AccountFieldGetters

  Account-field getters layered over the K201 + K28 trie walk.
  Each function returns a single field of `account_at_address`'s
  104-byte struct (with a spec-defining default value for absent
  accounts) and applies the "missing-anything → zero-or-canonical"
  flattening from the EVM spec.

  Family overview (siblings of distinct return shapes):

    BALANCE        : u256;       missing -> 0
    NONCE          : u64;        missing -> 0
    storage_root   : Bytes32;    missing -> EMPTY_TRIE_ROOT
    code_hash      : Bytes32;    missing -> EMPTY_CODE_HASH

  This module hosts `code_hash_at_header_state_root`; the other
  three currently live in `EvmAsm.Codegen.Programs.EvmOpcodes`.
  Once that file approaches its hard-cap line limit, the
  remaining getters will migrate here.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## code_hash_at_header_state_root

    Witness-side getter for `account.code_hash` as a 32-byte
    hash. Sibling of `storage_root_at_header_state_root`
    (raw-field getter with a canonical default for absent
    accounts), but with the spec default being EMPTY_CODE_HASH
    instead of EMPTY_TRIE_ROOT:

      EMPTY_CODE_HASH = keccak("") = 0xc5d2460186f7233c...

    Distinct from PR-K? `extcodehash_at_header_state_root` (EIP-1052),
    which applies the EIP-161 empty-account rule (an account
    with nonce=0 AND balance=0 AND code_hash=EMPTY_CODE_HASH
    returns 0 even when present in the trie). This primitive is
    the raw field accessor: it returns whatever `account.code_hash`
    holds, with EMPTY_CODE_HASH for missing accounts (per the
    "missing account is conceptually an account with no code"
    convention).

    The spec-divergence test: an account in the trie with
    nonce=0, balance=0, code_hash=EMPTY_CODE_HASH:

      | primitive          | returns |
      |--------------------|---------|
      | code_hash (this PR)| EMPTY_CODE_HASH |
      | extcodehash (#7150)| 0 (EIP-1052) |

    Composes K201 `header_extract_state_root` + K28
    `account_at_address`, then copies the 32-byte code_hash
    field (struct + 72 .. + 104) OR writes EMPTY_CODE_HASH when
    the account is absent.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : 32-byte output ptr
      ra (input)  : return

      a0 (output) : cahsr-family status — see `MptStatusVocab.Cahsr`
        (0 success with hash or EMPTY_CODE_HASH on absent;
         2 parse / 3 decodeFail / 4 headerFail / 6 unresolved).
        Account.unresolved remaps to 6 (`STATUS_VOCAB: account→cahsr`).
        Code 1 is intentionally absent: missing accounts map to
        `status=0, output=EMPTY_CODE_HASH`.
-/
def codeHashAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .AUIPC .x5 (laHi GuestAddrs.chahsr_empty_code_hash (GuestAddrs.code_hash_at_header_state_root + 60)),
    .ADDI .x5 .x5 (laLo GuestAddrs.chahsr_empty_code_hash (GuestAddrs.code_hash_at_header_state_root + 60)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x21 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x21 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x21 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x21 .x6 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.chahsr_state_root (GuestAddrs.code_hash_at_header_state_root + 108)),
    .ADDI .x12 .x12 (laLo GuestAddrs.chahsr_state_root (GuestAddrs.code_hash_at_header_state_root + 108)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.code_hash_at_header_state_root + 116)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x21 .x0 (0 : BitVec 12),
    .SD .x21 .x0 (8 : BitVec 12),
    .SD .x21 .x0 (16 : BitVec 12),
    .SD .x21 .x0 (24 : BitVec 12),
    .LI .x10 (4 : Word),
    .JAL .x0 (jalOff (GuestAddrs.code_hash_at_header_state_root + 276) (GuestAddrs.code_hash_at_header_state_root + 144)),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.chahsr_state_root (GuestAddrs.code_hash_at_header_state_root + 156)),
    .ADDI .x12 .x12 (laLo GuestAddrs.chahsr_state_root (GuestAddrs.code_hash_at_header_state_root + 156)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x22 (laHi GuestAddrs.chahsr_acct_struct (GuestAddrs.code_hash_at_header_state_root + 172)),
    .ADDI .x22 .x22 (laLo GuestAddrs.chahsr_acct_struct (GuestAddrs.code_hash_at_header_state_root + 172)),
    .MV .x15 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.code_hash_at_header_state_root + 184)),
    .BEQ .x10 .x0 (52 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (36 : BitVec 13),
    .SD .x21 .x0 (0 : BitVec 12),
    .SD .x21 .x0 (8 : BitVec 12),
    .SD .x21 .x0 (16 : BitVec 12),
    .SD .x21 .x0 (24 : BitVec 12),
    .LI .x5 (4 : Word),
    .BNE .x10 .x5 (56 : BitVec 13),
    .LI .x10 (6 : Word),
    .JAL .x0 (48 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LD .x6 .x22 (72 : BitVec 12),
    .SD .x21 .x6 (0 : BitVec 12),
    .LD .x6 .x22 (80 : BitVec 12),
    .SD .x21 .x6 (8 : BitVec 12),
    .LD .x6 .x22 (88 : BitVec 12),
    .SD .x21 .x6 (16 : BitVec 12),
    .LD .x6 .x22 (96 : BitVec 12),
    .SD .x21 .x6 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `codeHashAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def codeHashAtHeaderStateRoot_relocs : RelocTable :=
  [ (15, .la .x5 "chahsr_empty_code_hash"),
    (27, .la .x12 "chahsr_state_root"),
    (29, .jal .x1 "header_extract_state_root"),
    (39, .la .x12 "chahsr_state_root"),
    (43, .la .x22 "chahsr_acct_struct"),
    (46, .jal .x1 "account_at_address") ]

def codeHashAtHeaderStateRootFunction : String :=
  "code_hash_at_header_state_root:\n" ++ emitProgramR codeHashAtHeaderStateRoot_prog codeHashAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `codeHashAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem codeHashAtHeaderStateRootFunction_eq_prog :
    codeHashAtHeaderStateRootFunction = "code_hash_at_header_state_root:\n" ++ emitProgramR codeHashAtHeaderStateRoot_prog codeHashAtHeaderStateRoot_relocs := rfl

#guard codeHashAtHeaderStateRootFunction.startsWith "code_hash_at_header_state_root:\n"
/-- `zisk_code_hash_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..40 : code_hash (32 bytes; EMPTY_CODE_HASH on
                     absent; zeros on error) -/
def ziskCodeHashAtHeaderStateRootPrologue : String :=
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
  "  jal ra, code_hash_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lchahsr_pdone\n" ++
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
  codeHashAtHeaderStateRootFunction ++ "\n" ++
  ".Lchahsr_pdone:"

def ziskCodeHashAtHeaderStateRootDataSection : String :=
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
  "chahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "chahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "chahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
