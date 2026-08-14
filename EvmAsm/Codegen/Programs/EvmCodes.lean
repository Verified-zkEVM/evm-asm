/-
  EvmAsm.Codegen.Programs.EvmCodes

  EVM-opcode state-query programs carved out of `StateCompose.lean`
  to keep that file under the hard-cap line limit.  Imports
  `StateCompose` so it can reference the string-constant helpers
  defined there.
-/
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## has_code_or_nonce_at_header_state_root  (EIP-684 CREATE collision)

    Witness-side predicate for the EIP-684 CREATE2 / CREATE
    collision check: given a parent header RLP, an address, and
    an SSZ `witness.state` list section, return 1 iff the
    account at the address has `code_hash != EMPTY_CODE_HASH`,
    `nonce > 0`, or a non-empty storage root, else 0.

    The check is what `apply_body` uses before letting a CREATE
    opcode place new code at an address: per EIP-684, a CREATE
    that would land on an account with non-zero nonce,
    non-trivial code, or non-empty storage is rejected up-front,
    so pre-existing account state can't be silently overwritten.

    Distinct from the EIP-1052 EXTCODEHASH empty-account rule
    (which ALSO requires `balance == 0`): EIP-684 considers an
    account collision-relevant when its nonce, code, or storage is
    non-empty; balance-only accounts remain deployable.

    Composes K201 `header_extract_state_root`, K28
    `account_at_address`, and an inline check on 1 u64 nonce +
    4 u64 storage_root compares + 4 u64 code_hash compares.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      ra (input)  : return

      a0 (output) :
        0 = success (`hcon_predicate` holds 0 or 1)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

    The probe BuildUnit copies `hcon_predicate` to OUTPUT + 8.
    On a "not in trie" miss, the predicate is 0 (no collision)
    and the status is 0 -- account absence is a valid spec-side
    outcome, not an error.
-/
def hasCodeOrNonceAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.hcon_predicate (GuestAddrs.has_code_or_nonce_at_header_state_root + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hcon_predicate (GuestAddrs.has_code_or_nonce_at_header_state_root + 52)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.hcon_state_root (GuestAddrs.has_code_or_nonce_at_header_state_root + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.hcon_state_root (GuestAddrs.has_code_or_nonce_at_header_state_root + 72)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.has_code_or_nonce_at_header_state_root + 80)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (216 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.hcon_state_root (GuestAddrs.has_code_or_nonce_at_header_state_root + 104)),
    .ADDI .x12 .x12 (laLo GuestAddrs.hcon_state_root (GuestAddrs.has_code_or_nonce_at_header_state_root + 104)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x21 (laHi GuestAddrs.hcon_acct_struct (GuestAddrs.has_code_or_nonce_at_header_state_root + 120)),
    .ADDI .x21 .x21 (laLo GuestAddrs.hcon_acct_struct (GuestAddrs.has_code_or_nonce_at_header_state_root + 120)),
    .MV .x15 .x21,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.has_code_or_nonce_at_header_state_root + 132)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (160 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (152 : BitVec 21),
    .LD .x6 .x21 (0 : BitVec 12),
    .BNE .x6 .x0 (124 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hcon_empty_trie_root (GuestAddrs.has_code_or_nonce_at_header_state_root + 168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hcon_empty_trie_root (GuestAddrs.has_code_or_nonce_at_header_state_root + 168)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x21 (40 : BitVec 12),
    .BNE .x6 .x7 (104 : BitVec 13),
    .LD .x6 .x5 (8 : BitVec 12),
    .LD .x7 .x21 (48 : BitVec 12),
    .BNE .x6 .x7 (92 : BitVec 13),
    .LD .x6 .x5 (16 : BitVec 12),
    .LD .x7 .x21 (56 : BitVec 12),
    .BNE .x6 .x7 (80 : BitVec 13),
    .LD .x6 .x5 (24 : BitVec 12),
    .LD .x7 .x21 (64 : BitVec 12),
    .BNE .x6 .x7 (68 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hcon_empty_code_hash (GuestAddrs.has_code_or_nonce_at_header_state_root + 224)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hcon_empty_code_hash (GuestAddrs.has_code_or_nonce_at_header_state_root + 224)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x21 (72 : BitVec 12),
    .BNE .x6 .x7 (48 : BitVec 13),
    .LD .x6 .x5 (8 : BitVec 12),
    .LD .x7 .x21 (80 : BitVec 12),
    .BNE .x6 .x7 (36 : BitVec 13),
    .LD .x6 .x5 (16 : BitVec 12),
    .LD .x7 .x21 (88 : BitVec 12),
    .BNE .x6 .x7 (24 : BitVec 13),
    .LD .x6 .x5 (24 : BitVec 12),
    .LD .x7 .x21 (96 : BitVec 12),
    .BNE .x6 .x7 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.hcon_predicate (GuestAddrs.has_code_or_nonce_at_header_state_root + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hcon_predicate (GuestAddrs.has_code_or_nonce_at_header_state_root + 288)),
    .LI .x6 (1 : Word),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `hasCodeOrNonceAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def hasCodeOrNonceAtHeaderStateRoot_relocs : RelocTable :=
  [ (13, .la .x5 "hcon_predicate"),
    (18, .la .x12 "hcon_state_root"),
    (20, .jal .x1 "header_extract_state_root"),
    (26, .la .x12 "hcon_state_root"),
    (30, .la .x21 "hcon_acct_struct"),
    (33, .jal .x1 "account_at_address"),
    (42, .la .x5 "hcon_empty_trie_root"),
    (56, .la .x5 "hcon_empty_code_hash"),
    (72, .la .x5 "hcon_predicate") ]

def hasCodeOrNonceAtHeaderStateRootFunction : String :=
  "has_code_or_nonce_at_header_state_root:\n" ++ emitProgramR hasCodeOrNonceAtHeaderStateRoot_prog hasCodeOrNonceAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `hasCodeOrNonceAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem hasCodeOrNonceAtHeaderStateRootFunction_eq_prog :
    hasCodeOrNonceAtHeaderStateRootFunction = "has_code_or_nonce_at_header_state_root:\n" ++ emitProgramR hasCodeOrNonceAtHeaderStateRoot_prog hasCodeOrNonceAtHeaderStateRoot_relocs := rfl

#guard hasCodeOrNonceAtHeaderStateRootFunction.startsWith "has_code_or_nonce_at_header_state_root:\n"
/-- `zisk_has_code_or_nonce_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..16 : predicate (u64; 0 or 1) -/
def ziskHasCodeOrNonceAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  jal ra, has_code_or_nonce_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  la t1, hcon_predicate; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Lhcon_pdone\n" ++
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
  hasCodeOrNonceAtHeaderStateRootFunction ++ "\n" ++
  ".Lhcon_pdone:"

def ziskHasCodeOrNonceAtHeaderStateRootDataSection : String :=
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
  "hcon_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hcon_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "hcon_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "hcon_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "hcon_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
