/-
  EvmAsm.Codegen.Programs.ValidateHeaderPair

  validate_header_rlp_pair: decode this/parent RLP into K39 structs, then
  call SpecRef-shaped `validate_header` (#12345). Retires the former
  `validate_header_full` + `header_validate_parent_hash` split at this site.

  Status:
    0          valid child
    1          this-header parse fail
    2          parent-header parse fail
    3..12      `validate_header` conjunct failure (see ValidateHeader.lean)
-/

import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.ValidateHeader
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## validate_header_rlp_pair -- decode then SpecRef.validate_header -/

def validateHeaderRlpPair_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 48)),
    .JAL .x1 (jalOff GuestAddrs.header_extended_decode (GuestAddrs.validate_header_rlp_pair + 56)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header_rlp_pair + 128) (GuestAddrs.validate_header_rlp_pair + 60)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 72)),
    .JAL .x1 (jalOff GuestAddrs.header_extended_decode (GuestAddrs.validate_header_rlp_pair + 80)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 96)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 96)),
    .AUIPC .x13 (laHi GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 104)),
    .ADDI .x13 .x13 (laLo GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 104)),
    .MV .x14 .x18,
    .MV .x15 .x19,
    .JAL .x1 (jalOff GuestAddrs.validate_header (GuestAddrs.validate_header_rlp_pair + 120)),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `validateHeaderRlpPair_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def validateHeaderRlpPair_relocs : RelocTable :=
  [ (12, .la .x12 "vhrp_this_struct"),
    (14, .jal .x1 "header_extended_decode"),
    (18, .la .x12 "vhrp_parent_struct"),
    (20, .jal .x1 "header_extended_decode"),
    (24, .la .x12 "vhrp_this_struct"),
    (26, .la .x13 "vhrp_parent_struct"),
    (30, .jal .x1 "validate_header") ]

def validateHeaderRlpPairFunction : String :=
  "validate_header_rlp_pair:\n" ++ emitProgramR validateHeaderRlpPair_prog validateHeaderRlpPair_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `validateHeaderRlpPair_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem validateHeaderRlpPairFunction_eq_prog :
    validateHeaderRlpPairFunction = "validate_header_rlp_pair:\n" ++ emitProgramR validateHeaderRlpPair_prog validateHeaderRlpPair_relocs := rfl

#guard validateHeaderRlpPairFunction.startsWith "validate_header_rlp_pair:\n"

/-- `zisk_validate_header_rlp_pair`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  this header RLP length (u64)
      +16 parent header RLP length (u64)
      +24 this header RLP bytes, immediately followed by parent header RLP
-/
def ziskValidateHeaderRlpPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)\n" ++
  "  ld a3, 16(a4)\n" ++
  "  addi a0, a4, 24\n" ++
  "  add a2, a0, a1\n" ++
  "  addi a2, a2, 7\n" ++
  "  andi a2, a2, -8\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvhrp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  amsterdamBlobGasPriceU256Function ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  headerValidateExcessBlobGasFunction ++ "\n" ++
  validateHeaderFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  validateHeaderRlpPairFunction ++ "\n" ++
  ".Lvhrp_pdone:"

/-- Data section: union of the leaf probe scratch plus the two decode structs. -/
def ziskValidateHeaderRlpPairDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "hvebg_threshold:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  "hvpm_off:\n  .zero 8\n" ++
  "hvpm_len:\n  .zero 8\n" ++
  "hved_off:\n  .zero 8\n" ++
  "hved_len:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "hmd_offset:\n  .zero 8\n" ++
  "hmd_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 32\n" ++
  "hvph_claimed:\n  .zero 32\n" ++
  "hvph_computed:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "vhrp_this_struct:\n  .zero 144\n" ++
  "vhrp_parent_struct:\n  .zero 144\n"

end EvmAsm.Codegen
