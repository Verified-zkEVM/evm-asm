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

import EvmAsm.Rv64.Program
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
    .JAL .x1 (jalOff GuestAddrs.header_extended_decode_arity_check (GuestAddrs.validate_header_rlp_pair + 48)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header_rlp_pair + 160) (GuestAddrs.validate_header_rlp_pair + 52)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 64)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 64)),
    .JAL .x1 (jalOff GuestAddrs.header_extended_decode (GuestAddrs.validate_header_rlp_pair + 72)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header_rlp_pair + 160) (GuestAddrs.validate_header_rlp_pair + 76)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.header_extended_decode_arity_check (GuestAddrs.validate_header_rlp_pair + 88)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header_rlp_pair + 168) (GuestAddrs.validate_header_rlp_pair + 92)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 104)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 104)),
    .JAL .x1 (jalOff GuestAddrs.header_extended_decode (GuestAddrs.validate_header_rlp_pair + 112)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 128)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vhrp_this_struct (GuestAddrs.validate_header_rlp_pair + 128)),
    .AUIPC .x13 (laHi GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 136)),
    .ADDI .x13 .x13 (laLo GuestAddrs.vhrp_parent_struct (GuestAddrs.validate_header_rlp_pair + 136)),
    .MV .x14 .x18,
    .MV .x15 .x19,
    .JAL .x1 (jalOff GuestAddrs.validate_header (GuestAddrs.validate_header_rlp_pair + 152)),
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
  [ (12, .jal .x1 "header_extended_decode_arity_check"),
    (16, .la .x12 "vhrp_this_struct"),
    (18, .jal .x1 "header_extended_decode"),
    (22, .jal .x1 "header_extended_decode_arity_check"),
    (26, .la .x12 "vhrp_parent_struct"),
    (28, .jal .x1 "header_extended_decode"),
    (32, .la .x12 "vhrp_this_struct"),
    (34, .la .x13 "vhrp_parent_struct"),
    (38, .jal .x1 "validate_header") ]

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
#guard validateHeaderRlpPair_prog.length = 50

end EvmAsm.Codegen
