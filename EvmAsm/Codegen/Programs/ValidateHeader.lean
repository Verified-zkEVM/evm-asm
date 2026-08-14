/-
  EvmAsm.Codegen.Programs.ValidateHeader

  `validate_header` — SpecRef-shaped replacement for the former
  three-way split (`validate_header_full` + parent-relative chain
  helpers + `header_validate_parent_hash` at the pair site).

  Mirrors `SpecRef.validate_header` (`SeamShell.lean`) / `fork.py`
  `validate_header(parent_header, header)`: same conjuncts, reference
  order, one early-exit status per check. GH #12345; correspondence
  proof is #12346.

  Status (a0):
    0  ok
    1  number < 1
    2  excess blob gas mismatch
    3  gas used > gas limit
    4  gas-limit bounds / base-fee mismatch
       (`calculate_base_fee_per_gas` embeds `check_gas_limit`)
    5  timestamp ≤ parent
    6  number ≠ parent + 1
    7  extra data > 32
    8  difficulty nonzero          ⎤ mapped from `header_validate_post_merge`
    9  nonce nonzero               ⎥ sub-status (walk still visits ommers
   10  ommers hash mismatch        ⎦ field first; multi-fault status may
                                   differ from SpecRef which checks
                                   difficulty→nonce→ommers — both reject)
   11  parent hash mismatch
   12  post-merge / extra-data RLP parse failure

  ABI (after the caller has decoded both headers into K39 structs):
    a0 = this RLP ptr          a1 = this RLP length
    a2 = this extended struct  a3 = parent extended struct
    a4 = parent RLP ptr        a5 = parent RLP length
    a0 (out) = status above

  Re-emitted as SAsm-friendly straight-line early-exit composition of
  existing leaf Programs (no byte-equivalence with `validate_header_full`).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## validate_header — SpecRef.validate_header guest mirror (#12345) -/

/-- GNU-as body. Symbolic `jal` targets; concrete `Program` + `jalOff`
    land after the first relink / `asm_to_program.py` conversion. -/
def validateHeader_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
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
    .MV .x21 .x15,
    .LD .x5 .x18 (64 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.validate_header + 260) (GuestAddrs.validate_header + 60)),
    .LD .x10 .x18 (136 : BitVec 12),
    .LD .x11 .x19 (128 : BitVec 12),
    .LD .x12 .x19 (136 : BitVec 12),
    .ADDI .x13 .x19 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.header_validate_excess_blob_gas (GuestAddrs.validate_header + 80)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header + 268) (GuestAddrs.validate_header + 84)),
    .LD .x5 .x18 (88 : BitVec 12),
    .LD .x6 .x18 (80 : BitVec 12),
    .BLTU .x6 .x5 (brOff (GuestAddrs.validate_header + 276) (GuestAddrs.validate_header + 96)),
    .LD .x10 .x18 (80 : BitVec 12),
    .LD .x11 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.check_gas_limit (GuestAddrs.validate_header + 108)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header + 284) (GuestAddrs.validate_header + 112)),
    .ADDI .x10 .x18 (96 : BitVec 12),
    .LD .x11 .x19 (80 : BitVec 12),
    .LD .x12 .x19 (88 : BitVec 12),
    .ADDI .x13 .x19 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.header_validate_base_fee (GuestAddrs.validate_header + 132)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header + 284) (GuestAddrs.validate_header + 136)),
    .LD .x5 .x18 (72 : BitVec 12),
    .LD .x6 .x19 (72 : BitVec 12),
    .BGEU .x6 .x5 (brOff (GuestAddrs.validate_header + 292) (GuestAddrs.validate_header + 148)),
    .LD .x5 .x18 (64 : BitVec 12),
    .LD .x6 .x19 (64 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.validate_header + 300) (GuestAddrs.validate_header + 164)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.header_validate_extra_data_length (GuestAddrs.validate_header + 176)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header + 308) (GuestAddrs.validate_header + 180)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.header_validate_post_merge (GuestAddrs.validate_header + 192)),
    .BEQ .x10 .x0 (32 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.validate_header + 332) (GuestAddrs.validate_header + 204)),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.validate_header + 316) (GuestAddrs.validate_header + 212)),
    .LI .x5 (3 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.validate_header + 324) (GuestAddrs.validate_header + 220)),
    .JAL .x0 (jalOff (GuestAddrs.validate_header + 348) (GuestAddrs.validate_header + 224)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x20,
    .MV .x13 .x21,
    .JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash (GuestAddrs.validate_header + 244)),
    .BNE .x10 .x0 (brOff (GuestAddrs.validate_header + 340) (GuestAddrs.validate_header + 248)),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 256)),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 264)),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 272)),
    .LI .x10 (3 : Word),
    .JAL .x0 (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 280)),
    .LI .x10 (4 : Word),
    .JAL .x0 (jalOff (GuestAddrs.validate_header + 352) (GuestAddrs.validate_header + 288)),
    .LI .x10 (5 : Word),
    .JAL .x0 (56 : BitVec 21),
    .LI .x10 (6 : Word),
    .JAL .x0 (48 : BitVec 21),
    .LI .x10 (7 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LI .x10 (8 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (9 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (10 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (11 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (12 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `validateHeader_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def validateHeader_relocs : RelocTable :=
  [ (20, .jal .x1 "header_validate_excess_blob_gas"),
    (27, .jal .x1 "check_gas_limit"),
    (33, .jal .x1 "header_validate_base_fee"),
    (44, .jal .x1 "header_validate_extra_data_length"),
    (48, .jal .x1 "header_validate_post_merge"),
    (61, .jal .x1 "header_validate_parent_hash") ]

def validateHeaderFunction : String :=
  "validate_header:\n" ++ emitProgramR validateHeader_prog validateHeader_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `validateHeader_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem validateHeaderFunction_eq_prog :
    validateHeaderFunction = "validate_header:\n" ++ emitProgramR validateHeader_prog validateHeader_relocs := rfl

#guard validateHeaderFunction.startsWith "validate_header:\n"

end EvmAsm.Codegen
