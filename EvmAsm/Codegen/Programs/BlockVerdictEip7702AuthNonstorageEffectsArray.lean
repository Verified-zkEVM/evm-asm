import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def blockVerdictEip7702AuthNonstorageEffectsArray_prog : Program :=
  [ .ADDI .x2 .x2 (-88 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x24 .x15,
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (140 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 80)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BNE .x5 .x0 (124 : BitVec 13),
    .BLTU .x9 .x10 (120 : BitVec 13),
    .SRLI .x21 .x10 (2 : BitVec 6),
    .BNE .x21 .x18 (112 : BitVec 13),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x21 (104 : BitVec 13),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 120)),
    .MV .x23 .x10,
    .SLLI .x5 .x21 (2 : BitVec 6),
    .BLTU .x23 .x5 (72 : BitVec 13),
    .BLTU .x9 .x23 (68 : BitVec 13),
    .ADDI .x5 .x22 (1 : BitVec 12),
    .BEQ .x5 .x21 (20 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x10 .x8 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 156)),
    .JAL .x0 (8 : BitVec 21),
    .MV .x10 .x9,
    .BLTU .x10 .x23 (36 : BitVec 13),
    .BLTU .x9 .x10 (32 : BitVec 13),
    .ADD .x11 .x8 .x23,
    .SUB .x11 .x10 .x23,
    .ADD .x10 .x8 .x23,
    .MV .x12 .x19,
    .MV .x13 .x20,
    .MV .x14 .x24,
    .JAL .x1 (jalOff GuestAddrs.eip7702_auth_nonstorage_effects (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array + 200)),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-100 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (88 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictEip7702AuthNonstorageEffectsArray_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictEip7702AuthNonstorageEffectsArray_relocs : RelocTable :=
  [ (20, .jal .x1 "bgv_u32le"),
    (30, .jal .x1 "bgv_u32le"),
    (39, .jal .x1 "bgv_u32le"),
    (50, .jal .x1 "eip7702_auth_nonstorage_effects") ]

def blockVerdictEip7702AuthNonstorageEffectsArrayFunction : String :=
  "block_verdict_eip7702_auth_nonstorage_effects_array:\n" ++ emitProgramR blockVerdictEip7702AuthNonstorageEffectsArray_prog blockVerdictEip7702AuthNonstorageEffectsArray_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictEip7702AuthNonstorageEffectsArray_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictEip7702AuthNonstorageEffectsArrayFunction_eq_prog :
    blockVerdictEip7702AuthNonstorageEffectsArrayFunction = "block_verdict_eip7702_auth_nonstorage_effects_array:\n" ++ emitProgramR blockVerdictEip7702AuthNonstorageEffectsArray_prog blockVerdictEip7702AuthNonstorageEffectsArray_relocs := rfl

#guard blockVerdictEip7702AuthNonstorageEffectsArrayFunction.startsWith "block_verdict_eip7702_auth_nonstorage_effects_array:\n"
#guard blockVerdictEip7702AuthNonstorageEffectsArray_prog.length = 66

end EvmAsm.Codegen
