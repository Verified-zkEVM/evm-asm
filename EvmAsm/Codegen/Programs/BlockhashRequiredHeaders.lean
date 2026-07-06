/-
  EvmAsm.Codegen.Programs.BlockhashRequiredHeaders

  Bytecode scanners for stateless BLOCKHASH witness-depth validation.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## codes_blockhash_required_headers -- conservative BLOCKHASH witness-depth scan.

    Scans SSZ witness.codes bytecode entries for the concrete compiler pattern
    `PUSH1 offset; NUMBER; SUB; BLOCKHASH` (and the commuted
    `NUMBER; PUSH1 offset; SUB; BLOCKHASH` form). Returns the maximum observed
    offset. The top-level verdict uses this only for transaction-bearing blocks
    to reject witnesses whose header list is shorter than a code path can demand,
    matching execution-specs' in-window BLOCKHASH missing-header failure. -/
def codesBlockhashRequiredHeaders_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LI .x21 (0 : Word),
    .SD .x18 .x0 (0 : BitVec 12),
    .BEQ .x9 .x0 (232 : BitVec 13),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x19 .x5 (2 : BitVec 6),
    .LI .x20 (0 : Word),
    .BEQ .x20 .x19 (216 : BitVec 13),
    .SLLI .x5 .x20 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x22 .x8 .x7,
    .ADDI .x28 .x20 (1 : BitVec 12),
    .BEQ .x28 .x19 (20 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .MV .x29 .x9,
    .BLTU .x29 .x7 (180 : BitVec 13),
    .SUB .x23 .x29 .x7,
    .LI .x30 (5 : Word),
    .BLTU .x23 .x30 (148 : BitVec 13),
    .LI .x30 (5 : Word),
    .BLTU .x23 .x30 (140 : BitVec 13),
    .LBU .x5 .x22 (0 : BitVec 12),
    .LI .x6 (96 : Word),
    .BEQ .x5 .x6 (16 : BitVec 13),
    .LI .x6 (67 : Word),
    .BEQ .x5 .x6 (60 : BitVec 13),
    .JAL .x0 (104 : BitVec 21),
    .LBU .x7 .x22 (2 : BitVec 12),
    .LI .x28 (67 : Word),
    .BNE .x7 .x28 (92 : BitVec 13),
    .LBU .x7 .x22 (3 : BitVec 12),
    .LI .x28 (3 : Word),
    .BNE .x7 .x28 (80 : BitVec 13),
    .LBU .x7 .x22 (4 : BitVec 12),
    .LI .x28 (64 : Word),
    .BNE .x7 .x28 (68 : BitVec 13),
    .LBU .x29 .x22 (1 : BitVec 12),
    .BGEU .x21 .x29 (60 : BitVec 13),
    .MV .x21 .x29,
    .JAL .x0 (52 : BitVec 21),
    .LBU .x7 .x22 (1 : BitVec 12),
    .LI .x28 (96 : Word),
    .BNE .x7 .x28 (40 : BitVec 13),
    .LBU .x7 .x22 (3 : BitVec 12),
    .LI .x28 (3 : Word),
    .BNE .x7 .x28 (28 : BitVec 13),
    .LBU .x7 .x22 (4 : BitVec 12),
    .LI .x28 (64 : Word),
    .BNE .x7 .x28 (16 : BitVec 13),
    .LBU .x29 .x22 (2 : BitVec 12),
    .BGEU .x21 .x29 (8 : BitVec 13),
    .MV .x21 .x29,
    .ADDI .x22 .x22 (1 : BitVec 12),
    .ADDI .x23 .x23 (-1 : BitVec 12),
    .JAL .x0 (-140 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-212 : BitVec 21),
    .SD .x18 .x21 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def codesBlockhashRequiredHeadersFunction : String :=
  "codes_blockhash_required_headers:\n" ++ emitProgram codesBlockhashRequiredHeaders_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `codesBlockhashRequiredHeaders_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem codesBlockhashRequiredHeadersFunction_eq_prog :
    codesBlockhashRequiredHeadersFunction = "codes_blockhash_required_headers:\n" ++ emitProgram codesBlockhashRequiredHeaders_prog := rfl

#guard codesBlockhashRequiredHeadersFunction.startsWith "codes_blockhash_required_headers:\n"
#guard codesBlockhashRequiredHeaders_prog.length = 88
end EvmAsm.Codegen
