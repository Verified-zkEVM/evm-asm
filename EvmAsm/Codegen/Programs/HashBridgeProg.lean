/-
  EvmAsm.Codegen.Programs.HashBridgeProg

  GH #10753 layout-parameterised LEAF for the host-hash bridge stubs
  (`zkvm_sha256`, `zkvm_keccak256`, `zkvm_keccak256_segments`): the
  verification Programs are `_prog_of (L : GuestLayout)`, abstract over the
  guest link layout, and this module imports NOTHING concrete (no
  GuestAddrs).  The applied `_prog : Program` values live in the bridge
  `EvmAsm.Codegen.Programs.HashBridge` (the manifest path, unchanged), so
  every consumer keeps compiling untouched.

  Emission (`*Function` strings, `_eq_prog` drift guards, `#guard` length
  facts) is stated against `GuestLayout.zero`: `emitProgramR` keeps
  `la`/`jal` symbolic via the reloc side-tables, so the emitted text is
  layout-independent.  The concrete immediates are tied to the real link by
  the bridge and by `check-asm-to-program`'s concrete-render gate.

  The `_prog_of` bodies below are generated verbatim by
  `scripts/asm_to_program.py` (gen_lean_layout); do not hand-edit the
  blocks.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestLayout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def zkvmSha256_prog_of (L : GuestLayout) : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x18 (16 : BitVec 12),
    .SD .x2 .x19 (24 : BitVec 12),
    .SD .x2 .x20 (32 : BitVec 12),
    .SD .x2 .x21 (40 : BitVec 12),
    .AUIPC .x8 (laHi L.sha256_w_state (L.zkvm_sha256 + 28)),
    .ADDI .x8 .x8 (laLo L.sha256_w_state (L.zkvm_sha256 + 28)),
    .MV .x9 .x10,
    .MV .x18 .x11,
    .MV .x19 .x12,
    .SLLI .x20 .x11 (3 : BitVec 6),
    .AUIPC .x21 (laHi L.sha256_w_input (L.zkvm_sha256 + 52)),
    .ADDI .x21 .x21 (laLo L.sha256_w_input (L.zkvm_sha256 + 52)),
    .AUIPC .x5 (laHi L.sha256_w_iv (L.zkvm_sha256 + 60)),
    .ADDI .x5 .x5 (laLo L.sha256_w_iv (L.zkvm_sha256 + 60)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x8 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x8 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x8 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x8 .x6 (24 : BitVec 12),
    .LI .x5 (64 : Word),
    .BLT .x18 .x5 (92 : BitVec 13),
    .LD .x5 .x9 (0 : BitVec 12),
    .SD .x21 .x5 (0 : BitVec 12),
    .LD .x5 .x9 (8 : BitVec 12),
    .SD .x21 .x5 (8 : BitVec 12),
    .LD .x5 .x9 (16 : BitVec 12),
    .SD .x21 .x5 (16 : BitVec 12),
    .LD .x5 .x9 (24 : BitVec 12),
    .SD .x21 .x5 (24 : BitVec 12),
    .LD .x5 .x9 (32 : BitVec 12),
    .SD .x21 .x5 (32 : BitVec 12),
    .LD .x5 .x9 (40 : BitVec 12),
    .SD .x21 .x5 (40 : BitVec 12),
    .LD .x5 .x9 (48 : BitVec 12),
    .SD .x21 .x5 (48 : BitVec 12),
    .LD .x5 .x9 (56 : BitVec 12),
    .SD .x21 .x5 (56 : BitVec 12),
    .AUIPC .x10 (laHi L.sha256_w_params (L.zkvm_sha256 + 172)),
    .ADDI .x10 .x10 (laLo L.sha256_w_params (L.zkvm_sha256 + 172)),
    .CSRS (2053 : BitVec 12) .x10,
    .ADDI .x9 .x9 (64 : BitVec 12),
    .ADDI .x18 .x18 (-64 : BitVec 12),
    .JAL .x0 (-92 : BitVec 21),
    .SD .x21 .x0 (0 : BitVec 12),
    .SD .x21 .x0 (8 : BitVec 12),
    .SD .x21 .x0 (16 : BitVec 12),
    .SD .x21 .x0 (24 : BitVec 12),
    .SD .x21 .x0 (32 : BitVec 12),
    .SD .x21 .x0 (40 : BitVec 12),
    .SD .x21 .x0 (48 : BitVec 12),
    .SD .x21 .x0 (56 : BitVec 12),
    .MV .x5 .x21,
    .MV .x6 .x9,
    .MV .x7 .x18,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x6 (0 : BitVec 12),
    .SB .x5 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x5 .x21 .x18,
    .LI .x6 (128 : Word),
    .SB .x5 .x6 (0 : BitVec 12),
    .LI .x5 (56 : Word),
    .BLT .x18 .x5 (48 : BitVec 13),
    .AUIPC .x10 (laHi L.sha256_w_params (L.zkvm_sha256 + 288)),
    .ADDI .x10 .x10 (laLo L.sha256_w_params (L.zkvm_sha256 + 288)),
    .CSRS (2053 : BitVec 12) .x10,
    .SD .x21 .x0 (0 : BitVec 12),
    .SD .x21 .x0 (8 : BitVec 12),
    .SD .x21 .x0 (16 : BitVec 12),
    .SD .x21 .x0 (24 : BitVec 12),
    .SD .x21 .x0 (32 : BitVec 12),
    .SD .x21 .x0 (40 : BitVec 12),
    .SD .x21 .x0 (48 : BitVec 12),
    .SD .x21 .x0 (56 : BitVec 12),
    .ADDI .x5 .x21 (56 : BitVec 12),
    .SRLI .x6 .x20 (56 : BitVec 6),
    .SB .x5 .x6 (0 : BitVec 12),
    .SRLI .x6 .x20 (48 : BitVec 6),
    .SB .x5 .x6 (1 : BitVec 12),
    .SRLI .x6 .x20 (40 : BitVec 6),
    .SB .x5 .x6 (2 : BitVec 12),
    .SRLI .x6 .x20 (32 : BitVec 6),
    .SB .x5 .x6 (3 : BitVec 12),
    .SRLI .x6 .x20 (24 : BitVec 6),
    .SB .x5 .x6 (4 : BitVec 12),
    .SRLI .x6 .x20 (16 : BitVec 6),
    .SB .x5 .x6 (5 : BitVec 12),
    .SRLI .x6 .x20 (8 : BitVec 6),
    .SB .x5 .x6 (6 : BitVec 12),
    .SB .x5 .x20 (7 : BitVec 12),
    .AUIPC .x10 (laHi L.sha256_w_params (L.zkvm_sha256 + 396)),
    .ADDI .x10 .x10 (laLo L.sha256_w_params (L.zkvm_sha256 + 396)),
    .CSRS (2053 : BitVec 12) .x10,
    .LI .x5 (0 : Word),
    .LI .x6 (32 : Word),
    .BEQ .x5 .x6 (32 : BitVec 13),
    .XORI .x7 .x5 (3 : BitVec 12),
    .ADD .x28 .x8 .x7,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x30 .x19 .x5,
    .SB .x30 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x18 .x2 (16 : BitVec 12),
    .LD .x19 .x2 (24 : BitVec 12),
    .LD .x20 .x2 (32 : BitVec 12),
    .LD .x21 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `zkvmSha256_prog_of`: the `la`/cross-`jal` instruction
    indices kept SYMBOLIC in the emitted image text (`emitProgramR`), while
    the Program above carries the layout-parameterised immediates
    (`laHi`/`laLo`/`jalOff L.…`) for verification. -/
def zkvmSha256_relocs : RelocTable :=
  [ (7, .la .x8 "sha256_w_state"),
    (13, .la .x21 "sha256_w_input"),
    (15, .la .x5 "sha256_w_iv"),
    (43, .la .x10 "sha256_w_params"),
    (72, .la .x10 "sha256_w_params"),
    (99, .la .x10 "sha256_w_params") ]

def zkvmSha256Function : String :=
  "zkvm_sha256:\n" ++ emitProgramR (zkvmSha256_prog_of .zero) zkvmSha256_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `zkvmSha256_prog_of .zero` rendered under its label with the
    `la`/`jal` relocs kept symbolic (layout-parameterised per GH #10753;
    emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp
    over the bridge's `zkvmSha256_prog` (`_of guestLayout`). -/
theorem zkvmSha256Function_eq_prog :
    zkvmSha256Function = "zkvm_sha256:\n" ++ emitProgramR (zkvmSha256_prog_of .zero) zkvmSha256_relocs := rfl

#guard zkvmSha256Function.startsWith "zkvm_sha256:\n"
#guard (zkvmSha256_prog_of .zero).length = 121

def zkvmKeccak256_prog_of (L : GuestLayout) : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x18 (16 : BitVec 12),
    .SD .x2 .x20 (24 : BitVec 12),
    .MV .x20 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x8 (laHi L.zk3_state (L.zkvm_keccak256 + 32)),
    .ADDI .x8 .x8 (laLo L.zk3_state (L.zkvm_keccak256 + 32)),
    .MV .x28 .x8,
    .LI .x29 (25 : Word),
    .SD .x28 .x0 (0 : BitVec 12),
    .ADDI .x28 .x28 (8 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-12 : BitVec 13),
    .LI .x29 (136 : Word),
    .BLT .x9 .x29 (68 : BitVec 13),
    .MV .x28 .x8,
    .MV .x30 .x20,
    .LI .x31 (17 : Word),
    .LD .x5 .x30 (0 : BitVec 12),
    .LD .x6 .x28 (0 : BitVec 12),
    .XOR .x6 .x6 .x5,
    .SD .x28 .x6 (0 : BitVec 12),
    .ADDI .x28 .x28 (8 : BitVec 12),
    .ADDI .x30 .x30 (8 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .BNE .x31 .x0 (-28 : BitVec 13),
    .MV .x10 .x8,
    .CSRS (2048 : BitVec 12) .x10,
    .ADDI .x20 .x20 (136 : BitVec 12),
    .ADDI .x9 .x9 (-136 : BitVec 12),
    .JAL .x0 (-68 : BitVec 21),
    .MV .x28 .x8,
    .MV .x30 .x20,
    .BEQ .x9 .x0 (36 : BitVec 13),
    .LBU .x5 .x30 (0 : BitVec 12),
    .LBU .x6 .x28 (0 : BitVec 12),
    .XOR .x5 .x5 .x6,
    .SB .x28 .x5 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x9 .x9 (-1 : BitVec 12),
    .BNE .x9 .x0 (-28 : BitVec 13),
    .LBU .x5 .x28 (0 : BitVec 12),
    .XORI .x5 .x5 (1 : BitVec 12),
    .SB .x28 .x5 (0 : BitVec 12),
    .ADDI .x28 .x8 (135 : BitVec 12),
    .LBU .x5 .x28 (0 : BitVec 12),
    .XORI .x5 .x5 (128 : BitVec 12),
    .SB .x28 .x5 (0 : BitVec 12),
    .MV .x10 .x8,
    .CSRS (2048 : BitVec 12) .x10,
    .LD .x5 .x8 (0 : BitVec 12),
    .SD .x18 .x5 (0 : BitVec 12),
    .LD .x5 .x8 (8 : BitVec 12),
    .SD .x18 .x5 (8 : BitVec 12),
    .LD .x5 .x8 (16 : BitVec 12),
    .SD .x18 .x5 (16 : BitVec 12),
    .LD .x5 .x8 (24 : BitVec 12),
    .SD .x18 .x5 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x18 .x2 (16 : BitVec 12),
    .LD .x20 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `zkvmKeccak256_prog_of`: the `la`/cross-`jal` instruction
    indices kept SYMBOLIC in the emitted image text (`emitProgramR`), while
    the Program above carries the layout-parameterised immediates
    (`laHi`/`laLo`/`jalOff L.…`) for verification. -/
def zkvmKeccak256_relocs : RelocTable :=
  [ (8, .la .x8 "zk3_state") ]

def zkvmKeccak256Function : String :=
  "zkvm_keccak256:\n" ++ emitProgramR (zkvmKeccak256_prog_of .zero) zkvmKeccak256_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `zkvmKeccak256_prog_of .zero` rendered under its label with the
    `la`/`jal` relocs kept symbolic (layout-parameterised per GH #10753;
    emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp
    over the bridge's `zkvmKeccak256_prog` (`_of guestLayout`). -/
theorem zkvmKeccak256Function_eq_prog :
    zkvmKeccak256Function = "zkvm_keccak256:\n" ++ emitProgramR (zkvmKeccak256_prog_of .zero) zkvmKeccak256_relocs := rfl

#guard zkvmKeccak256Function.startsWith "zkvm_keccak256:\n"
#guard (zkvmKeccak256_prog_of .zero).length = 69

def zkvmKeccak256Segments_prog_of (L : GuestLayout) : Program :=
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
    .AUIPC .x19 (laHi L.zk3_state (L.zkvm_keccak256_segments + 48)),
    .ADDI .x19 .x19 (laLo L.zk3_state (L.zkvm_keccak256_segments + 48)),
    .MV .x5 .x19,
    .LI .x6 (25 : Word),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-12 : BitVec 13),
    .LI .x20 (0 : Word),
    .BEQ .x9 .x0 (80 : BitVec 13),
    .LD .x21 .x8 (0 : BitVec 12),
    .LD .x22 .x8 (8 : BitVec 12),
    .ADDI .x8 .x8 (16 : BitVec 12),
    .ADDI .x9 .x9 (-1 : BitVec 12),
    .BEQ .x22 .x0 (-20 : BitVec 13),
    .LBU .x5 .x21 (0 : BitVec 12),
    .ADD .x6 .x19 .x20,
    .LBU .x7 .x6 (0 : BitVec 12),
    .XOR .x7 .x7 .x5,
    .SB .x6 .x7 (0 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .ADDI .x22 .x22 (-1 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .LI .x5 (136 : Word),
    .BNE .x20 .x5 (-40 : BitVec 13),
    .MV .x10 .x19,
    .CSRS (2048 : BitVec 12) .x10,
    .LI .x20 (0 : Word),
    .JAL .x0 (-56 : BitVec 21),
    .ADD .x6 .x19 .x20,
    .LBU .x7 .x6 (0 : BitVec 12),
    .XORI .x7 .x7 (1 : BitVec 12),
    .SB .x6 .x7 (0 : BitVec 12),
    .ADDI .x6 .x19 (135 : BitVec 12),
    .LBU .x7 .x6 (0 : BitVec 12),
    .XORI .x7 .x7 (128 : BitVec 12),
    .SB .x6 .x7 (0 : BitVec 12),
    .MV .x10 .x19,
    .CSRS (2048 : BitVec 12) .x10,
    .LD .x5 .x19 (0 : BitVec 12),
    .SD .x18 .x5 (0 : BitVec 12),
    .LD .x5 .x19 (8 : BitVec 12),
    .SD .x18 .x5 (8 : BitVec 12),
    .LD .x5 .x19 (16 : BitVec 12),
    .SD .x18 .x5 (16 : BitVec 12),
    .LD .x5 .x19 (24 : BitVec 12),
    .SD .x18 .x5 (24 : BitVec 12),
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

/-- Reloc side-table for `zkvmKeccak256Segments_prog_of`: the `la`/cross-`jal` instruction
    indices kept SYMBOLIC in the emitted image text (`emitProgramR`), while
    the Program above carries the layout-parameterised immediates
    (`laHi`/`laLo`/`jalOff L.…`) for verification. -/
def zkvmKeccak256Segments_relocs : RelocTable :=
  [ (12, .la .x19 "zk3_state") ]

def zkvmKeccak256SegmentsFunction : String :=
  "zkvm_keccak256_segments:\n" ++ emitProgramR (zkvmKeccak256Segments_prog_of .zero) zkvmKeccak256Segments_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `zkvmKeccak256Segments_prog_of .zero` rendered under its label with the
    `la`/`jal` relocs kept symbolic (layout-parameterised per GH #10753;
    emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp
    over the bridge's `zkvmKeccak256Segments_prog` (`_of guestLayout`). -/
theorem zkvmKeccak256SegmentsFunction_eq_prog :
    zkvmKeccak256SegmentsFunction = "zkvm_keccak256_segments:\n" ++ emitProgramR (zkvmKeccak256Segments_prog_of .zero) zkvmKeccak256Segments_relocs := rfl

#guard zkvmKeccak256SegmentsFunction.startsWith "zkvm_keccak256_segments:\n"
#guard (zkvmKeccak256Segments_prog_of .zero).length = 70

end EvmAsm.Codegen
