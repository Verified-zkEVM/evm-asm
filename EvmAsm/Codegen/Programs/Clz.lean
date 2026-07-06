/-
  EvmAsm.Codegen.Programs.Clz

  Raw dispatcher helper for the EIP-7939 CLZ opcode.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.ClzSAsm

namespace EvmAsm.Codegen

/-- Legacy raw RV64IM handler for EIP-7939 CLZ (0x1e).

    The dispatcher registry now uses ClzSAsm.clz_verified; this raw tail is
    retained as a historical reference for the instruction sequence it replaced.

    Desired behavior is from execution-specs
    `bpo*/vm/instructions/bitwise.py::count_leading_zeros`: pop one
    256-bit word and push `256 - value.bit_length()`, with zero mapping
    to 256. Since the operation is stack-neutral, this handler overwrites
    the top stack word in place and clears the high limbs. It avoids the
    optional RISC-V Zbb `clz` instruction so it runs on the current
    RV64IM assembler/emulator path. -/
def clzTail : HandlerTail :=
  .custom (
    "  ld x14, 24(x12)\n" ++
    "  li x15, 0\n" ++
    "  bnez x14, .Lclz64_start\n" ++
    "  ld x14, 16(x12)\n" ++
    "  li x15, 64\n" ++
    "  bnez x14, .Lclz64_start\n" ++
    "  ld x14, 8(x12)\n" ++
    "  li x15, 128\n" ++
    "  bnez x14, .Lclz64_start\n" ++
    "  ld x14, 0(x12)\n" ++
    "  li x15, 192\n" ++
    "  bnez x14, .Lclz64_start\n" ++
    "  li x15, 256\n" ++
    "  j .Lclz_write\n" ++
    ".Lclz64_start:\n" ++
    "  srli x16, x14, 32\n" ++
    "  bnez x16, .Lclz_after32\n" ++
    "  addi x15, x15, 32\n" ++
    "  slli x14, x14, 32\n" ++
    ".Lclz_after32:\n" ++
    "  srli x16, x14, 48\n" ++
    "  bnez x16, .Lclz_after16\n" ++
    "  addi x15, x15, 16\n" ++
    "  slli x14, x14, 16\n" ++
    ".Lclz_after16:\n" ++
    "  srli x16, x14, 56\n" ++
    "  bnez x16, .Lclz_after8\n" ++
    "  addi x15, x15, 8\n" ++
    "  slli x14, x14, 8\n" ++
    ".Lclz_after8:\n" ++
    "  srli x16, x14, 60\n" ++
    "  bnez x16, .Lclz_after4\n" ++
    "  addi x15, x15, 4\n" ++
    "  slli x14, x14, 4\n" ++
    ".Lclz_after4:\n" ++
    "  srli x16, x14, 62\n" ++
    "  bnez x16, .Lclz_after2\n" ++
    "  addi x15, x15, 2\n" ++
    "  slli x14, x14, 2\n" ++
    ".Lclz_after2:\n" ++
    "  srli x16, x14, 63\n" ++
    "  bnez x16, .Lclz_write\n" ++
    "  addi x15, x15, 1\n" ++
    ".Lclz_write:\n" ++
    "  sd x15, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  ret")

end EvmAsm.Codegen
