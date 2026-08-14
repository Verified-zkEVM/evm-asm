/-
  EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard

  The former nonce-reuse guard was retired from the stateless guest: its
  emitted symbol had no call or jump references.  This module now retains the
  small `enrg_u32le` helper, which is still linked by the guest and has a
  verified SAsm port.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## enrg_u32le -- local unaligned u32 little-endian reader. -/
def enrgU32le_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LBU .x6 .x10 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (2 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (3 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x10 .x5 .x6,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def enrgU32leFunction : String :=
  "enrg_u32le:\n" ++ emitProgram enrgU32le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `enrgU32le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem enrgU32leFunction_eq_prog :
    enrgU32leFunction = "enrg_u32le:\n" ++ emitProgram enrgU32le_prog := rfl

#guard enrgU32leFunction.startsWith "enrg_u32le:\n"

end EvmAsm.Codegen
