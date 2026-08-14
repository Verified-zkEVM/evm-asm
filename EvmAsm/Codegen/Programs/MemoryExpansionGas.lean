/-
  EvmAsm.Codegen.Programs.MemoryExpansionGas

  `memory_expansion_gas` (bead nxio8.2) — the exact Amsterdam memory-expansion gas
  charge, the second dynamic-gas leaf the dispatcher needs (the metering currently
  drops memory-expansion cost; see nxio8).

  Per execution-specs amsterdam `vm/gas.py` `calculate_memory_gas_cost`:

      words = ceil32(size_in_bytes) // 32 = (size_in_bytes + 31) // 32
      cost(size)  = words * MEMORY_PER_WORD(3) + words^2 // 512

  A memory-touching op (MLOAD/MSTORE/MSTORE8/MCOPY/*COPY/KECCAK256/LOG/RETURN/
  REVERT/CREATE…) charges the *expansion*: `cost(new_size) - cost(old_size)`
  (0 when it does not grow memory). Pure unsigned 64-bit arithmetic — no helper
  calls.

  NOT wired into the dispatcher's memory-op handlers (that is the follow-up,
  dispatcher-gas / Dispatch.lean domain). Soundness-neutral foundation, like
  nxio8.1 (`sstore_regular_gas`, #8630).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## memory_expansion_gas
    a0 = old size in bytes   a1 = new size in bytes
    a0 (output) = the memory-expansion gas charge = cost(new) - cost(old), or 0 if
    new <= old. cost(b) = w*3 + w*w/512 with w = (b + 31) >> 5. Leaf (no calls). -/
def memoryExpansionGas_prog : Program :=
  [ .BGEU .x10 .x11 (64 : BitVec 13),
    .ADDI .x5 .x10 (31 : BitVec 12),
    .SRLI .x5 .x5 (5 : BitVec 6),
    .ADDI .x6 .x11 (31 : BitVec 12),
    .SRLI .x6 .x6 (5 : BitVec 6),
    .LI .x7 (3 : Word),
    .MUL .x28 .x5 .x7,
    .MUL .x29 .x5 .x5,
    .SRLI .x29 .x29 (9 : BitVec 6),
    .ADD .x28 .x28 .x29,
    .MUL .x30 .x6 .x7,
    .MUL .x31 .x6 .x6,
    .SRLI .x31 .x31 (9 : BitVec 6),
    .ADD .x30 .x30 .x31,
    .SUB .x10 .x30 .x28,
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def memoryExpansionGasFunction : String :=
  "memory_expansion_gas:\n" ++ emitProgram memoryExpansionGas_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `memoryExpansionGas_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem memoryExpansionGasFunction_eq_prog :
    memoryExpansionGasFunction = "memory_expansion_gas:\n" ++ emitProgram memoryExpansionGas_prog := rfl

#guard memoryExpansionGasFunction.startsWith "memory_expansion_gas:\n"
/-- `zisk_memory_expansion_gas`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : old size in bytes (u64)
      bytes 16..24 : new size in bytes (u64)
    Output: bytes 0..8 = the memory-expansion gas charge. -/
def ziskMemoryExpansionGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a0, 8(t6)                # old size\n" ++
  "  ld a1, 16(t6)               # new size\n" ++
  "  jal ra, memory_expansion_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # gas\n" ++
  "  j .Lmeg_pdone\n" ++
  memoryExpansionGasFunction ++ "\n" ++
  ".Lmeg_pdone:"


end EvmAsm.Codegen
