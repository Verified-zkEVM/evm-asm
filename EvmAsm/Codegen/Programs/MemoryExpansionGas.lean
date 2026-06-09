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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## memory_expansion_gas
    a0 = old size in bytes   a1 = new size in bytes
    a0 (output) = the memory-expansion gas charge = cost(new) - cost(old), or 0 if
    new <= old. cost(b) = w*3 + w*w/512 with w = (b + 31) >> 5. Leaf (no calls). -/
def memoryExpansionGasFunction : String :=
  "memory_expansion_gas:\n" ++
  "  bgeu a0, a1, .Lmeg_zero        # new <= old -> no expansion\n" ++
  "  addi t0, a0, 31; srli t0, t0, 5   # t0 = words_old = (old+31)/32\n" ++
  "  addi t1, a1, 31; srli t1, t1, 5   # t1 = words_new = (new+31)/32\n" ++
  "  li t2, 3\n" ++
  "  mul t3, t0, t2                 # words_old * 3\n" ++
  "  mul t4, t0, t0; srli t4, t4, 9 # words_old^2 / 512\n" ++
  "  add t3, t3, t4                 # cost_old\n" ++
  "  mul t5, t1, t2                 # words_new * 3\n" ++
  "  mul t6, t1, t1; srli t6, t6, 9 # words_new^2 / 512\n" ++
  "  add t5, t5, t6                 # cost_new\n" ++
  "  sub a0, t5, t3                 # expansion = cost_new - cost_old\n" ++
  "  ret\n" ++
  ".Lmeg_zero:\n" ++
  "  li a0, 0\n" ++
  "  ret"

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

def ziskMemoryExpansionGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMemoryExpansionGasPrologue
  dataAsm     := ""
}

end EvmAsm.Codegen
