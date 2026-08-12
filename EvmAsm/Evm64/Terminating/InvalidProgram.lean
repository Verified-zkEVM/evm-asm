/-
  EvmAsm.Evm64.Terminating.InvalidProgram

  The verified `Program` image of the `INVALID` (0xfe) handler tail.

  The runtime dispatcher emits INVALID as `dispatchHaltRet 3`
  (`EvmAsm.Codegen.Dispatch`), whose assembler expansion is the seven
  RISC-V instructions

  ```
    li   x5, 3                 ; halt routing code (INVALID → .exit_invalid_op)
    la   x6, evm_halt_flag     ; auipc x6, hi2 ; addi x6, x6, lo2
    sd   x5, 0(x6)             ; evm_halt_flag := 3
    la   x1, .dispatch_resume ; auipc x1, hi1 ; addi x1, x1, lo1
    ret                        ; jalr x0, x1, 0  (reaches resume &&& ~~~1)
  ```

  `evm_invalid` is exactly that instruction list, parameterized by the two
  linker `la` immediate pairs (`hi2`/`lo2` for `evm_halt_flag`, `hi1`/`lo1`
  for `.dispatch_resume`). It is the byte image of the emitted tail; the
  codegen (`h_INVALID`, `tail := .custom (dispatchHaltRet 3)`) is left
  unchanged, and the `la` targets are carried as reconstruction hypotheses
  (`hla1`/`hla2`) in `InvalidSpec`, exactly as the guard/glue-track precedents
  (`GuardedHandlerSpecs`, `CalldataLoadGuardedHandlerSpec`) do.

  This is a direct clone of `StopProgram` (STOP → `dispatchHaltRet 1`),
  differing only in the routing code (3 vs 1). RETURN / REVERT /
  SELFDESTRUCT follow the same halt-triple shape.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64

/-- The verified `Program` image of `dispatchHaltRet 3` (the emitted INVALID
    tail): set `evm_halt_flag := 3`, point `x1` at `.dispatch_resume`, and
    `ret`. `hi2`/`lo2` are the `la evm_halt_flag` immediate pair; `hi1`/`lo1`
    the `la .dispatch_resume` pair. -/
def evm_invalid (hi2 : BitVec 20) (lo2 : BitVec 12) (hi1 : BitVec 20) (lo1 : BitVec 12) :
    Program :=
  [.LI .x5 3, .AUIPC .x6 hi2, .ADDI .x6 .x6 lo2, .SD .x6 .x5 0,
   .AUIPC .x1 hi1, .ADDI .x1 .x1 lo1, .JALR .x0 .x1 0]

/-- Byte fidelity: the emitted INVALID tail is exactly 7 instructions. -/
@[simp] theorem evm_invalid_length (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12) :
    (evm_invalid hi2 lo2 hi1 lo1).length = 7 := rfl

end EvmAsm.Evm64.Terminating
