/-
  EvmAsm.Evm64.Terminating.StopProgram

  The verified `Program` image of the `STOP` (0x00) handler tail.

  The runtime dispatcher emits STOP as `dispatchHaltRet 1`
  (`EvmAsm.Codegen.Dispatch`), whose assembler expansion is the seven
  RISC-V instructions

  ```
    li   x5, 1                 ; halt routing code (STOP → .exit_label)
    la   x6, evm_halt_flag     ; auipc x6, hi2 ; addi x6, x6, lo2
    sd   x5, 0(x6)             ; evm_halt_flag := 1
    la   x1, .dispatch_resume ; auipc x1, hi1 ; addi x1, x1, lo1
    ret                        ; jalr x0, x1, 0  (reaches resume &&& ~~~1)
  ```

  `evm_stop` is exactly that instruction list, parameterized by the two
  linker `la` immediate pairs (`hi2`/`lo2` for `evm_halt_flag`, `hi1`/`lo1`
  for `.dispatch_resume`). It is the byte image of the emitted tail; the
  codegen (`stopHandler`, `tail := .custom (dispatchHaltRet 1)`) is left
  unchanged, and the `la` targets are carried as reconstruction hypotheses
  (`hla1`/`hla2`) in `StopSpec`, exactly as the guard/glue-track precedents
  (`GuardedHandlerSpecs`, `CalldataLoadGuardedHandlerSpec`) do.

  This is the *first* terminating/halt opcode; INVALID / RETURN / REVERT /
  SELFDESTRUCT follow the same halt-triple shape (they differ only in the
  routing code and any pre-halt body).
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64

/-- The verified `Program` image of `dispatchHaltRet 1` (the emitted STOP
    tail): set `evm_halt_flag := 1`, point `x1` at `.dispatch_resume`, and
    `ret`. `hi2`/`lo2` are the `la evm_halt_flag` immediate pair; `hi1`/`lo1`
    the `la .dispatch_resume` pair. -/
def evm_stop (hi2 : BitVec 20) (lo2 : BitVec 12) (hi1 : BitVec 20) (lo1 : BitVec 12) :
    Program :=
  [.LI .x5 1, .AUIPC .x6 hi2, .ADDI .x6 .x6 lo2, .SD .x6 .x5 0,
   .AUIPC .x1 hi1, .ADDI .x1 .x1 lo1, .JALR .x0 .x1 0]

/-- Byte fidelity: the emitted STOP tail is exactly 7 instructions. -/
@[simp] theorem evm_stop_length (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12) :
    (evm_stop hi2 lo2 hi1 lo1).length = 7 := rfl

end EvmAsm.Evm64.Terminating
