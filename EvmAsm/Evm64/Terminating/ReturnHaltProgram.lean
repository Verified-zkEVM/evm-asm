/-
  EvmAsm.Evm64.Terminating.ReturnHaltProgram

  The verified `Program` image of the *halt core* shared by the `RETURN`
  (0xf3) and `REVERT` (0xfd) handler tails.

  Both terminating opcodes finish their return-data descriptor setup by
  emitting `dispatchHaltRet 2` (`EvmAsm.Codegen.Dispatch`), whose assembler
  expansion is the seven RISC-V instructions

  ```
    li   x5, 2                 ; halt routing code (RETURN/REVERT → .exit_no_epilogue)
    la   x6, evm_halt_flag     ; auipc x6, hi2 ; addi x6, x6, lo2
    sd   x5, 0(x6)             ; evm_halt_flag := 2
    la   x1, .dispatch_resume ; auipc x1, hi1 ; addi x1, x1, lo1
    ret                        ; jalr x0, x1, 0  (reaches resume &&& ~~~1)
  ```

  `evm_return_halt` is exactly that instruction list, parameterized by the two
  linker `la` immediate pairs (`hi2`/`lo2` for `evm_halt_flag`, `hi1`/`lo1`
  for `.dispatch_resume`). It is the byte image of the emitted `dispatchHaltRet
  2` sub-slice at the tail of the RETURN/REVERT handlers; the codegen is left
  unchanged, and the `la` targets are carried as reconstruction hypotheses
  (`hla1`/`hla2`) in `ReturnHaltSpec`, exactly as the guard/glue-track
  precedents (`GuardedHandlerSpecs`, `CalldataLoadGuardedHandlerSpec`) do.

  This is a direct clone of `StopProgram` (STOP → `dispatchHaltRet 1`) and
  `InvalidProgram` (INVALID → `dispatchHaltRet 3`), differing only in the
  routing code (2 vs 1 / 3). It is the *shared halt-routing core* of the
  RETURN/REVERT family; the substantive return-data descriptor window that
  precedes it in the emitted tail (`returnRevertTail`) is NOT modeled here —
  see `ReturnHaltSpec` for the coverage boundary.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64

/-- The verified `Program` image of `dispatchHaltRet 2` (the emitted RETURN /
    REVERT halt core): set `evm_halt_flag := 2`, point `x1` at
    `.dispatch_resume`, and `ret`. `hi2`/`lo2` are the `la evm_halt_flag`
    immediate pair; `hi1`/`lo1` the `la .dispatch_resume` pair. -/
def evm_return_halt (hi2 : BitVec 20) (lo2 : BitVec 12) (hi1 : BitVec 20) (lo1 : BitVec 12) :
    Program :=
  [.LI .x5 2, .AUIPC .x6 hi2, .ADDI .x6 .x6 lo2, .SD .x6 .x5 0,
   .AUIPC .x1 hi1, .ADDI .x1 .x1 lo1, .JALR .x0 .x1 0]

/-- Byte fidelity: the emitted `dispatchHaltRet 2` halt core is exactly 7
    instructions. -/
@[simp] theorem evm_return_halt_length (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12) :
    (evm_return_halt hi2 lo2 hi1 lo1).length = 7 := rfl

end EvmAsm.Evm64.Terminating
