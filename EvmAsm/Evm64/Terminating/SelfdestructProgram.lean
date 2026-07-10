/-
  EvmAsm.Evm64.Terminating.SelfdestructProgram

  The verified `Program` image of the `SELFDESTRUCT` (0xff) handler's halt tail.

  The runtime dispatcher's `h_SELFDESTRUCT` handler ends in `dispatchHaltRet 4`
  (`EvmAsm.Codegen.Dispatch`; routing code 4 → `.exit_selfdestruct`), whose
  assembler expansion is the same seven RISC-V instructions as STOP's tail, with
  the routing code `4` in place of `1`:

  ```
    li   x5, 4                 ; halt routing code (SELFDESTRUCT → .exit_selfdestruct)
    la   x6, evm_halt_flag     ; auipc x6, hi2 ; addi x6, x6, lo2
    sd   x5, 0(x6)             ; evm_halt_flag := 4
    la   x1, .Ldispatch_resume ; auipc x1, hi1 ; addi x1, x1, lo1
    ret                        ; jalr x0, x1, 0  (reaches resume &&& ~~~1)
  ```

  `evm_selfdestruct` is exactly that instruction list (the direct STOP clone with
  routing code 4). It sits at `hbase` = the `dispatchHaltRet 4` entry, i.e. AFTER
  the handler's effects body (cold-access charge, EIP-6780 detection, balance
  transfer to the beneficiary, EIP-7708 log). That effects body is unverified
  glue (documented in DRIFT); this program + spec prove only the halt/routing
  behavior, exactly as STOP/INVALID do (STOP has no effect either). A future phase
  can prove the balance-transfer effects (`EL/SelfdestructEffects.lean`).
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64

/-- The verified `Program` image of `dispatchHaltRet 4` (the emitted SELFDESTRUCT
    halt tail): set `evm_halt_flag := 4`, point `x1` at `.Ldispatch_resume`, and
    `ret`. `hi2`/`lo2` are the `la evm_halt_flag` immediate pair; `hi1`/`lo1` the
    `la .Ldispatch_resume` pair. Direct STOP clone with routing code 4. -/
def evm_selfdestruct (hi2 : BitVec 20) (lo2 : BitVec 12) (hi1 : BitVec 20) (lo1 : BitVec 12) :
    Program :=
  [.LI .x5 4, .AUIPC .x6 hi2, .ADDI .x6 .x6 lo2, .SD .x6 .x5 0,
   .AUIPC .x1 hi1, .ADDI .x1 .x1 lo1, .JALR .x0 .x1 0]

/-- Byte fidelity: the emitted SELFDESTRUCT halt tail is exactly 7 instructions. -/
@[simp] theorem evm_selfdestruct_length (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12) :
    (evm_selfdestruct hi2 lo2 hi1 lo1).length = 7 := rfl

end EvmAsm.Evm64.Terminating
