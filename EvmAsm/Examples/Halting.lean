/-
  EvmAsm.Examples.Halting

  ECALL-based halting (SP1 convention).
-/

import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.MulMacro

namespace EvmAsm.Examples

-- ============================================================================
-- ECALL-based halting (SP1 convention)
-- ============================================================================

/-- A program that computes 6 * 7 and halts with the result as exit code. -/
def mul_and_halt : Program :=
  LI .x10 0 ;;
  LI .x11 6 ;;
  add_mulc 8 .x10 .x11 7 ;;
  LI .x5 0 ;;     -- t0 := HALT
  single .ECALL

def mul_and_halt_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After running all instructions before ECALL, the next step halts. -/
example : let steps := mul_and_halt.length - 1  -- run up to ECALL
          let s0 := { mul_and_halt_state with code := loadProgram 0 mul_and_halt }
          (stepN steps s0).bind (fun s =>
            step s) = none := by
  native_decide

/-- After running all instructions before ECALL, a0 (x10) contains 42. -/
example : let steps := mul_and_halt.length - 1
          let s0 := { mul_and_halt_state with code := loadProgram 0 mul_and_halt }
          (stepN steps s0).bind (fun s =>
            some (s.getReg .x10)) = some 42 := by
  native_decide

/-- A simple program that halts immediately with exit code 0. -/
def halt_zero : Program := HALT 0

/-- halt_zero terminates in 3 steps (LI x5, LI x10, ECALL),
    and the next step returns none. -/
example : let s0 := { mul_and_halt_state with code := loadProgram 0 halt_zero }
          (stepN 2 s0).bind (fun s => step s) = none := by
  native_decide

end EvmAsm.Examples
