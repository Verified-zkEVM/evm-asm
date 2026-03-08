/-
  EvmAsm.Examples.Multiply

  Multiply by constant using the add_mulc recursive macro.
-/

import EvmAsm.Rv32.MulMacro
import EvmAsm.Examples.Zero

namespace EvmAsm.Examples

-- ============================================================================
-- Multiply by constant (from MulMacro)
-- ============================================================================

/-- Multiply x11 by 7, storing the result in x10.
    We first zero x10, then use add_mulc. -/
def mul7 (rd rs : Reg) : Program :=
  zero rd ;;
  add_mulc 8 rd rs 7

def mul7TestState : MachineState where
  regs := fun r =>
    match r with
    | .x11 => 6
    | _    => 0
  mem := fun _ => 0
  pc := 0

/-- 6 * 7 = 42 -/
example : (execProgram mul7TestState (mul7 .x10 .x11)).getReg .x10 = 42 := by
  native_decide

/-- 13 * 7 = 91 -/
def mul7TestState2 : MachineState where
  regs := fun r =>
    match r with
    | .x11 => 13
    | _    => 0
  mem := fun _ => 0
  pc := 0

example : (execProgram mul7TestState2 (mul7 .x10 .x11)).getReg .x10 = 91 := by
  native_decide

end EvmAsm.Examples
