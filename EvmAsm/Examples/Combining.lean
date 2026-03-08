/-
  EvmAsm.Examples.Combining

  Combining macros: double and triple.
-/

import EvmAsm.Rv32.Program

namespace EvmAsm.Examples

-- ============================================================================
-- Combining macros
-- ============================================================================

/-- Double a value: rd := rs * 2. This is just a single left shift. -/
def double (rd rs : Reg) : Program :=
  SLLI rd rs 1

/-- Triple a value: rd := rs * 3 = rs + rs * 2.
    We move rs to rd, then shift rs, then add. -/
def triple (rd rs tmp : Reg) : Program :=
  MV rd rs ;;       -- rd := rs
  SLLI tmp rs 1 ;;  -- tmp := rs * 2
  ADD rd rd tmp     -- rd := rs + rs * 2 = rs * 3

def tripleTestState : MachineState where
  regs := fun r =>
    match r with
    | .x11 => 15
    | _    => 0
  mem := fun _ => 0
  pc := 0

example : (execProgram tripleTestState (triple .x10 .x11 .x5)).getReg .x10 = 45 := by
  native_decide

end EvmAsm.Examples
