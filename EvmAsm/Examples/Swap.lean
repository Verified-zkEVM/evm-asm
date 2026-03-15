/-
  EvmAsm.Examples.Swap

  A simple swap macro and its CPS-style Hoare triple specification.
-/

import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.ControlFlow
import EvmAsm.Rv32.InstructionSpecs
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.RunBlock

namespace EvmAsm.Examples

-- ============================================================================
-- Swap macro
-- ============================================================================

/-- Swap the values of two registers using a temporary register.
    swap rd rs tmp :=
      MV tmp, rd
      MV rd, rs
      MV rs, tmp
-/
def swap (rd rs tmp : Reg) : Program :=
  MV tmp rd ;;
  MV rd rs ;;
  MV rs tmp

/-- Test state for swap. -/
def swapTestState : MachineState where
  regs := fun r =>
    match r with
    | .x10 => 42
    | .x11 => 99
    | _    => 0
  mem := fun _ => 0
  pc := 0

/-- Swap correctness on concrete values: x10 gets the old value of x11. -/
example : (execProgram swapTestState (swap .x10 .x11 .x5)).getReg .x10 = 99 := by
  native_decide

/-- Swap correctness on concrete values: x11 gets the old value of x10. -/
example : (execProgram swapTestState (swap .x10 .x11 .x5)).getReg .x11 = 42 := by
  native_decide

-- ============================================================================
-- CPS-style Hoare triple for swap (symbolic proof, 3 steps)
-- ============================================================================

/-- Swap specification as a cpsTriple: 3 steps of MV instructions.

    Precondition: x10 holds v, x11 holds w, and x5 holds tmp.
    Postcondition: x10 holds w, x11 holds v, and x5 holds v.

    All three registers are in the precondition since the code writes to all of them.
    The frame R is preserved because it's disjoint from all owned registers. -/
theorem swap_cpsTriple (v w tmp : Word) (base : Addr) :
    cpsTriple base (base + 12)
      (CodeReq.singleton base (.MV .x5 .x10) |>.union
        (CodeReq.singleton (base + 4) (.MV .x10 .x11) |>.union
          (CodeReq.singleton (base + 8) (.MV .x11 .x5))))
      ((.x10 ↦ᵣ v) ** (.x11 ↦ᵣ w) ** (.x5 ↦ᵣ tmp))
      ((.x10 ↦ᵣ w) ** (.x11 ↦ᵣ v) ** (.x5 ↦ᵣ v)) := by
  have S0 := mv_spec .x5 .x10 v tmp base (by nofun)
  have S1 := mv_spec .x10 .x11 w v (base + 4) (by nofun)
  have S2 := mv_spec .x11 .x5 v w (base + 8) (by nofun)
  runBlock S0 S1 S2

end EvmAsm.Examples
