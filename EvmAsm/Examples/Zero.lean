/-
  EvmAsm.Examples.Zero

  A zero-register macro and a CPS-style Hoare triple.
-/

import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.ControlFlow
import EvmAsm.Rv32.InstructionSpecs

namespace EvmAsm.Examples

-- ============================================================================
-- Zero a register
-- ============================================================================

/-- Zero a register: rd := 0. Uses SUB rd, rd, rd. -/
def zero (rd : Reg) : Program :=
  SUB rd rd rd

def zeroTestState : MachineState where
  regs := fun r =>
    match r with
    | .x10 => 12345
    | _    => 0
  mem := fun _ => 0
  pc := 0

example : (execProgram zeroTestState (zero .x10)).getReg .x10 = 0 := by
  native_decide

-- ============================================================================
-- CPS-style Hoare triple for zero
-- ============================================================================

/-- CPS-style specification: zeroing a register in one step.
    Requires instrAt for the SUB instruction at the base address. -/
theorem zero_cpsTriple (rd : Reg) (v : Word) (hrd : rd ≠ .x0) (base : Addr) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .SUB rd rd rd) ** (rd ↦ᵣ v))
      ((base ↦ᵢ .SUB rd rd rd) ** (rd ↦ᵣ 0)) := by
  have h := sub_spec_all_same rd v base hrd
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hq => by simp only [BitVec.sub_self] at hq; exact hq)
    h

end EvmAsm.Examples
