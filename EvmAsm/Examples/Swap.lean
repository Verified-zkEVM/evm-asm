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
      ((base ↦ᵢ .MV .x5 .x10) ** ((base + 4) ↦ᵢ .MV .x10 .x11) **
       ((base + 8) ↦ᵢ .MV .x11 .x5) **
       (.x10 ↦ᵣ v) ** (.x11 ↦ᵣ w) ** (.x5 ↦ᵣ tmp))
      ((base ↦ᵢ .MV .x5 .x10) ** ((base + 4) ↦ᵢ .MV .x10 .x11) **
       ((base + 8) ↦ᵢ .MV .x11 .x5) **
       (.x10 ↦ᵣ w) ** (.x11 ↦ᵣ v) ** (.x5 ↦ᵣ v)) := by
  -- Step 1: MV x5 x10 at base (x5 := v)
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .MV .x10 .x11) ** ((base + 8) ↦ᵢ .MV .x11 .x5) ** (.x11 ↦ᵣ w))
    (by pcFree) (mv_spec .x5 .x10 v tmp base (by nofun))
  -- Step 2: MV x10 x11 at base+4 (x10 := w)
  have s2_raw := mv_spec .x10 .x11 w v (base + 4) (by nofun)
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .MV .x5 .x10) ** ((base + 8) ↦ᵢ .MV .x11 .x5) ** (.x5 ↦ᵣ v))
    (by pcFree) s2_raw
  -- Step 3: MV x11 x5 at base+8 (x11 := v)
  have s3_raw := mv_spec .x11 .x5 v w (base + 8) (by nofun)
  rw [show (base + 8 : Addr) + 4 = base + 12 from by bv_omega] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .MV .x5 .x10) ** ((base + 4) ↦ᵢ .MV .x10 .x11) ** (.x10 ↦ᵣ w))
    (by pcFree) s3_raw
  -- Compose all 3 steps
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_seq_with_perm _ _ _ _ _ _ _
        (fun _ hp => by xperm_hyp hp) s1 s2)
      s3)

end EvmAsm.Examples
