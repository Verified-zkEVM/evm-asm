/-
  EvmAsm.Examples.FullPipeline

  Full pipeline: WRITE + COMMIT + HALT.
-/

import EvmAsm.Rv32.Execution

namespace EvmAsm.Examples

-- ============================================================================
-- Full pipeline — WRITE + COMMIT + HALT
-- ============================================================================

/-- Store a word, WRITE to public values, COMMIT a digest word, then HALT. -/
def full_pipeline : Program :=
  LI .x6 42 ;;
  LI .x7 0x100 ;;
  SW .x7 .x6 0 ;;          -- mem[0x100] := 42
  WRITE 13 0x100 4 ;;      -- publicValues gets [42]
  COMMIT 0 0xDEAD ;;       -- committed gets [(0, 0xDEAD)]
  HALT 0

def full_pipeline_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After running full_pipeline, publicValues = [0x2A, 0, 0, 0] (42 as LE bytes). -/
example : let steps := full_pipeline.length - 1
          let s0 := { full_pipeline_state with code := loadProgram 0 full_pipeline }
          (stepN steps s0).bind (fun s =>
            some s.publicValues) = some [0x2A, 0, 0, 0] := by
  native_decide

/-- After running full_pipeline, committed = [(0, 0xDEAD)]. -/
example : let steps := full_pipeline.length - 1
          let s0 := { full_pipeline_state with code := loadProgram 0 full_pipeline }
          (stepN steps s0).bind (fun s =>
            some s.committed) = some [(0, 0xDEAD)] := by
  native_decide

/-!
  ## The Macro Assembler Pattern

  The key idea from Kennedy et al. is:

  1. **Instructions** are data: they are an inductive type in Lean.
  2. **Programs** are lists of instructions with sequential composition (;;).
  3. **Macros** are Lean functions that produce programs. They can use
     all of Lean's facilities: recursion, pattern matching, conditionals.
  4. **Specifications** are Hoare triples using separation logic.
  5. **Proofs** verify that macros meet their specifications.

  Lean serves as both the macro language and the verification language.
  The `add_mulc` example shows a recursive macro that compiles a
  multiply-by-constant into a sequence of shifts and adds, with concrete
  correctness verified by `native_decide` and a general specification
  stated using Hoare triples and separating conjunction.
-/

end EvmAsm.Examples
