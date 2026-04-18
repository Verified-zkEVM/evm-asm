/-
  EvmAsm.Rv64.RegOps

  `reg_ops` grindset for `MachineState` projection lemmas (GRIND.md Phase 5).

  The lemmas live in `Basic.lean` already tagged `@[simp]`; this file registers
  them *additionally* in the `reg_ops` named simp set and the `grind`
  equational index, then exposes a one-line tactic macro.

  GRIND.md identifies this phase as the **lowest-risk** in the roadmap:
  augmenting already-`@[simp]` lemmas with `@[grind =]` cannot break existing
  `simp`-based proofs — nothing is removed from the default simp set, nothing
  is reshaped. Downstream modules opt in to `by reg_ops` where it wins; the
  legacy `simp [..]` closers continue to work unchanged.

  Included lemmas: the *projection* family — reading one field after
  writing another:
    * `pc_set<Field>`               (5 lemmas)
    * `code_set<Field>` / `code_append*`       (8 lemmas)
    * `getReg_setPC` / `getReg_append*`        (3 lemmas)
    * `getMem_setMem_eq` / `getMem_setMem_ne`  (2 lemmas)
    * `getMem_setReg` / `getMem_setPC`         (2 lemmas)
    * `getMem_append*`                         (2 lemmas)
    * `pc_append*`                             (2 lemmas)
    * `committed_set<Field>` / `committed_append<Public>` (6 lemmas)
    * `publicValues_set<Field>` / `publicValues_appendCommit` (6 lemmas)
    * `privateInput_set<Field>` / `privateInput_append<Commit/Public>` (7 lemmas)

  Deliberately *excluded*: the inductive `*_writeWords` / `*_writeBytesAsWords`
  family. Those unfold via induction on the list argument and are liable to
  loop `grind`'s equational index on open-ended lists. They remain `@[simp]`
  in `Basic.lean` so existing `simp` closers keep working.
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.RegOpsAttr

namespace EvmAsm.Rv64

-- ============================================================================
-- pc_set<Field>
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.pc_setReg
  MachineState.pc_setMem
  MachineState.pc_setByte
  MachineState.pc_setHalfword
  MachineState.pc_setWord32

-- ============================================================================
-- code_set<Field> / code_append*
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.code_setReg
  MachineState.code_setMem
  MachineState.code_setPC
  MachineState.code_setByte
  MachineState.code_setHalfword
  MachineState.code_setWord32
  MachineState.code_appendCommit
  MachineState.code_appendPublicValues

-- ============================================================================
-- getReg_* (read register after writing another field)
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.getReg_setPC
  MachineState.getReg_appendCommit
  MachineState.getReg_appendPublicValues

-- ============================================================================
-- getMem_* (read memory after writing another field)
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.getMem_setMem_eq
  MachineState.getMem_setMem_ne
  MachineState.getMem_setReg
  MachineState.getMem_setPC
  MachineState.getMem_appendCommit
  MachineState.getMem_appendPublicValues

-- ============================================================================
-- pc_append*
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.pc_appendCommit
  MachineState.pc_appendPublicValues

-- ============================================================================
-- committed_*
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.committed_setReg
  MachineState.committed_setMem
  MachineState.committed_setByte
  MachineState.committed_setHalfword
  MachineState.committed_setPC
  MachineState.committed_appendCommit
  MachineState.committed_appendPublicValues

-- ============================================================================
-- publicValues_*
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.publicValues_setReg
  MachineState.publicValues_setMem
  MachineState.publicValues_setByte
  MachineState.publicValues_setHalfword
  MachineState.publicValues_setPC
  MachineState.publicValues_appendCommit
  MachineState.publicValues_appendPublicValues

-- ============================================================================
-- privateInput_*
-- ============================================================================

attribute [reg_ops, grind =]
  MachineState.privateInput_setReg
  MachineState.privateInput_setMem
  MachineState.privateInput_setByte
  MachineState.privateInput_setHalfword
  MachineState.privateInput_setPC
  MachineState.privateInput_appendCommit
  MachineState.privateInput_appendPublicValues

-- ============================================================================
-- `reg_ops` tactic
--
-- Primary: `grind` (sees every `@[grind =]`-registered projection lemma and
-- closes multi-step projection chains including those with side-condition
-- hypotheses like `getMem_setMem_ne`).
-- Fallback: `simp only [reg_ops]` (matches hand-written closer shapes).
-- ============================================================================

/-- Close a `MachineState` projection-chain goal (register / memory / PC /
    code / committed / publicValues / privateInput reads after field writes).
    Tries `grind` first; falls back to `simp only [reg_ops]` for edge shapes. -/
macro "reg_ops" : tactic =>
  `(tactic| first
    | grind
    | simp only [reg_ops])

end EvmAsm.Rv64

-- ============================================================================
-- Sanity: the tactic closes a short projection chain.
-- ============================================================================

section Sanity
open EvmAsm.Rv64

example (s : MachineState) (r : Reg) (v : Word) :
    ((s.setReg r v).setReg r v).pc = s.pc := by reg_ops

example (s : MachineState) (a : Word) (v : Word) (r : Reg) :
    ((s.setMem a v).setReg r v).getMem a = v := by reg_ops

example (s : MachineState) (a : Word) (b : List (BitVec 8)) (v : Word)
    (r : Reg) :
    ((s.appendPublicValues b).setReg r v).getMem a = s.getMem a := by reg_ops
end Sanity
