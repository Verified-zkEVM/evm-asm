/-
  EvmAsm.Rv64.Tactics.SymStep

  Symbolic-simulation prototype tactic — slice 2 of GH #302 / beads
  `evm-asm-avjm`.

  `sym_step h` rewrites a goal of shape `step s = ?` (or a goal containing
  such a sub-term) using the canonical fetch hypothesis
  `h : s.code s.pc = some i` for a *non-branch / non-memory / non-ECALL /
  non-EBREAK* RV64IM instruction `i`. The rewrite uses
  `EvmAsm.Rv64.step_non_ecall_non_mem` and then unfolds `execInstrBr`,
  producing an explicit `(s.setReg … …).setPC (s.pc + 4)`-style record
  update.

  ## Scope (slice 2)

  This is a *prototype* aimed at the four smoke-test instruction classes
  required by the acceptance criteria of beads `evm-asm-avjm`:
  `ADDI`, `ADD`, `LUI`, `SLLI`. All four route through the
  `step_non_ecall_non_mem` non-memory path, so a single macro covers them.

  Memory instructions (LD/SD/LW/…) and branches (BEQ/BNE/JAL/…) need
  separate per-class macros that supply the validity hypothesis or the
  branch-condition decision; those are deferred to a follow-up slice
  (see GH #302).

  ## Usage

  ```lean
  example (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12)
      (h : s.code s.pc = some (.ADDI rd rs1 imm)) :
      step s = some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) := by
    sym_step h
  ```

  ## Failure modes

  - If `i` is a branch / memory / ECALL / EBREAK instruction, the
    `decide`-discharged side conditions of `step_non_ecall_non_mem` will
    fail; use the dedicated `step_*` lemmas in `EvmAsm/Rv64/Execution.lean`
    directly instead.
  - If the goal does not match `step s = ?`, the underlying `rw` will
    fail with the usual error message.

  ## References

  - GH issue #302 ("LNSym-style symbolic simulation on partial state").
  - `EvmAsm/Rv64/Execution.lean` — `step`, `execInstrBr`,
    `step_non_ecall_non_mem`, and the per-instruction `step_*` lemmas.
-/

module

public import Lean
public import EvmAsm.Rv64.Execution
meta import Lean
meta import EvmAsm.Rv64.Execution

@[expose] public section

namespace EvmAsm.Rv64.Tactics

open Lean Elab Tactic

/-- `sym_step h` simulates a single RV64IM step from the fetch hypothesis
    `h : s.code s.pc = some i` for non-branch / non-memory / non-ECALL /
    non-EBREAK instructions, then unfolds `execInstrBr` so the result is
    an explicit record-update form.

    Typical use: smoke-test ADDI/ADD/LUI/SLLI sequences. See module
    docstring (and GH #302) for the broader plan. -/
syntax (name := symStepTac) "sym_step " ident : tactic

macro_rules
  | `(tactic| sym_step $h:ident) =>
    `(tactic|
      first
      | (rw [EvmAsm.Rv64.step_non_ecall_non_mem $h
              (by intro hEq; cases hEq)
              (by intro hEq; cases hEq)
              (by simp [EvmAsm.Rv64.Instr.isMemAccess])]
         simp only [EvmAsm.Rv64.execInstrBr])
      | (simp only [EvmAsm.Rv64.step_non_ecall_non_mem $h
                      (by intro hEq; cases hEq)
                      (by intro hEq; cases hEq)
                      (by simp [EvmAsm.Rv64.Instr.isMemAccess]),
                    EvmAsm.Rv64.execInstrBr]))

end EvmAsm.Rv64.Tactics

-- ---------------------------------------------------------------------------
-- Smoke tests
-- ---------------------------------------------------------------------------
-- Acceptance from beads `evm-asm-avjm`:
--   "works on ADDI, ADD, LUI, SLLI as smoke tests; lake build green; no
--    behavioral change to existing proofs."
-- ---------------------------------------------------------------------------

namespace EvmAsm.Rv64.Tactics.SymStepTests

open EvmAsm.Rv64

-- (a) ADDI: register-immediate add.
example {s : MachineState} {rd rs1 : Reg} {imm : BitVec 12}
    (h : s.code s.pc = some (.ADDI rd rs1 imm)) :
    step s =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) := by
  sym_step h

-- (b) ADD: register-register add.
example {s : MachineState} {rd rs1 rs2 : Reg}
    (h : s.code s.pc = some (.ADD rd rs1 rs2)) :
    step s =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) := by
  sym_step h

-- (c) LUI: 32-bit upper-immediate, sign-extended to 64 bits.
example {s : MachineState} {rd : Reg} {imm : BitVec 20}
    (h : s.code s.pc = some (.LUI rd imm)) :
    step s =
      some ((s.setReg rd
              (((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64)).setPC
            (s.pc + 4)) := by
  sym_step h

-- (d) SLLI: shift-left logical immediate.
example {s : MachineState} {rd rs1 : Reg} {shamt : BitVec 6}
    (h : s.code s.pc = some (.SLLI rd rs1 shamt)) :
    step s =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) := by
  sym_step h

end EvmAsm.Rv64.Tactics.SymStepTests
