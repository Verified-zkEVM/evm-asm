/-
  EvmAsm.Rv64.SailEquiv.MExtProofs

  Per-instruction equivalence theorems for M-extension instructions:
  MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.InstrMap
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.HelperEquiv

open LeanRV64D.Functions
open LeanRV64D.Defs

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Multiply
-- ============================================================================

/-- MUL: lower 64 bits of rs1 * rs2. -/
theorem mul_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.MUL rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := Low, signed_rs1 := Signed, signed_rs2 := Signed }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- MULH: upper 64 bits of signed × signed. -/
theorem mulh_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.MULH rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := High, signed_rs1 := Signed, signed_rs2 := Signed }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- MULHSU: upper 64 bits of signed × unsigned. -/
theorem mulhsu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.MULHSU rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := High, signed_rs1 := Signed, signed_rs2 := Unsigned }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- MULHU: upper 64 bits of unsigned × unsigned. -/
theorem mulhu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.MULHU rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := High, signed_rs1 := Unsigned, signed_rs2 := Unsigned }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Division
-- ============================================================================

/-- DIV: signed division. -/
theorem div_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.DIV rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_DIV (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) false) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- DIVU: unsigned division. -/
theorem divu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.DIVU rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_DIV (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) true) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Remainder
-- ============================================================================

/-- REM: signed remainder. -/
theorem rem_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.REM rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_REM (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) false) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- REMU: unsigned remainder. -/
theorem remu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.REMU rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_REM (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) true) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
