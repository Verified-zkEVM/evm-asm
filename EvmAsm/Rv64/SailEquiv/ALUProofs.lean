/-
  EvmAsm.Rv64.SailEquiv.ALUProofs

  Per-instruction equivalence theorems for ALU register-register instructions:
  ADD, SUB, AND, OR, XOR.

  These are the simplest proofs since both models use identical BitVec operators.
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
-- ADD
-- ============================================================================

/-- ADD rd rs1 rs2: execInstrBr agrees with SAIL's execute_RTYPE ... rop.ADD. -/
theorem add_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.ADD rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.ADD) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- SUB
-- ============================================================================

/-- SUB rd rs1 rs2: execInstrBr agrees with SAIL's execute_RTYPE ... rop.SUB. -/
theorem sub_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.SUB rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SUB) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- AND
-- ============================================================================

/-- AND rd rs1 rs2: execInstrBr agrees with SAIL's execute_RTYPE ... rop.AND. -/
theorem and_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.AND rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.AND) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- OR
-- ============================================================================

/-- OR rd rs1 rs2: execInstrBr agrees with SAIL's execute_RTYPE ... rop.OR. -/
theorem or_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.OR rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.OR) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- XOR
-- ============================================================================

/-- XOR rd rs1 rs2: execInstrBr agrees with SAIL's execute_RTYPE ... rop.XOR. -/
theorem xor_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.XOR rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.XOR) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
