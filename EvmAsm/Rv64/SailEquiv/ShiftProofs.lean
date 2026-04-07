/-
  EvmAsm.Rv64.SailEquiv.ShiftProofs

  Per-instruction equivalence theorems for shift instructions:
  SLL, SRL, SRA (register), SLLI, SRLI, SRAI (immediate).
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
-- Register shifts
-- ============================================================================

theorem sll_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.SLL rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLL) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem srl_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.SRL rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SRL) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem sra_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.SRA rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SRA) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Immediate shifts
-- ============================================================================

theorem slli_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    let s_rv' := execInstrBr s_rv (.SLLI rd rs1 shamt)
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SLLI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem srli_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    let s_rv' := execInstrBr s_rv (.SRLI rd rs1 shamt)
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SRLI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem srai_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    let s_rv' := execInstrBr s_rv (.SRAI rd rs1 shamt)
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SRAI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
