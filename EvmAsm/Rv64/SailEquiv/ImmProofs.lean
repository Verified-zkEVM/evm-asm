/-
  EvmAsm.Rv64.SailEquiv.ImmProofs

  Per-instruction equivalence theorems for ALU immediate and comparison instructions:
  ADDI, ANDI, ORI, XORI, SLTI, SLTIU, SLT, SLTU.
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
-- Immediate ALU
-- ============================================================================

theorem addi_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.ADDI rd rs1 imm)
    ∃ s_sail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.ADDI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem andi_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.ANDI rd rs1 imm)
    ∃ s_sail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.ANDI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem ori_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.ORI rd rs1 imm)
    ∃ s_sail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.ORI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem xori_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.XORI rd rs1 imm)
    ∃ s_sail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.XORI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Comparison register-register
-- ============================================================================

theorem slt_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.SLT rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLT) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem sltu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    let s_rv' := execInstrBr s_rv (.SLTU rd rs1 rs2)
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLTU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Comparison immediate
-- ============================================================================

theorem slti_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.SLTI rd rs1 imm)
    ∃ s_sail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.SLTI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

theorem sltiu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.SLTIU rd rs1 imm)
    ∃ s_sail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.SLTIU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
