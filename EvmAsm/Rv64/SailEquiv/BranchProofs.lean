/-
  EvmAsm.Rv64.SailEquiv.BranchProofs

  Per-instruction equivalence theorems for branch and jump instructions:
  BEQ, BNE, BLT, BGE, BLTU, BGEU, JAL, JALR.

  Note: Branch instructions don't write registers (except JAL/JALR link register).
  The key challenge is relating PC update semantics between the two models.
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
-- Conditional branches
-- ============================================================================

/-- BEQ rs1 rs2 offset: branch if equal. -/
theorem beq_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 13) :
    let s_rv' := execInstrBr s_rv (.BEQ rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BEQ) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- BNE rs1 rs2 offset: branch if not equal. -/
theorem bne_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 13) :
    let s_rv' := execInstrBr s_rv (.BNE rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BNE) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- BLT rs1 rs2 offset: branch if less than (signed). -/
theorem blt_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 13) :
    let s_rv' := execInstrBr s_rv (.BLT rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLT) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- BGE rs1 rs2 offset: branch if greater or equal (signed). -/
theorem bge_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 13) :
    let s_rv' := execInstrBr s_rv (.BGE rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGE) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- BLTU rs1 rs2 offset: branch if less than (unsigned). -/
theorem bltu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 13) :
    let s_rv' := execInstrBr s_rv (.BLTU rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLTU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- BGEU rs1 rs2 offset: branch if greater or equal (unsigned). -/
theorem bgeu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 13) :
    let s_rv' := execInstrBr s_rv (.BGEU rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGEU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Unconditional jumps
-- ============================================================================

/-- JAL rd offset: jump and link. -/
theorem jal_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd : Reg) (offset : BitVec 21) :
    let s_rv' := execInstrBr s_rv (.JAL rd offset)
    ∃ s_sail',
      runSail (execute_JAL offset (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- JALR rd rs1 offset: jump and link register.
    Key lemma needed: jalr_mask_equiv (bit-0 masking agreement). -/
theorem jalr_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.JALR rd rs1 offset)
    ∃ s_sail',
      runSail (execute_JALR offset (regToRegidx rs1) (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
