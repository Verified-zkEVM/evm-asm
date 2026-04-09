/-
  EvmAsm.Rv64.SailEquiv.BranchProofs

  Per-instruction equivalence theorems for branch and jump instructions:
  BEQ, BNE, BLT, BGE, BLTU, BGEU, JAL, JALR.

  Branches don't write registers — they only update PC. Since StateRel
  doesn't track PC (SAIL writes nextPC, Rv64 writes pc), branches
  trivially preserve StateRel for registers and memory.

  JAL/JALR additionally write a link register (rd := PC + 4).
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

set_option maxHeartbeats 1600000

-- ============================================================================
-- Conditional branches (BEQ, BNE, BLT, BGE, BLTU, BGEU)
-- ============================================================================

theorem beq_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rs1 rs2 : Reg) (offset : BitVec 13) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BEQ) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BEQ rs1 rs2 offset)) s_sail' := by
  sorry

theorem bne_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rs1 rs2 : Reg) (offset : BitVec 13) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BNE) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BNE rs1 rs2 offset)) s_sail' := by
  sorry

theorem blt_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rs1 rs2 : Reg) (offset : BitVec 13) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLT) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BLT rs1 rs2 offset)) s_sail' := by
  sorry

theorem bge_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rs1 rs2 : Reg) (offset : BitVec 13) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGE) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BGE rs1 rs2 offset)) s_sail' := by
  sorry

theorem bltu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rs1 rs2 : Reg) (offset : BitVec 13) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLTU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BLTU rs1 rs2 offset)) s_sail' := by
  sorry

theorem bgeu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rs1 rs2 : Reg) (offset : BitVec 13) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGEU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BGEU rs1 rs2 offset)) s_sail' := by
  sorry

-- ============================================================================
-- Unconditional jumps (JAL, JALR)
-- ============================================================================

theorem jal_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rd : Reg) (offset : BitVec 21) :
    ∃ s_sail',
      runSail (execute_JAL offset (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.JAL rd offset)) s_sail' := by
  sorry

theorem jalr_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_JALR offset (regToRegidx rs1) (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.JALR rd rs1 offset)) s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
