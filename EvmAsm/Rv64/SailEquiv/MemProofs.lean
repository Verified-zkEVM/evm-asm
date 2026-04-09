/-
  EvmAsm.Rv64.SailEquiv.MemProofs

  Per-instruction equivalence theorems for memory instructions:
  LD, SD, LW, LWU, SW, LB, LH, LBU, LHU, SB, SH.

  These are the most challenging proofs — require bridging:
  - SAIL's byte-addressed memory (ExtHashMap Nat (BitVec 8)) with virtual
    memory translation (vmem_read/vmem_write)
  - Rv64's doubleword-addressed flat memory (Word → Word) with sub-word
    extraction helpers (extractByte, replaceByte, etc.)

  All proofs assume bare mode (Machine privilege, satp=0, no MMU).
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
-- Doubleword loads/stores (LD/SD)
-- ============================================================================

theorem ld_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 8) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LD rd rs1 offset)) s_sail' := by
  sorry

theorem sd_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 8) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SD rs1 rs2 offset)) s_sail' := by
  sorry

-- ============================================================================
-- Word loads/stores (LW/LWU/SW)
-- ============================================================================

theorem lw_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 4) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LW rd rs1 offset)) s_sail' := by
  sorry

theorem lwu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 4) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LWU rd rs1 offset)) s_sail' := by
  sorry

theorem sw_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 4) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SW rs1 rs2 offset)) s_sail' := by
  sorry

-- ============================================================================
-- Byte loads/stores (LB/LBU/SB)
-- ============================================================================

theorem lb_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 1) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LB rd rs1 offset)) s_sail' := by
  sorry

theorem lbu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 1) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LBU rd rs1 offset)) s_sail' := by
  sorry

theorem sb_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 1) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SB rs1 rs2 offset)) s_sail' := by
  sorry

-- ============================================================================
-- Halfword loads/stores (LH/LHU/SH)
-- ============================================================================

theorem lh_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 2) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LH rd rs1 offset)) s_sail' := by
  sorry

theorem lhu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 2) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.LHU rd rs1 offset)) s_sail' := by
  sorry

theorem sh_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 2) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SH rs1 rs2 offset)) s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
