/-
  EvmAsm.Rv64.SailEquiv.MemProofs

  Per-instruction equivalence theorems for memory instructions:
  LD, SD, LW, LWU, SW, LB, LH, LBU, LHU, SB, SH.

  These are the most challenging proofs due to the memory model gap:
  - Rv64 uses doubleword-addressed flat memory (Word → Word) with sub-word extraction
  - SAIL uses byte-addressed memory (Nat → BitVec 8) with virtual memory translation

  All proofs assume bare mode (Machine privilege, no address translation).
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
-- Doubleword loads/stores (LD/SD) — simplest memory operations
-- ============================================================================

/-- LD rd rs1 offset: 64-bit load agrees with SAIL's execute_LOAD (width=8). -/
theorem ld_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LD rd rs1 offset)
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 8) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- SD rs1 rs2 offset: 64-bit store agrees with SAIL's execute_STORE (width=8). -/
theorem sd_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.SD rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 8) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Word loads/stores (LW/LWU/SW)
-- ============================================================================

/-- LW rd rs1 offset: 32-bit signed load. -/
theorem lw_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LW rd rs1 offset)
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 4) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- LWU rd rs1 offset: 32-bit unsigned load. -/
theorem lwu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LWU rd rs1 offset)
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 4) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- SW rs1 rs2 offset: 32-bit store. -/
theorem sw_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.SW rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 4) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Byte loads/stores (LB/LBU/SB)
-- ============================================================================

/-- LB rd rs1 offset: signed byte load. -/
theorem lb_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LB rd rs1 offset)
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 1) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- LBU rd rs1 offset: unsigned byte load. -/
theorem lbu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LBU rd rs1 offset)
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 1) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- SB rs1 rs2 offset: byte store. -/
theorem sb_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.SB rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 1) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Halfword loads/stores (LH/LHU/SH)
-- ============================================================================

/-- LH rd rs1 offset: signed halfword load. -/
theorem lh_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LH rd rs1 offset)
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 2) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- LHU rd rs1 offset: unsigned halfword load. -/
theorem lhu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LHU rd rs1 offset)
    ∃ s_sail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 2) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- SH rs1 rs2 offset: halfword store. -/
theorem sh_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rs1 rs2 : Reg) (offset : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.SH rs1 rs2 offset)
    ∃ s_sail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 2) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
