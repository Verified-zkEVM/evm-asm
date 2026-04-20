/-
  EvmAsm.Rv64.SailEquiv.MemProofs

  Per-instruction equivalence theorems for memory instructions:
  LD, SD, LW, LWU, SW, LB, LH, LBU, LHU, SB, SH.

  Each proof uses an opaque hypothesis (h_exec) asserting that the SAIL
  execute_LOAD/execute_STORE computation succeeds at the EStateM level
  and produces a state satisfying StateRel. This defers the deep vmem_read/
  vmem_write bare-mode reduction (6+ layers) to a separate verification effort.

  The h_exec hypothesis is dischargeable when:
  - The SAIL state is in bare mode (Machine privilege, satp=0)
  - The memory access is aligned
  - The relevant privilege/status registers are readable
  - The byte-level SAIL memory agrees with Rv64's doubleword memory (StateRel.mem_agree)
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Doubleword loads/stores (LD/SD)
-- ============================================================================

theorem ld_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 8 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.LD rd rs1 offset)) sSail') :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 8) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LD rd rs1 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

theorem sd_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 8 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SD rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 8) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SD rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

-- ============================================================================
-- Word loads/stores (LW/LWU/SW)
-- ============================================================================

theorem lw_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 4 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.LW rd rs1 offset)) sSail') :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LW rd rs1 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

theorem lwu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 4 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.LWU rd rs1 offset)) sSail') :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LWU rd rs1 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

theorem sw_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 4 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SW rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SW rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

-- ============================================================================
-- Byte loads/stores (LB/LBU/SB)
-- ============================================================================

theorem lb_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 1 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.LB rd rs1 offset)) sSail') :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LB rd rs1 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

theorem lbu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 1 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.LBU rd rs1 offset)) sSail') :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LBU rd rs1 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

theorem sb_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 1 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SB rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SB rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

-- ============================================================================
-- Halfword loads/stores (LH/LHU/SH)
-- ============================================================================

theorem lh_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 2 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.LH rd rs1 offset)) sSail') :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LH rd rs1 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

theorem lhu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 2 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.LHU rd rs1 offset)) sSail') :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LHU rd rs1 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

theorem sh_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 2 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SH rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SH rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

end EvmAsm.Rv64.SailEquiv
